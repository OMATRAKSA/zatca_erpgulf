"""
Advance payment invoices from Payment Entry.

A customer advance received through a normal ERPNext Payment Entry is sent to
ZATCA as a prepayment invoice (type 386). It can be standard-rated (VAT in its
taxes table), zero-rated, exempt or out of scope (ZATCA Tax Category and
exemption reason on the Payment Entry), or split over several categories (the
"ZATCA Advance Line" table). A refund of that advance is sent as a credit note
(type 381) against it, in the same categories. On the final Sales Invoice,
advances allocated from such Payment Entries are reported as prepayment lines
(one per advance and VAT category/rate) with PrepaidAmount, and the VAT already
declared on the advance can be reversed automatically so it is not counted twice.

Everything here is switched on per company (Company > ZATCA >
"Send customer advance Payment Entries to ZATCA"). It does not need or touch the
claudion4saudi "Advance Sales Invoice" route, which keeps working as before.

The header, seller, buyer and payment-means builders of the existing advance
route (advance_payment.py) are reused unchanged through AdvancePaymentEntryView;
the tax totals and lines are built here so several categories can be reported.
"""

import base64
import contextlib
import uuid
import xml.etree.ElementTree as ET
from decimal import Decimal, ROUND_HALF_UP

import frappe
import requests
from frappe import _
from frappe.utils import cint, flt, get_time

from zatca_erpgulf.zatca_erpgulf.createxml import xml_tags, get_icv_code
from zatca_erpgulf.zatca_erpgulf.createxml_advance import (
    removetags,
    canonicalize_xml,
    getinvoicehash,
    digital_signature,
    extract_certificate_details,
    certificate_hash,
    signxml_modify,
    generate_signed_properties_hash,
    populate_the_ubl_extensions_output,
    generate_tlv_xml,
    structuring_signedxml,
    get_tlv_for_value,
    update_qr_toxml,
)
from zatca_erpgulf.zatca_erpgulf.advance_payment import (
    additional_reference_advanve,
    company_data_advance,
    customer_data_advance,
    delivery_and_payment_means_adavance,
    xml_structuring_advance,
    xml_base64_decode,
    attach_qr_image_advance,
)
from zatca_erpgulf.zatca_erpgulf.sign_invoice import get_api_url
from zatca_erpgulf.zatca_erpgulf.xml_tax_data import get_exemption_reason_map

try:  # frappe >= v15
    from frappe.utils.synchronization import filelock
except ImportError:  # pragma: no cover
    filelock = None

PAYMENT_ENTRY = "Payment Entry"
DONE_STATUSES = ("CLEARED", "REPORTED")
ADVANCE_ITEM_CODE = "ADVANCE"
PREPAYMENT_TYPE = "386"
CREDIT_NOTE_TYPE = "381"
STANDARD_SUBTYPE = "0100000"
SIMPLIFIED_SUBTYPE = "0200000"
REFUND_REASON = "Refund of advance payment"


# --------------------------------------------------------------------------
# Settings and classification
# --------------------------------------------------------------------------


def is_enabled(company):
    """True when the company sends advance Payment Entries to ZATCA."""
    if not company:
        return False
    values = frappe.db.get_value(
        "Company",
        company,
        ["custom_zatca_invoice_enabled", "custom_zatca_advance_payment_entry"],
        as_dict=True,
    )
    return bool(
        values
        and cint(values.custom_zatca_invoice_enabled)
        and cint(values.custom_zatca_advance_payment_entry)
    )


def is_vat_reversal_enabled(company):
    """True when the final invoice should reverse the VAT declared on its advances."""
    return is_enabled(company) and cint(
        frappe.db.get_value("Company", company, "custom_reverse_advance_vat")
    )


STANDARD = "Standard"
ZERO_RATED = "Zero Rated"
EXEMPTED = "Exempted"
OUT_OF_SCOPE = "Services outside scope of tax / Not subject to VAT"
CATEGORY_CODES = {STANDARD: "S", ZERO_RATED: "Z", EXEMPTED: "E", OUT_OF_SCOPE: "O"}
# Exemption reason codes allowed per category (ZATCA code list, BR-KSA-69/BR-KSA-CL-04)
REASON_CODES = {
    "Z": (
        "VATEX-SA-32", "VATEX-SA-33", "VATEX-SA-34-1", "VATEX-SA-34-2", "VATEX-SA-34-3",
        "VATEX-SA-34-4", "VATEX-SA-34-5", "VATEX-SA-35", "VATEX-SA-36", "VATEX-SA-EDU",
        "VATEX-SA-HEA", "VATEX-SA-MLTRY",
    ),
    "E": ("VATEX-SA-29", "VATEX-SA-29-7", "VATEX-SA-30"),
    "O": ("VATEX-SA-OOS",),
}
STANDARD_RATES = (5.0, 15.0)
CENT = Decimal("0.01")


def _money(value):
    return Decimal(str(flt(value))).quantize(CENT, rounding=ROUND_HALF_UP)


def get_category(pe):
    """ZATCA tax category of a single-category advance (empty = Standard)."""
    return pe.get("custom_zatca_tax_category") or STANDARD


def has_category_lines(pe):
    """Advance split over several categories (e.g. part standard, part zero-rated)."""
    return bool(pe.get("custom_zatca_advance_lines"))


def is_advance(pe):
    """A customer receipt sent to ZATCA as an advance tax invoice: it carries VAT,
    or it is marked zero-rated / exempt / out of scope, or it is split by category."""
    return (
        pe.payment_type == "Receive"
        and pe.party_type == "Customer"
        and (
            bool(pe.get("taxes"))
            or has_category_lines(pe)
            or get_category(pe) != STANDARD
        )
    )


def is_advance_refund(pe):
    """A payment back to the customer against an advance = a credit note."""
    return (
        pe.payment_type == "Pay"
        and pe.party_type == "Customer"
        and bool(pe.get("custom_advance_refund_against"))
    )


def get_vat_row(pe):
    """The single VAT row of a standard-rated, single-category advance."""
    taxes = pe.get("taxes") or []
    if len(taxes) != 1:
        frappe.throw(
            _(
                "{0}: a standard-rated advance sent to ZATCA must have exactly one VAT row in Taxes and Charges."
            ).format(pe.name)
        )
    row = taxes[0]
    if row.charge_type != "On Paid Amount":
        frappe.throw(_("{0}: the VAT row must be 'On Paid Amount'.").format(pe.name))
    if flt(row.rate) not in STANDARD_RATES:
        frappe.throw(_("{0}: the VAT rate must be 15% or 5%.").format(pe.name))
    if row.add_deduct_tax and row.add_deduct_tax != "Add":
        frappe.throw(_("{0}: the VAT row must be 'Add'.").format(pe.name))
    return row


def get_included_tax(pe, base=False):
    """VAT included in the paid amount (0 for zero-rated / exempt / out-of-scope)."""
    total = 0
    for row in pe.get("taxes") or []:
        if cint(row.included_in_paid_amount):
            total += flt(row.base_tax_amount if base else row.tax_amount)
    return flt(total, 2)


def get_net_amount(pe, base=False):
    """Amount excluding VAT, i.e. what the party account is credited (or debited)."""
    paid = flt(pe.base_paid_amount if base else pe.paid_amount)
    return flt(paid - get_included_tax(pe, base), 2)


def get_gross_factor(pe):
    """Gross / net of an advance: what 1.00 of it is worth with its VAT."""
    net = get_net_amount(pe)
    if net <= 0:
        return 1
    return flt(pe.paid_amount) / net


def _reason_text(code, free_text=None):
    if code == "VATEX-SA-OOS":
        return free_text or "Not subject to VAT"
    return get_exemption_reason_map().get(code) or code


def _line(category, rate, reason_code, reason, taxable, tax):
    code = CATEGORY_CODES.get(category or STANDARD)
    return frappe._dict(
        category=category or STANDARD,
        code=code,
        rate=flt(rate) if code == "S" else 0.0,
        reason_code=None if code == "S" else reason_code,
        reason=None if code == "S" else _reason_text(reason_code, reason),
        taxable=_money(taxable),
        tax=_money(tax) if code == "S" else Decimal("0.00"),
    )


def line_tax(category, rate, amount):
    """VAT of one category line: taxable x rate / 100 (BR-KSA-79), 0 if not standard."""
    if CATEGORY_CODES.get(category or STANDARD) != "S":
        return Decimal("0.00")
    return (_money(amount) * Decimal(str(flt(rate))) / Decimal("100")).quantize(
        CENT, rounding=ROUND_HALF_UP
    )


def get_breakdown(pe):
    """The advance (or refund) by VAT category and rate, in its own currency:
    one line per category, each with taxable amount, VAT, rate and exemption reason."""
    if has_category_lines(pe):
        merged = {}
        for row in pe.get("custom_zatca_advance_lines"):
            line = _line(
                row.tax_category,
                row.rate,
                row.exemption_reason_code,
                row.tax_exemption_reason,
                row.amount,
                line_tax(row.tax_category, row.rate, row.amount),
            )
            key = (line.code, line.rate, line.reason_code, line.reason)
            if key in merged:
                merged[key].taxable += line.taxable
                merged[key].tax = line_tax(line.category, line.rate, merged[key].taxable)
            else:
                merged[key] = line
        return list(merged.values())
    category = get_category(pe)
    if CATEGORY_CODES.get(category) == "S":
        row = get_vat_row(pe)
        tax = _money(row.tax_amount)
        paid = _money(pe.paid_amount)
        taxable = paid - tax if cint(row.included_in_paid_amount) else paid
        return [_line(STANDARD, row.rate, None, None, taxable, tax)]
    return [
        _line(
            category,
            0,
            pe.get("custom_exemption_reason_code"),
            pe.get("custom_tax_exemption_reason"),
            pe.paid_amount,
            0,
        )
    ]


def scale_breakdown(lines, net):
    """The part of an advance worth `net` (excluding VAT), split over its category
    lines in proportion; VAT recomputed per line so tax = taxable x rate (BR-KSA-79)."""
    net = _money(net)
    total = sum((l.taxable for l in lines), Decimal("0"))
    if total <= 0 or net <= 0:
        return []
    if net >= total:
        return [frappe._dict(l) for l in lines]
    result = []
    left = net
    for i, l in enumerate(lines):
        if i == len(lines) - 1:
            taxable = left
        else:
            taxable = (l.taxable * net / total).quantize(CENT, rounding=ROUND_HALF_UP)
            left -= taxable
        scaled = frappe._dict(l)
        scaled.taxable = taxable
        scaled.tax = line_tax(l.category, l.rate, taxable)
        if taxable > 0:
            result.append(scaled)
    return result


def get_refunded_net(advance_name, exclude=None):
    """Net amount already refunded (submitted refund Payment Entries) against an advance."""
    filters = {
        "docstatus": 1,
        "payment_type": "Pay",
        "custom_advance_refund_against": advance_name,
    }
    if exclude:
        filters["name"] = ["!=", exclude]
    total = 0
    for name in frappe.get_all(PAYMENT_ENTRY, filters=filters, pluck="name"):
        total += get_net_amount(frappe.get_doc(PAYMENT_ENTRY, name))
    return flt(total, 2)


def is_simplified(pe):
    return cint(frappe.db.get_value("Customer", pe.party, "custom_b2c")) == 1


# --------------------------------------------------------------------------
# View: a Payment Entry shaped like an Advance Sales Invoice
# --------------------------------------------------------------------------


class AdvancePaymentEntryView:
    """Read-only view over a Payment Entry exposing the fields that the
    advance_payment.py XML builders read (company, customer, totals, tax
    category). Everything else, db_set included, goes to the Payment Entry."""

    def __init__(self, pe):
        self.__dict__["_pe"] = pe
        lines = get_breakdown(pe)
        net = flt(sum((l.taxable for l in lines), Decimal("0")))
        rate = flt(pe.get("source_exchange_rate") or 1)
        so = next(
            (
                r.reference_name
                for r in pe.get("references") or []
                if r.reference_doctype == "Sales Order"
            ),
            None,
        )
        if is_advance_refund(pe):
            label = _("Refund of advance {0}").format(pe.custom_advance_refund_against)
        elif so:
            label = _("Advance payment for {0}").format(so)
        else:
            label = _("Advance payment")
        self.__dict__.update(
            zatca_lines=lines,
            zatca_label=label,
            total=net,
            base_total=flt(net * rate, 2),
            net_total=net,
            base_net_total=flt(net * rate, 2),
            custom_zatca_tax_category=lines[0].category if len(lines) == 1 else STANDARD,
            custom_exemption_reason_code=lines[0].reason_code if len(lines) == 1 else None,
            custom_tax_exemption_reason=lines[0].reason if len(lines) == 1 else None,
            doctype=PAYMENT_ENTRY,
        )

    def __getattr__(self, name):
        return getattr(self.__dict__["_pe"], name)

    def get(self, key, default=None):
        if key in self.__dict__:
            return self.__dict__[key]
        return self.__dict__["_pe"].get(key, default)

    def db_set(self, *args, **kwargs):
        return self.__dict__["_pe"].db_set(*args, **kwargs)

    def notify_update(self):
        return self.__dict__["_pe"].notify_update()


# --------------------------------------------------------------------------
# XML
# --------------------------------------------------------------------------


def _header(invoice, view):
    ET.SubElement(invoice, "cbc:ProfileID").text = "reporting:1.0"
    ET.SubElement(invoice, "cbc:ID").text = str(view.name)
    uuid1 = str(uuid.uuid1())
    ET.SubElement(invoice, "cbc:UUID").text = uuid1
    ET.SubElement(invoice, "cbc:IssueDate").text = str(view.posting_date)
    ET.SubElement(invoice, "cbc:IssueTime").text = issue_time(view)
    return uuid1


def issue_time(pe):
    """Payment Entry has no posting time: its creation time is used, the same in
    the advance's own XML and in every final invoice that refers to it."""
    return get_time(pe.creation).strftime("%H:%M:%S")


def _type_code(invoice, simplified, refund):
    code = ET.SubElement(invoice, "cbc:InvoiceTypeCode")
    code.set("name", SIMPLIFIED_SUBTYPE if simplified else STANDARD_SUBTYPE)
    code.text = CREDIT_NOTE_TYPE if refund else PREPAYMENT_TYPE


def _currency_and_icv(invoice, view, refund):
    ET.SubElement(invoice, "cbc:DocumentCurrencyCode").text = view.paid_from_account_currency
    ET.SubElement(invoice, "cbc:TaxCurrencyCode").text = "SAR"
    if refund:
        billing = ET.SubElement(invoice, "cac:BillingReference")
        ref = ET.SubElement(billing, "cac:InvoiceDocumentReference")
        ET.SubElement(ref, "cbc:ID").text = str(view.custom_advance_refund_against)
    icv = ET.SubElement(invoice, "cac:AdditionalDocumentReference")
    ET.SubElement(icv, "cbc:ID").text = "ICV"
    ET.SubElement(icv, "cbc:UUID").text = str(get_icv_code(view.name))


def _child(element, tag):
    """First direct child with this literal tag. The builders write prefixed tag
    names ("cac:Party") without namespaces, so ElementTree's find() can't be used."""
    if element is None:
        return None
    return next((c for c in element if c.tag == tag), None)


def _add_buyer_vat(invoice, pe):
    """Buyer VAT number (BT-48), as the normal Sales Invoice XML does: Saudi
    customers with a VAT number only (BR-KSA-44)."""
    tax_id, address_name = frappe.db.get_value(
        "Customer", pe.party, ["tax_id", "customer_primary_address"]
    )
    if not tax_id or not address_name:
        return
    if frappe.db.get_value("Address", address_name, "country") != "Saudi Arabia":
        return
    scheme = _child(_child(_child(invoice, "cac:AccountingCustomerParty"), "cac:Party"), "cac:PartyTaxScheme")
    if scheme is None or _child(scheme, "cbc:CompanyID") is not None:
        return
    company_id = ET.Element("cbc:CompanyID")
    company_id.text = tax_id
    scheme.insert(0, company_id)


def _add_instruction_note(invoice):
    """Credit notes need the reason (KSA-10) in PaymentMeans."""
    means = _child(invoice, "cac:PaymentMeans")
    if means is not None:
        ET.SubElement(means, "cbc:InstructionNote").text = REFUND_REASON


def _amount(parent, tag, value, currency):
    element = ET.SubElement(parent, tag, currencyID=currency)
    element.text = f"{Decimal(str(value)).quantize(CENT, rounding=ROUND_HALF_UP):.2f}"
    return element


def _tax_category(parent, tag, line, with_reason):
    category = ET.SubElement(parent, tag)
    ET.SubElement(category, "cbc:ID").text = line.code
    ET.SubElement(category, "cbc:Percent").text = f"{flt(line.rate):.2f}"
    if with_reason and line.code != "S":
        ET.SubElement(category, "cbc:TaxExemptionReasonCode").text = line.reason_code
        ET.SubElement(category, "cbc:TaxExemptionReason").text = line.reason
    ET.SubElement(ET.SubElement(category, "cac:TaxScheme"), "cbc:ID").text = "VAT"
    return category


def _add_tax_totals_and_lines(invoice, view):
    """TaxTotal (in SAR, then in the document currency with one TaxSubtotal per
    category and rate), LegalMonetaryTotal and one InvoiceLine per category."""
    currency = view.paid_from_account_currency
    lines = view.zatca_lines
    exchange = Decimal(str(flt(view.get("source_exchange_rate") or 1)))
    taxable = sum((l.taxable for l in lines), Decimal("0"))
    tax = sum((l.tax for l in lines), Decimal("0"))

    sar_total = ET.SubElement(invoice, "cac:TaxTotal")
    _amount(sar_total, "cbc:TaxAmount", tax if currency == "SAR" else tax * exchange, "SAR")
    doc_total = ET.SubElement(invoice, "cac:TaxTotal")
    _amount(doc_total, "cbc:TaxAmount", tax, currency)
    for line in lines:
        subtotal = ET.SubElement(doc_total, "cac:TaxSubtotal")
        _amount(subtotal, "cbc:TaxableAmount", line.taxable, currency)
        _amount(subtotal, "cbc:TaxAmount", line.tax, currency)
        _tax_category(subtotal, "cac:TaxCategory", line, with_reason=True)

    monetary = ET.SubElement(invoice, "cac:LegalMonetaryTotal")
    _amount(monetary, "cbc:LineExtensionAmount", taxable, currency)
    _amount(monetary, "cbc:TaxExclusiveAmount", taxable, currency)
    _amount(monetary, "cbc:TaxInclusiveAmount", taxable + tax, currency)
    _amount(monetary, "cbc:AllowanceTotalAmount", 0, currency)
    _amount(monetary, "cbc:PayableAmount", taxable + tax, currency)

    for idx, line in enumerate(lines, start=1):
        invoice_line = ET.SubElement(invoice, "cac:InvoiceLine")
        ET.SubElement(invoice_line, "cbc:ID").text = str(idx)
        ET.SubElement(invoice_line, "cbc:InvoicedQuantity", unitCode="EA").text = "1"
        _amount(invoice_line, "cbc:LineExtensionAmount", line.taxable, currency)
        line_tax_total = ET.SubElement(invoice_line, "cac:TaxTotal")
        _amount(line_tax_total, "cbc:TaxAmount", line.tax, currency)
        _amount(line_tax_total, "cbc:RoundingAmount", line.taxable + line.tax, currency)
        item = ET.SubElement(invoice_line, "cac:Item")
        name = f"{ADVANCE_ITEM_CODE}:{view.zatca_label}"
        if len(lines) > 1:
            name += f" ({line.category}{' ' + format(line.rate, 'g') + '%' if line.code == 'S' else ''})"
        ET.SubElement(item, "cbc:Name").text = name
        _tax_category(item, "cac:ClassifiedTaxCategory", line, with_reason=False)
        price = ET.SubElement(invoice_line, "cac:Price")
        _amount(price, "cbc:PriceAmount", line.taxable, currency)
    return invoice


def build_signed_xml(pe):
    """Build and sign the XML; returns (uuid, hash, signed file path, qr b64)."""
    view = AdvancePaymentEntryView(pe)
    refund = is_advance_refund(pe)
    simplified = is_simplified(pe)
    company_abbr = frappe.db.get_value("Company", pe.company, "abbr")

    invoice = xml_tags()
    uuid1 = _header(invoice, view)
    _type_code(invoice, simplified, refund)
    _currency_and_icv(invoice, view, refund)
    invoice = additional_reference_advanve(invoice, company_abbr, view)
    invoice = company_data_advance(invoice, view)
    invoice = customer_data_advance(invoice, view)
    _add_buyer_vat(invoice, pe)
    invoice = delivery_and_payment_means_adavance(invoice, view)
    if refund:
        _add_instruction_note(invoice)
    invoice = _add_tax_totals_and_lines(invoice, view)
    file_content = xml_structuring_advance(invoice, view)

    canonicalized_xml = canonicalize_xml(removetags(file_content))
    hash1, encoded_hash = getinvoicehash(canonicalized_xml)
    encoded_signature = digital_signature(hash1, company_abbr, pe)
    issuer_name, serial_number = extract_certificate_details(company_abbr, pe)
    encoded_certificate_hash = certificate_hash(company_abbr, pe)
    modified_xml_string, namespaces, signing_time = signxml_modify(
        company_abbr, file_content, pe
    )
    signed_properties_base64 = generate_signed_properties_hash(
        signing_time, issuer_name, serial_number, encoded_certificate_hash
    )
    final_xml_string = populate_the_ubl_extensions_output(
        modified_xml_string,
        encoded_signature,
        namespaces,
        signed_properties_base64,
        encoded_hash,
        company_abbr,
        pe,
    )
    tlv_data = generate_tlv_xml(final_xml_string, company_abbr, pe)
    qrcodeb64 = base64.b64encode(
        b"".join(get_tlv_for_value(num, value) for num, value in tlv_data.items())
    ).decode("utf-8")
    updated_xml_string = update_qr_toxml(final_xml_string, qrcodeb64, company_abbr)
    signed_xmlfile_name = structuring_signedxml(pe.name, updated_xml_string)
    return view, uuid1, encoded_hash, signed_xmlfile_name, qrcodeb64, simplified


# --------------------------------------------------------------------------
# Sending
# --------------------------------------------------------------------------


@contextlib.contextmanager
def _company_chain_lock(company):
    """Send one document at a time per company so the PIH chain stays in order."""
    if filelock is None:
        yield
        return
    with filelock(f"zatca_pih_{frappe.scrub(company)}", timeout=120):
        yield


def _set_not_submitted(pe, message):
    pe.db_set("custom_zatca_status", "Not Submitted", update_modified=False)
    pe.db_set("custom_zatca_full_response", message, update_modified=False)


def _attach_xml(pe, xml_text, label):
    file = frappe.get_doc(
        {
            "doctype": "File",
            "file_name": f"{label} xml file {pe.name}.xml",
            "attached_to_doctype": pe.doctype,
            "attached_to_name": pe.name,
            "is_private": 1,
            "content": xml_text,
        }
    )
    file.save(ignore_permissions=True)
    pe.db_set("custom_ksa_einvoicing_xml", file.file_url, update_modified=False)


def send_to_zatca(pe):
    """Sign and send one advance (or advance refund) Payment Entry to ZATCA."""
    if pe.get("custom_zatca_status") in DONE_STATUSES:
        frappe.throw(_("{0} has already been sent to ZATCA.").format(pe.name))

    with _company_chain_lock(pe.company):
        company_abbr, csid = frappe.db.get_value(
            "Company", pe.company, ["abbr", "custom_basic_auth_from_production"]
        )
        if not csid:
            frappe.throw(_("Production CSID for company {0} not found.").format(pe.company))

        view, uuid1, encoded_hash, signed_file, qrcodeb64, simplified = build_signed_xml(pe)
        payload = {
            "invoiceHash": encoded_hash,
            "uuid": uuid1,
            "invoice": xml_base64_decode(signed_file),
        }
        headers = {
            "accept": "application/json",
            "accept-language": "en",
            "Clearance-Status": "0" if simplified else "1",
            "Accept-Version": "V2",
            "Authorization": "Basic " + csid,
            "Content-Type": "application/json",
        }
        endpoint = "invoices/reporting/single" if simplified else "invoices/clearance/single"
        try:
            response = requests.post(
                url=get_api_url(company_abbr, base_url=endpoint),
                headers=headers,
                json=payload,
                timeout=300,
            )
        except requests.RequestException as e:
            _set_not_submitted(pe, str(e))
            frappe.throw(_("ZATCA could not be reached: {0}").format(e))

        if response.status_code not in (200, 202):
            _set_not_submitted(pe, response.text)
            frappe.throw(
                _("ZATCA rejected {0}. Status code: {1}<br><br>{2}").format(
                    pe.name, response.status_code, response.text
                )
            )

        status = "REPORTED" if simplified else "CLEARED"
        prefix = "WITH WARNINGS: " if response.status_code == 202 else "SUCCESS: "
        # ERPGulf's QR step (tag8_publickey -> create_public_key) saves and commits
        # the Company while the XML is built, so a Company doc loaded before it is
        # stale ("Document has been modified"). Write the PIH directly instead.
        frappe.db.set_value("Company", pe.company, "custom_pih", encoded_hash)

        pe.db_set("custom_uuid", uuid1, update_modified=False)
        pe.db_set("custom_zatca_status", status, update_modified=False)
        pe.db_set(
            "custom_zatca_full_response",
            f"{prefix}Status Code: {response.status_code}<br><br>{response.text}",
            update_modified=False,
        )

        if simplified:
            with open(signed_file, encoding="utf-8") as f:
                xml_text = f.read()
            _attach_xml(pe, xml_text, "Reported")
        else:
            cleared = (response.json() or {}).get("clearedInvoice")
            xml_text = base64.b64decode(cleared).decode("utf-8") if cleared else ""
            if xml_text:
                _attach_xml(pe, xml_text, "Cleared")
        attach_qr_image_advance(qrcodeb64, view)
        return status


# --------------------------------------------------------------------------
# Payment Entry hooks
# --------------------------------------------------------------------------


def before_validate_payment_entry(doc, method=None):
    """Fill the category lines' VAT and the VAT row of a split advance, then cap the
    Sales Order allocation at the amount excluding VAT (the party is credited only
    that much when VAT is included in the amount received)."""
    if not (is_enabled(doc.company) and (is_advance(doc) or is_advance_refund(doc))):
        return
    if has_category_lines(doc):
        for row in doc.get("custom_zatca_advance_lines"):
            code = CATEGORY_CODES.get(row.tax_category or STANDARD)
            if code == "S":
                if not flt(row.rate):
                    row.rate = 15
            else:
                row.rate = 0
            row.tax_amount = flt(line_tax(row.tax_category, row.rate, row.amount))
        vat = sum(flt(r.tax_amount) for r in doc.get("custom_zatca_advance_lines"))
        taxes = doc.get("taxes") or []
        if len(taxes) == 1:
            taxes[0].charge_type = "Actual"
            taxes[0].tax_amount = vat
            taxes[0].included_in_paid_amount = 1
            taxes[0].add_deduct_tax = "Add"
        net = flt(flt(doc.paid_amount) - vat, 2)
    else:
        row = (doc.get("taxes") or [None])[0]
        if row and cint(row.included_in_paid_amount) and flt(row.rate):
            net = flt(flt(doc.paid_amount) / (1 + flt(row.rate) / 100), 2)
        else:
            net = flt(doc.paid_amount, 2)
    allocated = 0
    for ref in doc.get("references") or []:
        if ref.reference_doctype != "Sales Order":
            continue
        room = max(0, flt(net - allocated, 2))
        if flt(ref.allocated_amount) > room:
            ref.allocated_amount = room
        allocated += flt(ref.allocated_amount)


def _can_bypass():
    """Only a System Manager may record a customer receipt that breaks the advance rules
    (e.g. finance recording old payments)."""
    return "System Manager" in frappe.get_roles()


def _guard_customer_receipt(doc):
    """Money received from a customer before an invoice is an advance and must carry VAT."""
    if doc.payment_type != "Receive" or doc.party_type != "Customer" or is_advance(doc):
        return
    refs = doc.get("references") or []
    against_order = [r.reference_name for r in refs if r.reference_doctype == "Sales Order" and flt(r.allocated_amount)]
    unallocated = flt(doc.unallocated_amount) > 0.01
    if (against_order or unallocated) and not _can_bypass():
        frappe.throw(
            _(
                "This payment is an advance ({0}). In Taxes and Charges, pick the template "
                "<b>Advance VAT (15%)</b> so the customer gets an advance tax invoice. "
                "For a zero-rated, exempt or out-of-scope advance, set the ZATCA Tax Category instead."
            ).format(", ".join(against_order) if against_order else _("not linked to an invoice")),
            title=_("VAT template missing"),
        )


def _check_reason(category, code, free_text, where):
    letter = CATEGORY_CODES.get(category or STANDARD)
    if letter == "S":
        return
    if not code:
        frappe.throw(
            _("{0}: pick the exemption reason code for a {1} advance.").format(where, _(category)),
            title=_("Exemption reason missing"),
        )
    if code not in REASON_CODES[letter]:
        frappe.throw(
            _("{0}: reason code {1} does not belong to {2}. Use one of: {3}.").format(
                where, code, _(category), ", ".join(REASON_CODES[letter])
            ),
            title=_("Wrong exemption reason"),
        )
    if letter == "O" and not (free_text or "").strip():
        frappe.throw(
            _("{0}: write why the advance is out of scope of VAT (Tax Exemption Reason).").format(where),
            title=_("Exemption reason missing"),
        )


def _check_vat_account(row):
    account = frappe.db.get_value("Account", row.account_head, ["account_type", "root_type"], as_dict=True)
    if not account or account.root_type != "Liability" or account.account_type != "Tax":
        frappe.throw(_("The VAT row must post to an Output VAT account, not {0}.").format(row.account_head))


def _warn_reduced_rate(rate):
    if flt(rate) == 5:
        frappe.msgprint(
            _(
                "5% VAT applies only to advances for supplies agreed before the rate rose to 15% "
                "(1 July 2020). Check the rate before submitting."
            ),
            title=_("5% VAT"),
            indicator="orange",
        )


def _guard_categories(doc, warn=True):
    """VAT category rules for an advance or a refund, single or split."""
    taxes = doc.get("taxes") or []
    if has_category_lines(doc):
        standard_vat = 0
        for row in doc.get("custom_zatca_advance_lines"):
            where = _("Category row {0}").format(row.idx)
            if not row.tax_category:
                frappe.throw(_("{0}: pick the ZATCA tax category.").format(where))
            if flt(row.amount) <= 0:
                frappe.throw(_("{0}: the amount (excluding VAT) must be more than zero.").format(where))
            if CATEGORY_CODES[row.tax_category] == "S":
                if flt(row.rate) not in STANDARD_RATES:
                    frappe.throw(_("{0}: the VAT rate must be 15% or 5%.").format(where))
                if warn:
                    _warn_reduced_rate(row.rate)
                standard_vat += flt(row.tax_amount)
            else:
                _check_reason(row.tax_category, row.exemption_reason_code, row.tax_exemption_reason, where)
        if standard_vat:
            if len(taxes) != 1:
                frappe.throw(
                    _("Add one VAT row in Taxes and Charges (Output VAT account) for the standard-rated part."),
                    title=_("VAT row missing"),
                )
            _check_vat_account(taxes[0])
        elif taxes:
            frappe.throw(_("No row is standard-rated, so remove the VAT row from Taxes and Charges."))
        gross = sum(flt(r.amount) + flt(r.tax_amount) for r in doc.get("custom_zatca_advance_lines"))
        if abs(flt(gross, 2) - flt(doc.paid_amount, 2)) > 0.01:
            frappe.throw(
                _(
                    "The category rows add up to {0} with VAT, but the amount paid is {1}. "
                    "Make them equal."
                ).format(flt(gross, 2), flt(doc.paid_amount, 2)),
                title=_("Category rows don't add up"),
            )
        return
    category = get_category(doc)
    if CATEGORY_CODES.get(category) == "S":
        row = get_vat_row(doc)
        if not cint(row.included_in_paid_amount):
            frappe.throw(
                _("Tick 'Considered in Paid Amount' on the VAT row: the amount includes VAT."),
                title=_("Wrong VAT setting"),
            )
        _check_vat_account(row)
        if warn:
            _warn_reduced_rate(row.rate)
        return
    if taxes:
        frappe.throw(
            _("A {0} advance has no VAT: remove the VAT row from Taxes and Charges.").format(_(category)),
            title=_("Remove the VAT row"),
        )
    _check_reason(
        category,
        doc.get("custom_exemption_reason_code"),
        doc.get("custom_tax_exemption_reason"),
        doc.name or _("This advance"),
    )


def _guard_advance(doc):
    """An advance must be clean before it reaches ZATCA."""
    _guard_categories(doc)
    others = sorted(
        {r.reference_doctype for r in doc.get("references") or [] if r.reference_doctype != "Sales Order"}
    )
    if others:
        frappe.throw(
            _(
                "An advance can only be linked to a Sales Order. Remove the {0} rows under References, "
                "or remove the VAT template if this payment settles an existing invoice."
            ).format(", ".join(others)),
            title=_("Wrong references"),
        )
    if flt(doc.paid_amount) <= 0:
        frappe.throw(_("Paid Amount must be more than zero."))


def _category_keys(pe):
    return {(l.code, l.rate, l.reason_code) for l in get_breakdown(pe)}


def validate_payment_entry(doc, method=None):
    if not is_enabled(doc.company):
        return
    _guard_customer_receipt(doc)
    if (
        doc.payment_type == "Pay"
        and doc.party_type == "Customer"
        and doc.get("taxes")
        and not doc.get("custom_advance_refund_against")
    ):
        frappe.throw(
            _("To pay back an advance, open the advance Payment Entry and use <b>Create → Refund Advance</b>."),
            title=_("Use Refund Advance"),
        )
    if is_advance(doc):
        _guard_advance(doc)
    elif is_advance_refund(doc):
        _guard_categories(doc, warn=False)
        original = frappe.get_doc(PAYMENT_ENTRY, doc.custom_advance_refund_against)
        if original.docstatus != 1 or original.party != doc.party:
            frappe.throw(_("The advance being refunded must be a submitted Payment Entry for the same customer."))
        if original.get("custom_zatca_status") not in DONE_STATUSES:
            frappe.throw(_("The advance {0} has not been sent to ZATCA.").format(original.name))
        if not _category_keys(doc) <= _category_keys(original):
            frappe.throw(
                _(
                    "A refund must use the same VAT categories and rates as advance {0}. "
                    "Use Create → Refund Advance on the advance."
                ).format(original.name),
                title=_("Wrong VAT category"),
            )
        available = flt(
            get_net_amount(original)
            - get_refunded_net(original.name, exclude=doc.name)
            - get_allocated_to_invoices(original.name),
            2,
        )
        if get_net_amount(doc) - available > 0.01:
            frappe.throw(
                _("Refund (excluding VAT) {0} is more than what is left on advance {1}: {2}.").format(
                    get_net_amount(doc), original.name, available
                )
            )


def _guard_customer_data(doc):
    """What ZATCA needs from the customer, checked before submit so it isn't rejected."""
    customer = frappe.db.get_value(
        "Customer", doc.party, ["tax_id", "custom_b2c", "customer_primary_address"], as_dict=True
    ) or frappe._dict()
    link = frappe.utils.get_link_to_form("Customer", doc.party)
    tax_id = (customer.tax_id or "").strip()
    if cint(customer.custom_b2c):
        if tax_id:
            frappe.throw(
                _(
                    "Customer {0} has a VAT number but is marked as B2C. Untick B2C on the customer "
                    "so they get a standard tax invoice they can claim VAT on."
                ).format(link),
                title=_("Check the customer"),
            )
        return
    missing = []
    if not (len(tax_id) == 15 and tax_id.isdigit() and tax_id[0] == "3" and tax_id[-1] == "3"):
        missing.append(_("a valid VAT number (15 digits, starts and ends with 3)"))
    address = (
        frappe.db.get_value(
            "Address",
            customer.customer_primary_address,
            ["address_line1", "address_line2", "city", "pincode", "custom_building_number", "country"],
            as_dict=True,
        )
        if customer.customer_primary_address
        else None
    )
    if not address:
        missing.append(_("a primary address"))
    else:
        if not address.address_line1:
            missing.append(_("street"))
        if not address.address_line2:
            missing.append(_("district (Address Line 2)"))
        if not address.city:
            missing.append(_("city"))
        if not (address.pincode and len(address.pincode.strip()) == 5 and address.pincode.strip().isdigit()):
            missing.append(_("5-digit postal code"))
        if not (
            address.get("custom_building_number")
            and len(address.custom_building_number.strip()) == 4
            and address.custom_building_number.strip().isdigit()
        ):
            missing.append(_("4-digit building number"))
    if missing:
        frappe.throw(
            _("Customer {0} is a business customer. Before submitting, add: {1}.").format(
                link, ", ".join(missing)
            ),
            title=_("Customer details missing"),
        )


def before_submit_payment_entry(doc, method=None):
    if not is_enabled(doc.company) or not (is_advance(doc) or is_advance_refund(doc)):
        return
    today = frappe.utils.getdate(frappe.utils.nowdate())
    if frappe.utils.getdate(doc.posting_date) != today:
        frappe.throw(
            _("Advance invoices and refunds are dated the day they are issued. Set Posting Date to today ({0}).").format(
                frappe.utils.formatdate(today)
            ),
            title=_("Wrong date"),
        )
    _guard_customer_data(doc)


def before_update_after_submit_payment_entry(doc, method=None):
    """Payment Reconciliation can link a submitted advance to an invoice behind the
    final invoice's back (no prepayment line to ZATCA, VAT counted twice)."""
    if not is_enabled(doc.company) or not is_advance(doc):
        return

    def used_on_invoice(ref):
        # The final invoice's own submit links the advance this way: allowed when the
        # invoice took the advance in through its advances table.
        return ref.reference_doctype == "Sales Invoice" and frappe.db.exists(
            "Sales Invoice Advance",
            {"parent": ref.reference_name, "reference_type": PAYMENT_ENTRY, "reference_name": doc.name},
        )

    if any(
        r.reference_doctype != "Sales Order" and not used_on_invoice(r)
        for r in doc.get("references") or []
    ):
        frappe.throw(
            _(
                "{0} is an advance sent to ZATCA. Use it on the final invoice: "
                "Payments tab → Get Advances Received. Do not reconcile it here."
            ).format(doc.name),
            title=_("Use the final invoice"),
        )


def on_submit_payment_entry(doc, method=None):
    if not is_enabled(doc.company):
        return
    if is_advance(doc) or is_advance_refund(doc):
        send_to_zatca(doc)


def before_cancel_payment_entry(doc, method=None):
    if is_enabled(doc.company) and doc.get("custom_zatca_status") in DONE_STATUSES:
        frappe.throw(
            _(
                "{0} has been sent to ZATCA and cannot be cancelled. Use Refund Advance to refund the customer."
            ).format(doc.name)
        )


@frappe.whitelist()
def resend_payment_entry(name):
    """Retry a submitted advance whose sending failed."""
    pe = frappe.get_doc(PAYMENT_ENTRY, name)
    pe.check_permission("submit")
    if pe.docstatus != 1:
        frappe.throw(_("Submit the Payment Entry first."))
    if not (is_enabled(pe.company) and (is_advance(pe) or is_advance_refund(pe))):
        frappe.throw(_("This Payment Entry is not an advance for ZATCA."))
    return send_to_zatca(pe)


@frappe.whitelist()
def make_advance_refund(source_name):
    """New draft Payment Entry paying back what is left of an advance, VAT included,
    in the same VAT categories and rates as the advance."""
    src = frappe.get_doc(PAYMENT_ENTRY, source_name)
    src.check_permission("read")
    if not is_advance(src) or src.get("custom_zatca_status") not in DONE_STATUSES:
        frappe.throw(_("Only an advance that has been sent to ZATCA can be refunded."))
    left_net = flt(
        get_net_amount(src) - get_refunded_net(src.name) - get_allocated_to_invoices(src.name),
        2,
    )
    if left_net <= 0:
        frappe.throw(_("Nothing is left to refund on {0}.").format(src.name))
    lines = scale_breakdown(get_breakdown(src), left_net)
    vat = sum((l.tax for l in lines), Decimal("0"))
    gross = flt(sum((l.taxable + l.tax for l in lines), Decimal("0")))

    pe = frappe.new_doc(PAYMENT_ENTRY)
    pe.payment_type = "Pay"
    pe.company = src.company
    pe.posting_date = frappe.utils.nowdate()
    pe.mode_of_payment = src.mode_of_payment
    pe.party_type = "Customer"
    pe.party = src.party
    pe.party_name = src.party_name
    pe.paid_from = src.paid_to
    pe.paid_to = src.paid_from
    pe.paid_from_account_currency = src.paid_to_account_currency
    pe.paid_to_account_currency = src.paid_from_account_currency
    pe.cost_center = src.cost_center
    pe.project = src.get("project")
    pe.custom_advance_refund_against = src.name
    pe.custom_zatca_tax_category = src.get("custom_zatca_tax_category")
    pe.custom_exemption_reason_code = src.get("custom_exemption_reason_code")
    pe.custom_tax_exemption_reason = src.get("custom_tax_exemption_reason")
    pe.sales_taxes_and_charges_template = src.get("sales_taxes_and_charges_template")
    pe.paid_amount = gross
    pe.received_amount = gross
    pe.source_exchange_rate = 1
    pe.target_exchange_rate = 1
    vat_row = (src.get("taxes") or [None])[0]
    if has_category_lines(src):
        source_rows = {
            (CATEGORY_CODES[r.tax_category], flt(r.rate) if CATEGORY_CODES[r.tax_category] == "S" else 0.0, r.exemption_reason_code if CATEGORY_CODES[r.tax_category] != "S" else None): r
            for r in src.get("custom_zatca_advance_lines")
        }
        for l in lines:
            r = source_rows.get((l.code, l.rate, l.reason_code))
            pe.append(
                "custom_zatca_advance_lines",
                {
                    "tax_category": l.category,
                    "exemption_reason_code": l.reason_code,
                    "tax_exemption_reason": r.tax_exemption_reason if r else None,
                    "rate": l.rate,
                    "amount": flt(l.taxable),
                    "tax_amount": flt(l.tax),
                },
            )
        if vat and vat_row:
            pe.append(
                "taxes",
                {
                    "charge_type": "Actual",
                    "account_head": vat_row.account_head,
                    "description": vat_row.description,
                    "tax_amount": flt(vat),
                    "add_deduct_tax": "Add",
                    "included_in_paid_amount": 1,
                    "cost_center": vat_row.cost_center,
                },
            )
    elif vat_row:
        pe.append(
            "taxes",
            {
                "charge_type": "On Paid Amount",
                "account_head": vat_row.account_head,
                "description": vat_row.description,
                "rate": vat_row.rate,
                "add_deduct_tax": "Add",
                "included_in_paid_amount": 1,
                "cost_center": vat_row.cost_center,
            },
        )
    pe.remarks = _("Refund of advance {0}").format(src.name)
    pe.setup_party_account_field()
    pe.set_missing_values()
    return pe.as_dict()


# --------------------------------------------------------------------------
# Final Sales Invoice
# --------------------------------------------------------------------------


def get_allocated_to_invoices(advance_name):
    """Net amount of an advance used on submitted Sales Invoices."""
    total = frappe.db.sql(
        """
        select coalesce(sum(adv.allocated_amount), 0)
        from `tabSales Invoice Advance` adv
        join `tabSales Invoice` si on si.name = adv.parent
        where adv.reference_type = 'Payment Entry' and adv.reference_name = %s
          and si.docstatus = 1
        """,
        advance_name,
    )
    return flt(total[0][0] if total else 0, 2)


def get_prepayments(sales_invoice_doc):
    """Advances on this Sales Invoice that were sent to ZATCA as Payment Entries:
    one dict per advance, with the allocated part split by VAT category and rate
    (one prepayment line each, KSA-31 to KSA-34)."""
    if sales_invoice_doc.doctype != "Sales Invoice" or not is_enabled(
        sales_invoice_doc.company
    ):
        return []
    result = []
    for adv in sales_invoice_doc.get("advances") or []:
        if adv.reference_type != PAYMENT_ENTRY or flt(adv.allocated_amount) <= 0:
            continue
        pe = frappe.get_doc(PAYMENT_ENTRY, adv.reference_name)
        if not is_advance(pe) or pe.get("custom_zatca_status") not in DONE_STATUSES:
            continue
        lines = scale_breakdown(get_breakdown(pe), adv.allocated_amount)
        if not lines:
            continue
        taxable = sum((l.taxable for l in lines), Decimal("0"))
        tax = sum((l.tax for l in lines), Decimal("0"))
        vat_row = (pe.get("taxes") or [None])[0]
        result.append(
            frappe._dict(
                name=pe.name,
                uuid=pe.custom_uuid,
                issue_date=str(pe.posting_date),
                issue_time=issue_time(pe),
                lines=lines,
                taxable=taxable,
                tax=tax,
                gross=taxable + tax,
                tax_account=vat_row.account_head if vat_row else None,
            )
        )
    return result


def get_prepaid_amount(sales_invoice_doc):
    """Total prepaid (VAT included) to report as PrepaidAmount, or None."""
    prepayments = get_prepayments(sales_invoice_doc)
    if not prepayments:
        return None
    return sum((p.gross for p in prepayments), Decimal("0"))


def add_prepayment_lines(invoice, sales_invoice_doc):
    """Append the zero-quantity prepayment InvoiceLines after the invoice's own
    item lines: one per advance and VAT category/rate, each referring to the
    advance invoice (KSA-26 to KSA-30) with its taxable amount, VAT, category
    and rate (KSA-31 to KSA-34)."""
    prepayments = get_prepayments(sales_invoice_doc)
    if not prepayments:
        return invoice
    currency = sales_invoice_doc.currency
    next_id = len(sales_invoice_doc.get("items") or []) + 1
    for p in prepayments:
        for l in p.lines:
            line = ET.SubElement(invoice, "cac:InvoiceLine")
            ET.SubElement(line, "cbc:ID").text = str(next_id)
            next_id += 1
            ET.SubElement(line, "cbc:InvoicedQuantity", unitCode="EA").text = "0.000000"
            ET.SubElement(line, "cbc:LineExtensionAmount", currencyID=currency).text = "0.00"

            docref = ET.SubElement(line, "cac:DocumentReference")
            ET.SubElement(docref, "cbc:ID").text = p.name
            ET.SubElement(docref, "cbc:UUID").text = p.uuid
            ET.SubElement(docref, "cbc:IssueDate").text = p.issue_date
            ET.SubElement(docref, "cbc:IssueTime").text = p.issue_time
            ET.SubElement(docref, "cbc:DocumentTypeCode").text = PREPAYMENT_TYPE

            tax_total = ET.SubElement(line, "cac:TaxTotal")
            ET.SubElement(tax_total, "cbc:TaxAmount", currencyID=currency).text = "0.00"
            ET.SubElement(tax_total, "cbc:RoundingAmount", currencyID=currency).text = "0.00"
            subtotal = ET.SubElement(tax_total, "cac:TaxSubtotal")
            _amount(subtotal, "cbc:TaxableAmount", l.taxable, currency)
            _amount(subtotal, "cbc:TaxAmount", l.tax, currency)
            _tax_category(subtotal, "cac:TaxCategory", l, with_reason=False)

            item = ET.SubElement(line, "cac:Item")
            ET.SubElement(item, "cbc:Name").text = _("Advance payment {0}").format(p.name)
            _tax_category(item, "cac:ClassifiedTaxCategory", l, with_reason=False)

            price = ET.SubElement(line, "cac:Price")
            ET.SubElement(price, "cbc:PriceAmount", currencyID=currency).text = "0.00"
    return invoice


def _invoice_total(doc):
    return flt(doc.rounded_total) if flt(doc.rounded_total) and not cint(doc.get("disable_rounded_total")) else flt(doc.grand_total)


def _sales_orders_of(doc):
    orders = {i.sales_order for i in doc.get("items") or [] if i.get("sales_order")}
    dns = {i.delivery_note for i in doc.get("items") or [] if i.get("delivery_note")}
    if dns:
        orders |= set(
            frappe.get_all(
                "Delivery Note Item",
                filters={"parent": ["in", list(dns)], "against_sales_order": ["is", "set"]},
                pluck="against_sales_order",
            )
        )
    return orders


def _open_advances_for(orders, customer, exclude_invoice=None):
    """Sent advances against these Sales Orders that still have something left (net)."""
    if not orders:
        return []
    names = frappe.get_all(
        "Payment Entry Reference",
        filters={"reference_doctype": "Sales Order", "reference_name": ["in", list(orders)], "docstatus": 1},
        pluck="parent",
    )
    result = []
    for name in sorted(set(names)):
        pe = frappe.get_doc(PAYMENT_ENTRY, name)
        if pe.party != customer or not is_advance(pe) or pe.get("custom_zatca_status") not in DONE_STATUSES:
            continue
        left = flt(get_net_amount(pe) - get_refunded_net(pe.name) - get_allocated_to_invoices(pe.name), 2)
        if left > 0.01:
            result.append(frappe._dict(name=pe.name, left=left))
    return result


def _advance_factor(adv):
    """Gross / net for an advance sent to ZATCA (1 + its VAT share), 1 for any other row."""
    if adv.reference_type != PAYMENT_ENTRY:
        return 1
    pe = frappe.get_doc(PAYMENT_ENTRY, adv.reference_name)
    return get_gross_factor(pe) if is_advance(pe) else 1


def _cap_advances(doc):
    """Use no more of the advances than the invoice needs: each 1.00 allocated from a
    VAT advance also clears its VAT, so it can cover at most what is left / (1 + rate)."""
    if doc.get("is_return") or not is_enabled(doc.company):
        return False
    changed = False
    room = _invoice_total(doc)
    for adv in doc.get("advances") or []:
        if flt(adv.allocated_amount) <= 0:
            continue
        factor = _advance_factor(adv)
        max_net = flt(max(room, 0) / factor, 2)
        if flt(adv.allocated_amount) - max_net > 0.001:
            adv.allocated_amount = max_net
            changed = True
        room -= flt(adv.allocated_amount) * factor
    return changed


def before_validate_sales_invoice(doc, method=None):
    _cap_advances(doc)


def validate_sales_invoice(doc, method=None):
    """ERPNext may re-allocate advances during validate (allocate automatically): cap again."""
    if _cap_advances(doc):
        doc.calculate_taxes_and_totals()


def validate_sales_invoice_advances(doc, method=None):
    """Before submit: only advances that reached ZATCA, never more than is left,
    and never skip an advance the customer paid for this order."""
    if not is_enabled(doc.company):
        return
    if doc.get("is_return"):
        return
    allocated = {}
    gross_used = 0
    for adv in doc.get("advances") or []:
        if flt(adv.allocated_amount) <= 0:
            continue
        gross_used += flt(adv.allocated_amount) * _advance_factor(adv)
        if adv.reference_type == PAYMENT_ENTRY:
            allocated[adv.reference_name] = allocated.get(adv.reference_name, 0) + flt(adv.allocated_amount)
    if gross_used - _invoice_total(doc) > 0.05:
        frappe.throw(
            _("The advances allocated (with VAT) are more than this invoice. Reduce the Allocated amounts on the Payments tab."),
            title=_("Too much advance"),
        )
    if gross_used < _invoice_total(doc) - 0.05:
        missing = [
            a for a in _open_advances_for(_sales_orders_of(doc), doc.customer)
            if flt(allocated.get(a.name)) < a.left - 0.01
        ]
        if missing:
            frappe.throw(
                _(
                    "The customer already paid an advance for this order: {0}. On the <b>Payments</b> tab, "
                    "click <b>Get Advances Received</b> and allocate it, or the customer is charged twice."
                ).format(", ".join(f"{a.name} ({a.left})" for a in missing)),
                title=_("Advance not used"),
            )
    for adv in doc.get("advances") or []:
        if adv.reference_type != PAYMENT_ENTRY or flt(adv.allocated_amount) <= 0:
            continue
        pe = frappe.get_doc(PAYMENT_ENTRY, adv.reference_name)
        if not is_advance(pe):
            continue
        if pe.get("custom_zatca_status") not in DONE_STATUSES:
            frappe.throw(
                _("Advance {0} has not been sent to ZATCA yet. Send it first.").format(pe.name)
            )
        left = flt(
            get_net_amount(pe) - get_refunded_net(pe.name) - get_allocated_to_invoices(pe.name),
            2,
        )
        if flt(adv.allocated_amount) - left > 0.01:
            frappe.throw(
                _("Advance {0} has only {1} left (excluding VAT).").format(pe.name, left)
            )


def reverse_advance_vat(doc, method=None):
    """After submit: the VAT on the allocated advances was declared when the
    customer paid. Post Dr VAT / Cr customer against this invoice so it is
    counted once and the invoice is settled."""
    if not is_vat_reversal_enabled(doc.company):
        return
    prepayments = get_prepayments(doc)
    if not prepayments:
        return
    by_account = {}
    for p in prepayments:
        if p.tax <= 0 or not p.tax_account:
            continue
        by_account[p.tax_account] = by_account.get(p.tax_account, Decimal("0")) + p.tax
    total = sum(by_account.values(), Decimal("0"))
    if total <= 0:
        return

    je = frappe.new_doc("Journal Entry")
    je.voucher_type = "Journal Entry"
    je.company = doc.company
    je.posting_date = doc.posting_date
    je.user_remark = _("Reversal of advance VAT already declared, for {0}").format(doc.name)
    for account, amount in by_account.items():
        je.append(
            "accounts",
            {
                "account": account,
                "debit_in_account_currency": flt(amount),
                "cost_center": doc.cost_center,
            },
        )
    je.append(
        "accounts",
        {
            "account": doc.debit_to,
            "party_type": "Customer",
            "party": doc.customer,
            "credit_in_account_currency": flt(total),
            "reference_type": "Sales Invoice",
            "reference_name": doc.name,
            "cost_center": doc.cost_center,
        },
    )
    je.flags.ignore_permissions = True
    je.insert()
    je.submit()
    doc.db_set("custom_advance_vat_reversal", je.name, update_modified=False)


def cancel_advance_vat_reversal(doc, method=None):
    """Before cancel: the reversal goes with the invoice."""
    name = doc.get("custom_advance_vat_reversal")
    if not name:
        return
    je = frappe.get_doc("Journal Entry", name)
    if je.docstatus == 1:
        je.flags.ignore_permissions = True
        je.flags.cancelling_with_invoice = True
        je.cancel()


def before_cancel_journal_entry(doc, method=None):
    """The advance VAT reversal can only go together with its final invoice."""
    if doc.flags.get("cancelling_with_invoice"):
        return
    invoice = frappe.db.get_value(
        "Sales Invoice", {"custom_advance_vat_reversal": doc.name, "docstatus": 1}, "name"
    )
    if invoice:
        frappe.throw(
            _("{0} reverses the advance VAT on {1}. Cancel the invoice instead; this entry goes with it.").format(
                doc.name, invoice
            ),
            title=_("Cancel the invoice instead"),
        )
