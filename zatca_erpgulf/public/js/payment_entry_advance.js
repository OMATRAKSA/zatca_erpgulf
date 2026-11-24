// Customer advances sent to ZATCA as advance invoices (386) and their refunds (381).
// An advance carries VAT, or is marked zero-rated / exempt / out of scope, or is split by category.
// Buttons only show for companies with "Send customer advance Payment Entries to ZATCA".
frappe.ui.form.on("Payment Entry", {
	refresh(frm) {
		if (frm.doc.docstatus !== 1 || frm.doc.party_type !== "Customer") return;

		frappe.db
			.get_value("Company", frm.doc.company, "custom_zatca_advance_payment_entry")
			.then(({ message }) => {
				if (!message || !message.custom_zatca_advance_payment_entry) return;

				const sent = ["CLEARED", "REPORTED"].includes(frm.doc.custom_zatca_status);
				const has_vat = (frm.doc.taxes || []).length > 0;
				const has_split = (frm.doc.custom_zatca_advance_lines || []).length > 0;
				const no_vat_category =
					!!frm.doc.custom_zatca_tax_category &&
					frm.doc.custom_zatca_tax_category !== "Standard";
				const is_advance =
					frm.doc.payment_type === "Receive" && (has_vat || has_split || no_vat_category);
				const is_refund =
					frm.doc.payment_type === "Pay" && !!frm.doc.custom_advance_refund_against;

				if (sent) {
					frm.dashboard.set_headline_alert(
						__("ZATCA: {0}", [frm.doc.custom_zatca_status]),
						"green"
					);
				} else if (is_advance || is_refund) {
					frm.dashboard.set_headline_alert(
						__("Not sent to ZATCA yet. This is not a valid tax invoice. Click Send to ZATCA."),
						"red"
					);
				}

				if ((is_advance || is_refund) && !sent) {
					frm.add_custom_button(__("Send to ZATCA"), () => {
						frappe.call({
							method: "zatca_erpgulf.zatca_erpgulf.payment_entry_advance.resend_payment_entry",
							args: { name: frm.doc.name },
							freeze: true,
							freeze_message: __("Sending to ZATCA..."),
							callback: () => frm.reload_doc(),
						});
					});
				}

				if (is_advance && sent) {
					frm.add_custom_button(__("Refund Advance"), () => {
						frappe.call({
							method: "zatca_erpgulf.zatca_erpgulf.payment_entry_advance.make_advance_refund",
							args: { source_name: frm.doc.name },
							callback: (r) => {
								if (!r.message) return;
								const doc = frappe.model.sync(r.message)[0];
								frappe.set_route("Form", doc.doctype, doc.name);
							},
						});
					}, __("Create"));
				}
			});
	},
});

// Split by VAT category: show each row's VAT as it is typed (the server recomputes it).
frappe.ui.form.on("ZATCA Advance Line", {
	tax_category(frm, cdt, cdn) {
		const row = locals[cdt][cdn];
		frappe.model.set_value(cdt, cdn, "rate", row.tax_category === "Standard" ? 15 : 0);
	},
	amount(frm, cdt, cdn) {
		set_line_vat(cdt, cdn);
	},
	rate(frm, cdt, cdn) {
		set_line_vat(cdt, cdn);
	},
});

function set_line_vat(cdt, cdn) {
	const row = locals[cdt][cdn];
	const vat = row.tax_category === "Standard" ? flt((row.amount * row.rate) / 100, 2) : 0;
	frappe.model.set_value(cdt, cdn, "tax_amount", vat);
}
