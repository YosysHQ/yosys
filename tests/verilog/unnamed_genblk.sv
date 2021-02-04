// This test is taken directly from Section 27.6 of IEEE 1800-2017

module top;
	parameter genblk2 = 0;
	genvar i;

	// The following generate block is implicitly named genblk1

	if (genblk2) logic a; // top.genblk1.a
	else logic b; // top.genblk1.b

	// The following generate block is implicitly named genblk02
	// as genblk2 is already a declared identifier

	if (genblk2) logic a; // top.genblk02.a
	else logic b; // top.genblk02.b

	// The following generate block would have been named genblk3
	// but is explicitly named g1

	for (i = 0; i < 1; i = i + 1) begin : g1 // block name
		// The following generate block is implicitly named genblk1
		// as the first nested scope inside g1
		if (1) logic a; // top.g1[0].genblk1.a
	end

	// The following generate block is implicitly named genblk4 since
	// it belongs to the fourth generate construct in scope "top".
	// The previous generate block would have been
	// named genblk3 if it had not been explicitly named g1

	for (i = 0; i < 1; i = i + 1)
		// The following generate block is implicitly named genblk1
		// as the first nested generate block in genblk4
		if (1) logic a; // top.genblk4[0].genblk1.a

	// The following generate block is implicitly named genblk5
	if (1) logic a; // top.genblk5.a
endmodule
