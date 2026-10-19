module sv_top(input logic a, output logic y);
	// Instantiates VHDL entity to ensure mixed -f list is required
	vhdl_mod u_vhdl(.a(a), .y(y));
endmodule
