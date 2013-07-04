
// Based on the simulation models from /opt/altera/13.0/quartus/eda/sim_lib/cycloneiii_atoms.v

module cycloneiii_lcell_comb (dataa, datab, datac, datad, cin, combout, cout);

input dataa, datab, datac, datad, cin;
output combout, cout;

parameter lut_mask = 16'hFFFF;
parameter sum_lutc_input = "datac";
parameter dont_touch = "off";
parameter lpm_type = "cycloneiii_lcell_comb";

reg cout_tmp, combout_tmp;
reg [1:0] isum_lutc_input;

// 4-input LUT function
function lut4;
	input [15:0] mask;
	input dataa, datab, datac, datad;
	begin
	    lut4 = datad ? ( datac ? ( datab ? ( dataa ? mask[15] : mask[14])
					     : ( dataa ? mask[13] : mask[12]))
				   : ( datab ? ( dataa ? mask[11] : mask[10])
					     : ( dataa ? mask[ 9] : mask[ 8])))
			 : ( datac ? ( datab ? ( dataa ? mask[ 7] : mask[ 6])
					     : ( dataa ? mask[ 5] : mask[ 4]))
				   : ( datab ? ( dataa ? mask[ 3] : mask[ 2])
					     : ( dataa ? mask[ 1] : mask[ 0])));
	end
endfunction

initial
	if (sum_lutc_input == "datac")
		isum_lutc_input = 0;
	else if (sum_lutc_input == "cin")
		isum_lutc_input = 1;
	else
		isum_lutc_input = 2;

always @* begin
	if (isum_lutc_input == 0) // datac 
		combout_tmp = lut4(lut_mask, dataa, datab, datac, datad);
	else if (isum_lutc_input == 1) // cin
		combout_tmp = lut4(lut_mask, dataa, datab, cin, datad);
	cout_tmp = lut4(lut_mask, dataa, datab, cin, 'b0);
end

assign combout = combout_tmp;
assign cout = cout_tmp;

endmodule

// ----------------------------------------------------------------------

module cycloneiii_io_ibuf (i, ibar, o);

parameter differential_mode = "false";
parameter bus_hold = "false";
parameter simulate_z_as = "Z";
parameter lpm_type = "cycloneiii_io_ibuf";

input i, ibar;
output o;

assign o = i;

endmodule

// ----------------------------------------------------------------------

module cycloneiii_io_obuf (i, oe, seriesterminationcontrol, devoe, o, obar);

parameter open_drain_output = "false";
parameter bus_hold = "false";
parameter lpm_type = "cycloneiii_io_obuf";

input i, oe, devoe;
input [15:0] seriesterminationcontrol; 
output o, obar;

assign o = i;
assign obar = ~i;

endmodule

