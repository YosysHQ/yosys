module \$__MUL18X18 (input [17:0] A, input [17:0] B, output [35:0] Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter B_WIDTH = 0;
	parameter Y_WIDTH = 0;

	wire [A_WIDTH+B_WIDTH-1:0] mult_result;

	fiftyfivenm_mac_mult #(
		.dataa_clock ("none"),
		.datab_clock ("none"),
		.signa_clock ("none"),
		.signb_clock ("none"),
		.dataa_width (A_WIDTH),
		.datab_width (B_WIDTH),
		.lpm_type    ("fiftyfivenm_mac_mult")
	) _TECHMAP_REPLACE_mac_mult (
		//Data path
		.dataa  ( A                          ),
		.datab  ( B                          ),
		.dataout( mult_result                ),
		.signa  ( A_SIGNED != 0 ? 1'b1 : 1'b0),
		.signb  ( B_SIGNED != 0 ? 1'b1 : 1'b0)
	);

	fiftyfivenm_mac_out #(
		.dataa_width  (A_WIDTH + B_WIDTH),
		.output_clock ("none"),
		.lpm_type     ("fiftyfivenm_mac_out")
	) _TECHMAP_REPLACE_mac_out (
		.dataa   (mult_result),
		.dataout (Y)
	);
endmodule


module \$__MUL9X9 (input [8:0] A, input [8:0] B, output [17:0] Y);
        parameter A_SIGNED = 0;
        parameter B_SIGNED = 0;
        parameter A_WIDTH = 0;
        parameter B_WIDTH = 0;
        parameter Y_WIDTH = 0;

	wire [A_WIDTH+B_WIDTH-1:0] mult_result;

        fiftyfivenm_mac_mult #(
                .dataa_clock ("none"),
                .datab_clock ("none"),
                .signa_clock ("none"),
                .signb_clock ("none"),
                .dataa_width (A_WIDTH),
                .datab_width (B_WIDTH),
		.lpm_type    ("fiftyfivenm_mac_mult")
        ) _TECHMAP_REPLACE_mac_mult (
                //Data path
                .dataa  ( A                          ),
                .datab  ( B                          ),
                .dataout( mult_result                ),
                .signa  ( A_SIGNED != 0 ? 1'b1 : 1'b0),
                .signb  ( B_SIGNED != 0 ? 1'b1 : 1'b0)
        );

	fiftyfivenm_mac_out #(
		.dataa_width  (A_WIDTH + B_WIDTH),
		.output_clock ("none"),
		.lpm_type     ("fiftyfivenm_mac_out")
	) _TECHMAP_REPLACE_mac_out (
		.dataa   (mult_result),
		.dataout (Y)
	);
endmodule

