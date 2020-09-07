(* techmap_celltype = "$alu" *)
module _80_quicklogic_alu (A, B, CI, BI, X, Y, CO);
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;
    parameter A_WIDTH  = 1;
    parameter B_WIDTH  = 1;
    parameter Y_WIDTH  = 1;

    (* force_downto *)
    input [A_WIDTH-1:0] A;
    (* force_downto *)
    input [B_WIDTH-1:0] B;
    (* force_downto *)
    output [Y_WIDTH-1:0] X, Y;

    input CI, BI;
    (* force_downto *)
    output [Y_WIDTH-1:0] CO;

    wire _TECHMAP_FAIL_ = Y_WIDTH <= 2;

    (* force_downto *)
    wire [Y_WIDTH-1:0] A_buf, B_buf;
    \$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
    \$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

    (* force_downto *)
    wire [Y_WIDTH-1:0] AA = A_buf;
    (* force_downto *)
    wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;
    // force_downto *)
    //wire [Y_WIDTH-1:0] C = {CO, CI};

    full_adder first_inst(
            .A(AA[0]),
            .B(BB[0]),
			.CI(CI),
			.CO(CO[0]),
			.S(Y[0]));

    genvar i;
    generate for (i = 1; i < Y_WIDTH-1; i = i + 1) begin: slice
        full_adder inst_i (
			.A(AA[i]),
			.B(BB[i]),
			.CI(CO[i-1]),
			.CO(CO[i]),
			.S(Y[i])
		);

    end: slice	  
    endgenerate
    
    full_adder inst_last (
        .A(AA[Y_WIDTH-1]),
        .B(BB[Y_WIDTH-1]),
        .CI(CO[Y_WIDTH-2]),
        .CO(CO[Y_WIDTH-1]),
        .S(Y[Y_WIDTH-1])
    );

    /* End implementation */
    assign X = AA ^ BB;
endmodule
