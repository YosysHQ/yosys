`default_nettype none

(* techmap_celltype = "$alu" *)
module _80_nx_cy_alu (A, B, CI, BI, X, Y, CO);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

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

	function integer round_up4;
		input integer N;
		begin
			round_up4 = ((N + 3) / 4) * 4;
		end
	endfunction

	localparam Y_WIDTH4 = round_up4(Y_WIDTH);

	(* force_downto *)
	wire [Y_WIDTH4-1:0] AA = A_buf;
	(* force_downto *)
	wire [Y_WIDTH4-1:0] BB = BI ? ~B_buf : B_buf;
	(* force_downto *)
	wire [Y_WIDTH4-1:0] BX = B_buf;
	(* force_downto *)
	wire [Y_WIDTH4:0] C = {CO, CI};
	(* force_downto *)
	wire [Y_WIDTH4-1:0] FCO, Y1;

	genvar i;
	generate for (i = 0; i < Y_WIDTH4; i = i + 4) begin:slice
        NX_CY cy_i (
            .CI(C[i]),
            .A1(AA[i]), .A2(AA[i+1]), .A3(AA[i+2]), .A4(AA[i+3]),
            .B1(BB[i]), .B2(BB[i+1]), .B3(BB[i+2]), .B4(BB[i+3]),
            .S1(Y1[i]), .S2(Y1[i+1]), .S3(Y1[i+2]), .S4(Y1[i+3]),
            .CO(FCO[i])
        );

		assign CO[i] = (AA[i] && BB[i]) || (C[i] && (AA[i] || BB[i]));
        if (i+1 < Y_WIDTH)
		    assign CO[i+1] = (AA[i+1] && BB[i+1]) || (C[i+1] && (AA[i+1] || BB[i+1]));
		if (i+2 < Y_WIDTH)
            assign CO[i+2] = (AA[i+2] && BB[i+2]) || (C[i+2] && (AA[i+2] || BB[i+2]));
        if (i+3 < Y_WIDTH)
            assign CO[i+3] = FCO[i];

	end endgenerate

	assign X = AA ^ BB;
    assign Y = Y1[Y_WIDTH-1:0];
endmodule
