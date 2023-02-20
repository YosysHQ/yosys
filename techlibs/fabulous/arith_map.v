`default_nettype none

`ifdef ARITH_ha
(* techmap_celltype = "$alu" *)
module _80_fabulous_ha_alu (A, B, CI, BI, X, Y, CO);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

parameter _TECHMAP_CONSTMSK_CI_ = 0;
parameter _TECHMAP_CONSTVAL_CI_ = 0;

(* force_downto *)
input [A_WIDTH-1:0] A;
(* force_downto *)
input [B_WIDTH-1:0] B;
input CI, BI;
(* force_downto *)
output [Y_WIDTH-1:0] X, Y, CO;

(* force_downto *)
wire [Y_WIDTH-1:0] A_buf, B_buf;
\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

(* force_downto *)
wire [Y_WIDTH-1:0] AA = A_buf;
(* force_downto *)
wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;
wire [Y_WIDTH:0] CARRY;


LUT4_HA #(
	.INIT(16'b0),
	.I0MUX(1'b1)
) carry_statrt (
	.I0(), .I1(CI), .I2(CI), .I3(),
	.Ci(),
	.Co(CARRY[0])
);

// Carry chain
genvar i;
generate for (i = 0; i < Y_WIDTH; i = i + 1) begin:slice
	LUT4_HA #(
		.INIT(16'b1001_0110_1001_0110), // full adder sum over (I2, I1, I0)
		.I0MUX(1'b1)
	) lut_i (
		.I0(), .I1(AA[i]), .I2(BB[i]), .I3(),
		.Ci(CARRY[i]),
		.O(Y[i]),
		.Co(CARRY[i+1])
	);

	assign CO[i] = (AA[i] && BB[i]) || ((Y[i] ^ AA[i] ^ BB[i]) && (AA[i] || BB[i]));
end endgenerate

assign X = AA ^ BB;

endmodule
`endif

