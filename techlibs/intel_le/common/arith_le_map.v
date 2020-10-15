`default_nettype none

module \$alu (A, B, CI, BI, X, Y, CO);

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
(* force_downto *)
wire [Y_WIDTH-1:0] BX = B_buf;
wire [Y_WIDTH-1:0] BSUM;
wire [Y_WIDTH:0] LE_CARRY;

// Start of carry chain
generate
    if (_TECHMAP_CONSTMSK_CI_ == 1) begin
        assign ALM_CARRY[0] = _TECHMAP_CONSTVAL_CI_;
    end else begin
        MISTRAL_ALUT_ARITH #(
            .LUT0(16'b1010_1010_1010_1010), // Q = A
            .LUT1(16'b0000_0000_0000_0000), // Q = 0 (LUT1's input to the adder is inverted)
        ) alm_start (
            .A(CI), .B(1'b1), .C(1'b1), .D0(1'b1), .D1(1'b1),
            .CI(1'b0),
            .CO(ALM_CARRY[0])
        );
    end
endgenerate

// Carry chain
genvar i;
generate for (i = 0; i < Y_WIDTH; i = i + 1) begin:slice
    // TODO: mwk suggests that a pass could merge pre-adder logic into this.
    MISTRAL_ALUT_ARITH #(
        .LUT0(16'b0110_0110_0110_0110) // Q = A ? ~B : B
    ) alm_i (
        .A(BI), .B(BX[i]), .C(1'b0), .D(1'b0),
        .CI(1'b0),
        .SO(BSUM[i]),
        .CO()
    );
    MISTRAL_ALUT_ARITH #(
    		.LUT0(16'b1010_1010_1010_1010), // SUM = A xor B xor CI
    		// CARRYi+1 = A and B or A and CI or B and CI 
    		.sum_lutc_input("cin")
    	) alm_start (
    		.A(AA[i]), .B(BX[i]), .C(1'b1), .D(1'b1),
    		.CI(LE_CARRY),
    		.SO(Y[i]),
    		.CO(ALM_CARRY[i+1])
    	);
    // ALM carry chain is not directly accessible, so calculate the carry through soft logic if really needed.
    assign CO[i] = (AA[i] && BB[i]) || ((Y[i] ^ AA[i] ^ BB[i]) && (AA[i] || BB[i]));
end endgenerate

assign X = AA ^ BB;

endmodule
