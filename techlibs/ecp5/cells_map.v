module  \$_DFF_N_ (input D, C, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .DI(D), .Q(Q)); endmodule
module  \$_DFF_P_ (input D, C, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .DI(D), .Q(Q)); endmodule

module  \$_DFFE_NN_ (input D, C, E, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q)); endmodule
module  \$_DFFE_PN_ (input D, C, E, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q)); endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q)); endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q)); endmodule

module  \$_DFF_NN0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_NN1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_PN1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule

module  \$_DFF_NP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule

module  \$__DFFS_NN0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_NN1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_PN0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_PN1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule

module  \$__DFFS_NP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_NP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_PP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_PP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule

module  \$__DFFE_NN0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_NN1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_PN0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_PN1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule

module  \$__DFFE_NP0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_NP1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_PP0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_PP1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule

module  \$__DFFSE_NN0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_NN1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_PN0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_PN1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule

module  \$__DFFSE_NP0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_NP1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_PP0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_PP1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule

`include "cells_ff.vh"
`include "cells_io.vh"

`ifndef NO_LUT
module \$lut (A, Y);
    parameter WIDTH = 0;
    parameter LUT = 0;

    input [WIDTH-1:0] A;
    output Y;

    // Need to swap input ordering, and fix init accordingly,
    // to match ABC's expectation of LUT inputs in non-decreasing
    // delay order
    localparam P_WIDTH = WIDTH < 4 ? 4 : WIDTH;
    function [P_WIDTH-1:0] permute_index;
        input [P_WIDTH-1:0] i;
        integer j;
        begin
            permute_index = 0;
            for (j = 0; j < P_WIDTH; j = j + 1)
                permute_index[P_WIDTH-1 - j] = i[j];
        end
    endfunction

    function [2**P_WIDTH-1:0] permute_init;
        integer i;
        begin
            permute_init = 0;
            for (i = 0; i < 2**P_WIDTH; i = i + 1)
                permute_init[i] = LUT[permute_index(i)];
        end
    endfunction

    parameter [2**P_WIDTH-1:0] P_LUT = permute_init();

    generate
        if (WIDTH == 1) begin
            LUT4 #(.INIT(P_LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(1'b0), .B(1'b0), .C(1'b0), .D(A[0]));
        end else
        if (WIDTH == 2) begin
            LUT4 #(.INIT(P_LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(1'b0), .B(1'b0), .C(A[1]), .D(A[0]));
        end else
        if (WIDTH == 3) begin
            LUT4 #(.INIT(P_LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(1'b0), .B(A[2]), .C(A[1]), .D(A[0]));
        end else
        if (WIDTH == 4) begin
            LUT4 #(.INIT(P_LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[3]), .B(A[2]), .C(A[1]), .D(A[0]));
        `ifndef NO_PFUMUX
        end else
        if (WIDTH == 5) begin
            wire f0, f1;
            LUT4 #(.INIT(P_LUT[15: 0])) lut0 (.Z(f0),
                .A(A[4]), .B(A[3]), .C(A[2]), .D(A[1]));
            LUT4 #(.INIT(P_LUT[31:16])) lut1 (.Z(f1),
                .A(A[4]), .B(A[3]), .C(A[2]), .D(A[1]));
            PFUMX mux5(.ALUT(f1), .BLUT(f0), .C0(A[0]), .Z(Y));
        end else
        if (WIDTH == 6) begin
            wire f0, f1, f2, f3, g0, g1;
            LUT4 #(.INIT(P_LUT[15: 0])) lut0 (.Z(f0),
                .A(A[5]), .B(A[4]), .C(A[3]), .D(A[2]));
            LUT4 #(.INIT(P_LUT[31:16])) lut1 (.Z(f1),
                .A(A[5]), .B(A[4]), .C(A[3]), .D(A[2]));

            LUT4 #(.INIT(P_LUT[47:32])) lut2 (.Z(f2),
                .A(A[5]), .B(A[4]), .C(A[3]), .D(A[2]));
            LUT4 #(.INIT(P_LUT[63:48])) lut3 (.Z(f3),
                .A(A[5]), .B(A[4]), .C(A[3]), .D(A[2]));

            PFUMX mux50(.ALUT(f1), .BLUT(f0), .C0(A[1]), .Z(g0));
            PFUMX mux51(.ALUT(f3), .BLUT(f2), .C0(A[1]), .Z(g1));
            L6MUX21 mux6 (.D0(g0), .D1(g1), .SD(A[0]), .Z(Y));
        end else
        if (WIDTH == 7) begin
            wire f0, f1, f2, f3, f4, f5, f6, f7, g0, g1, g2, g3, h0, h1;
            LUT4 #(.INIT(P_LUT[15: 0])) lut0 (.Z(f0),
                .A(A[6]), .B(A[5]), .C(A[4]), .D(A[3]));
            LUT4 #(.INIT(P_LUT[31:16])) lut1 (.Z(f1),
                .A(A[6]), .B(A[5]), .C(A[4]), .D(A[3]));

            LUT4 #(.INIT(P_LUT[47:32])) lut2 (.Z(f2),
                .A(A[6]), .B(A[5]), .C(A[4]), .D(A[3]));
            LUT4 #(.INIT(P_LUT[63:48])) lut3 (.Z(f3),
                .A(A[6]), .B(A[5]), .C(A[4]), .D(A[3]));

            LUT4 #(.INIT(P_LUT[79:64])) lut4 (.Z(f4),
                .A(A[6]), .B(A[5]), .C(A[4]), .D(A[3]));
            LUT4 #(.INIT(P_LUT[95:80])) lut5 (.Z(f5),
                .A(A[6]), .B(A[5]), .C(A[4]), .D(A[3]));

            LUT4 #(.INIT(P_LUT[111: 96])) lut6 (.Z(f6),
                .A(A[6]), .B(A[5]), .C(A[4]), .D(A[3]));
            LUT4 #(.INIT(P_LUT[127:112])) lut7 (.Z(f7),
                .A(A[6]), .B(A[5]), .C(A[4]), .D(A[3]));

            PFUMX mux50(.ALUT(f1), .BLUT(f0), .C0(A[2]), .Z(g0));
            PFUMX mux51(.ALUT(f3), .BLUT(f2), .C0(A[2]), .Z(g1));
            PFUMX mux52(.ALUT(f5), .BLUT(f4), .C0(A[2]), .Z(g2));
            PFUMX mux53(.ALUT(f7), .BLUT(f6), .C0(A[2]), .Z(g3));
            L6MUX21 mux60 (.D0(g0), .D1(g1), .SD(A[1]), .Z(h0));
            L6MUX21 mux61 (.D0(g2), .D1(g3), .SD(A[1]), .Z(h1));
            L6MUX21 mux7  (.D0(h0), .D1(h1), .SD(A[0]), .Z(Y));
        `endif
        end else begin
            wire _TECHMAP_FAIL_ = 1;
        end
    endgenerate
endmodule
`endif
