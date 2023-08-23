module  \$_DFF_N_ (input D, C, output Q);
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .DI(D), .Q(Q));
    else
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .DI(D), .Q(Q));
    endgenerate
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
endmodule

module  \$_DFF_P_ (input D, C, output Q);
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .DI(D), .Q(Q));
    else
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .DI(D), .Q(Q));
    endgenerate
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
endmodule

module  \$_DFFE_NN_ (input D, C, E, output Q);
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q));
    else
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q));
    endgenerate
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
endmodule

module  \$_DFFE_PN_ (input D, C, E, output Q);
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q));
    else
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q));
    endgenerate
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q);
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q));
    else
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q));
    endgenerate
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
endmodule

module  \$_DFFE_PP_ (input D, C, E, output Q);
    parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
    generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q));
    else
        TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q));
    endgenerate
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
endmodule

module  \$_DFF_NP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule

module  \$_SDFF_NP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFF_NP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFF_PP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFF_PP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule

module  \$_DFFE_NP0P_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFFE_NP1P_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFFE_PP0P_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFFE_PP1P_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule

module  \$_DFFE_NP0N_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFFE_NP1N_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFFE_PP0N_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFFE_PP1N_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule

module  \$_SDFFE_NP0P_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFFE_NP1P_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFFE_PP0P_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFFE_PP1P_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule

module  \$_SDFFE_NP0N_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFFE_NP1N_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFFE_PP0N_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFFE_PP1N_ (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("AUTO"), .CEMUX("INV"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule

module \$_ALDFF_NP_ (input C, L, AD, D, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMODE("PRLD"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(L), .DI(D), .M(AD), .Q(Q)); endmodule
module \$_ALDFF_PP_ (input C, L, AD, D, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMODE("PRLD"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(L), .DI(D), .M(AD), .Q(Q)); endmodule

module \$_ALDFFE_NPN_ (input C, E, L, AD, D, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("INV"), .CLKMUX("INV"), .LSRMODE("PRLD"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(L), .DI(D), .M(AD), .Q(Q)); endmodule
module \$_ALDFFE_NPP_ (input C, E, L, AD, D, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMODE("PRLD"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(L), .DI(D), .M(AD), .Q(Q)); endmodule
module \$_ALDFFE_PPN_ (input C, E, L, AD, D, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("INV"), .CLKMUX("CLK"), .LSRMODE("PRLD"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(L), .DI(D), .M(AD), .Q(Q)); endmodule
module \$_ALDFFE_PPP_ (input C, E, L, AD, D, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMODE("PRLD"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(L), .DI(D), .M(AD), .Q(Q)); endmodule

`include "cells_ff.vh"
`include "cells_io.vh"

`ifndef NO_LUT
module \$lut (A, Y);
    parameter WIDTH = 0;
    parameter LUT = 0;

    (* force_downto *)
    input [WIDTH-1:0] A;
    output Y;

    generate
        if (WIDTH == 1) begin
            localparam [15:0] INIT = {{8{LUT[1]}}, {8{LUT[0]}}};
            LUT4 #(.INIT(INIT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(1'b0), .B(1'b0), .C(1'b0), .D(A[0]));
        end else
        if (WIDTH == 2) begin
            localparam [15:0] INIT = {{4{LUT[3]}}, {4{LUT[2]}}, {4{LUT[1]}}, {4{LUT[0]}}};
            LUT4 #(.INIT(INIT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(1'b0), .B(1'b0), .C(A[0]), .D(A[1]));
        end else
        if (WIDTH == 3) begin
            localparam [15:0] INIT = {{2{LUT[7]}}, {2{LUT[6]}}, {2{LUT[5]}}, {2{LUT[4]}}, {2{LUT[3]}}, {2{LUT[2]}}, {2{LUT[1]}}, {2{LUT[0]}}};
            LUT4 #(.INIT(INIT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(1'b0), .B(A[0]), .C(A[1]), .D(A[2]));
        end else
        if (WIDTH == 4) begin
            LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
        `ifndef NO_PFUMUX
        end else
        if (WIDTH == 5) begin
            wire f0, f1;
            LUT4 #(.INIT(LUT[15: 0])) lut0 (.Z(f0),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[31:16])) lut1 (.Z(f1),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            PFUMX mux5(.ALUT(f1), .BLUT(f0), .C0(A[4]), .Z(Y));
        end else
        if (WIDTH == 6) begin
            wire f0, f1, f2, f3, g0, g1;
            LUT4 #(.INIT(LUT[15: 0])) lut0 (.Z(f0),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[31:16])) lut1 (.Z(f1),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[47:32])) lut2 (.Z(f2),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[63:48])) lut3 (.Z(f3),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            PFUMX mux50(.ALUT(f1), .BLUT(f0), .C0(A[4]), .Z(g0));
            PFUMX mux51(.ALUT(f3), .BLUT(f2), .C0(A[4]), .Z(g1));
            L6MUX21 mux6 (.D0(g0), .D1(g1), .SD(A[5]), .Z(Y));
        end else
        if (WIDTH == 7) begin
            wire f0, f1, f2, f3, f4, f5, f6, f7, g0, g1, g2, g3, h0, h1;
            LUT4 #(.INIT(LUT[15: 0])) lut0 (.Z(f0),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[31:16])) lut1 (.Z(f1),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[47:32])) lut2 (.Z(f2),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[63:48])) lut3 (.Z(f3),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[79:64])) lut4 (.Z(f4),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[95:80])) lut5 (.Z(f5),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[111: 96])) lut6 (.Z(f6),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[127:112])) lut7 (.Z(f7),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            PFUMX mux50(.ALUT(f1), .BLUT(f0), .C0(A[4]), .Z(g0));
            PFUMX mux51(.ALUT(f3), .BLUT(f2), .C0(A[4]), .Z(g1));
            PFUMX mux52(.ALUT(f5), .BLUT(f4), .C0(A[4]), .Z(g2));
            PFUMX mux53(.ALUT(f7), .BLUT(f6), .C0(A[4]), .Z(g3));
            L6MUX21 mux60 (.D0(g0), .D1(g1), .SD(A[5]), .Z(h0));
            L6MUX21 mux61 (.D0(g2), .D1(g3), .SD(A[5]), .Z(h1));
            L6MUX21 mux7  (.D0(h0), .D1(h1), .SD(A[6]), .Z(Y));
        `endif
        end else begin
            wire _TECHMAP_FAIL_ = 1;
        end
    endgenerate
endmodule
`endif
