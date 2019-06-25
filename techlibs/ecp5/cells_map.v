module  \$_DFF_N_ (input D, C, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .DI(D), .Q(Q)); endmodule
module  \$_DFF_P_ (input D, C, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .DI(D), .Q(Q)); endmodule

module  \$_DFFE_NN_ (input D, C, E, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("INV"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q)); endmodule
module  \$_DFFE_PN_ (input D, C, E, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("INV"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q)); endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q)); endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q)); endmodule

module  \$_DFF_NN0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_NN1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_PN1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule

module  \$_DFF_NP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule

module  \$__DFFS_NN0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_NN1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_PN0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_PN1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(!R), .DI(D), .Q(Q)); endmodule

module  \$__DFFS_NP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_NP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_PP0_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFS_PP1_ (input D, C, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(R), .DI(D), .Q(Q)); endmodule

module  \$__DFFE_NN0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_NN1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_PN0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_PN1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule

module  \$__DFFE_NP0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_NP1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_PP0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFE_PP1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule

module  \$__DFFSE_NN0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_NN1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_PN0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_PN1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(!R), .DI(D), .Q(Q)); endmodule

module  \$__DFFSE_NP0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_NP1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("INV"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_PP0 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule
module  \$__DFFSE_PP1 (input D, C, E, R, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(R), .DI(D), .Q(Q)); endmodule

// TODO: Diamond flip-flops
// module FD1P3AX(); endmodule
// module FD1P3AY(); endmodule
// module FD1P3BX(); endmodule
// module FD1P3DX(); endmodule
// module FD1P3IX(); endmodule
// module FD1P3JX(); endmodule
// module FD1S3AX(); endmodule
// module FD1S3AY(); endmodule
module FD1S3BX(input PD, D, CK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(CK), .LSR(PD), .DI(D), .Q(Q)); endmodule
module FD1S3DX(input CD, D, CK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(CK), .LSR(CD), .DI(D), .Q(Q)); endmodule
module FD1S3IX(input CD, D, CK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(CK), .LSR(CD), .DI(D), .Q(Q)); endmodule
module FD1S3JX(input PD, D, CK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(CK), .LSR(PD), .DI(D), .Q(Q)); endmodule
// module FL1P3AY(); endmodule
// module FL1P3AZ(); endmodule
// module FL1P3BX(); endmodule
// module FL1P3DX(); endmodule
// module FL1P3IY(); endmodule
// module FL1P3JY(); endmodule
// module FL1S3AX(); endmodule
// module FL1S3AY(); endmodule

// Diamond I/O buffers
module IB   (input I, output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("INPUT")) _TECHMAP_REPLACE_ (.B(I), .O(O)); endmodule
module IBPU (input I, output O); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("INPUT"))   _TECHMAP_REPLACE_ (.B(I), .O(O)); endmodule
module IBPD (input I, output O); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("INPUT")) _TECHMAP_REPLACE_ (.B(I), .O(O)); endmodule
module OB   (input I, output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I)); endmodule
module OBZ  (input I, T, output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I), .T(T)); endmodule
module OBZPU(input I, T, output O); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("OUTPUT"))   _TECHMAP_REPLACE_ (.B(O), .I(I), .T(T)); endmodule
module OBZPD(input I, T, output O); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I), .T(T)); endmodule
module OBCO (input I, output OT, OC); OLVDS _TECHMAP_REPLACE_ (.A(I), .Z(OT), .ZN(OC)); endmodule
module BB   (input I, T, output O, inout B); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("BIDIR")) _TECHMAP_REPLACE_ (.B(B), .I(I), .O(O), .T(T)); endmodule
module BBPU (input I, T, output O, inout B); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("BIDIR"))   _TECHMAP_REPLACE_ (.B(B), .I(I), .O(O), .T(T)); endmodule
module BBPD (input I, T, output O, inout B); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("BIDIR")) _TECHMAP_REPLACE_ (.B(B), .I(I), .O(O), .T(T)); endmodule
module ILVDS(input A, AN, output Z); TRELLIS_IO #(.DIR("INPUT"))  _TECHMAP_REPLACE_ (.B(A), .O(Z)); endmodule
module OLVDS(input A, output Z, ZN); TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(Z), .I(A)); endmodule

// Diamond I/O registers
module IFS1P3BX(input PD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule
module IFS1P3DX(input CD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module IFS1P3IX(input CD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module IFS1P3JX(input PD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule

module OFS1P3BX(input PD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule
module OFS1P3DX(input CD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module OFS1P3IX(input CD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module OFS1P3JX(input PD, D, SP, SCLK, output Q); TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule

// TODO: Diamond I/O latches
// module IFS1S1B(input PD, D, SCLK, output Q); endmodule
// module IFS1S1D(input CD, D, SCLK, output Q); endmodule
// module IFS1S1I(input PD, D, SCLK, output Q); endmodule
// module IFS1S1J(input CD, D, SCLK, output Q); endmodule

`ifndef NO_LUT
module \$lut (A, Y);
    parameter WIDTH = 0;
    parameter LUT = 0;

    input [WIDTH-1:0] A;
    output Y;

    generate
        if (WIDTH == 1) begin
            LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[0]), .B(1'b0), .C(1'b0), .D(1'b0));
        end else
        if (WIDTH == 2) begin
            LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[0]), .B(A[1]), .C(1'b0), .D(1'b0));
        end else
        if (WIDTH == 3) begin
            LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(1'b0));
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
