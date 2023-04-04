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

module \$lut (A, Y);
	parameter WIDTH = 0;
	parameter LUT = 0;
	input [WIDTH-1:0] A;
	output Y;

	localparam rep = 1<<(4-WIDTH);
	wire [3:0] I;

	generate
		if(WIDTH == 1) begin
			assign I = {1'b0, 1'b0, 1'b0, A[0]};
		end else if(WIDTH == 2) begin
			assign I = {1'b0, 1'b0, A[1], A[0]};
		end else if(WIDTH == 3) begin
			assign I = {1'b0, A[2], A[1], A[0]};
		end else if(WIDTH == 4) begin
			assign I = {A[3], A[2], A[1], A[0]};
		end else begin
			wire _TECHMAP_FAIL_ = 1;
		end
	endgenerate

	LUT4 #(.INIT({rep{LUT}})) _TECHMAP_REPLACE_ (.A(I[0]), .B(I[1]), .C(I[2]), .D(I[3]), .Z(Y));
endmodule

`include "cells_io.vh"
