// Diamond flip-flops
module FD1P3AX(input     D, SP, CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))        _TECHMAP_REPLACE_ (.CLK(CK), .LSR(|0), .CE(SP), .DI(D), .Q(Q)); endmodule
module FD1P3AY(input     D, SP, CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("ASYNC"))        _TECHMAP_REPLACE_ (.CLK(CK), .LSR(|0), .CE(SP), .DI(D), .Q(Q)); endmodule
module FD1P3BX(input PD, D, SP, CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("ASYNC"))        _TECHMAP_REPLACE_ (.CLK(CK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule
module FD1P3DX(input CD, D, SP, CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))        _TECHMAP_REPLACE_ (.CLK(CK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module FD1P3IX(input CD, D, SP, CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(CK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module FD1P3JX(input PD, D, SP, CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(CK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule
module FD1S3AX(input     D,     CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("1"),  .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))        _TECHMAP_REPLACE_ (.CLK(CK), .LSR(|0),          .DI(D), .Q(Q)); endmodule
module FD1S3AY(input     D,     CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("1"),  .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("ASYNC"))        _TECHMAP_REPLACE_ (.CLK(CK), .LSR(|0),          .DI(D), .Q(Q)); endmodule
module FD1S3BX(input PD, D,     CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("1"),  .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("ASYNC"))        _TECHMAP_REPLACE_ (.CLK(CK), .LSR(PD),          .DI(D), .Q(Q)); endmodule
module FD1S3DX(input CD, D,     CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("1"),  .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))        _TECHMAP_REPLACE_ (.CLK(CK), .LSR(CD),          .DI(D), .Q(Q)); endmodule
module FD1S3IX(input CD, D,     CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("1"),  .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(CK), .LSR(CD),          .DI(D), .Q(Q)); endmodule
module FD1S3JX(input PD, D,     CK, output Q); parameter GSR = "ENABLED"; TRELLIS_FF #(.GSR(GSR), .CEMUX("1"),  .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(CK), .LSR(PD),          .DI(D), .Q(Q)); endmodule

// TODO: Diamond latches
// module FL1P3AY(); endmodule
// module FL1P3AZ(); endmodule
// module FL1P3BX(); endmodule
// module FL1P3DX(); endmodule
// module FL1P3IY(); endmodule
// module FL1P3JY(); endmodule
// module FL1S3AX(); endmodule
// module FL1S3AY(); endmodule

// Diamond I/O registers
module IFS1P3BX(input PD, D, SP, SCLK, output Q); parameter GSR = "ENABLED"; (* syn_useioff, ioff_dir="input" *) TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("ASYNC"))       _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule
module IFS1P3DX(input CD, D, SP, SCLK, output Q); parameter GSR = "ENABLED"; (* syn_useioff, ioff_dir="input" *) TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))       _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module IFS1P3IX(input CD, D, SP, SCLK, output Q); parameter GSR = "ENABLED"; (* syn_useioff, ioff_dir="input" *) TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE")) _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module IFS1P3JX(input PD, D, SP, SCLK, output Q); parameter GSR = "ENABLED"; (* syn_useioff, ioff_dir="input" *) TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("LSR_OVER_CE")) _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule

module OFS1P3BX(input PD, D, SP, SCLK, output Q); parameter GSR = "ENABLED"; (* syn_useioff, ioff_dir="output" *) TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("ASYNC"))       _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule
module OFS1P3DX(input CD, D, SP, SCLK, output Q); parameter GSR = "ENABLED"; (* syn_useioff, ioff_dir="output" *) TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))       _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module OFS1P3IX(input CD, D, SP, SCLK, output Q); parameter GSR = "ENABLED"; (* syn_useioff, ioff_dir="output" *) TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("LSR_OVER_CE")) _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(CD), .CE(SP), .DI(D), .Q(Q)); endmodule
module OFS1P3JX(input PD, D, SP, SCLK, output Q); parameter GSR = "ENABLED"; (* syn_useioff, ioff_dir="output" *) TRELLIS_FF #(.GSR(GSR), .CEMUX("CE"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("SET"),   .SRMODE("LSR_OVER_CE")) _TECHMAP_REPLACE_ (.CLK(SCLK), .LSR(PD), .CE(SP), .DI(D), .Q(Q)); endmodule

// TODO: Diamond I/O latches
// module IFS1S1B(input PD, D, SCLK, output Q); endmodule
// module IFS1S1D(input CD, D, SCLK, output Q); endmodule
// module IFS1S1I(input PD, D, SCLK, output Q); endmodule
// module IFS1S1J(input CD, D, SCLK, output Q); endmodule
