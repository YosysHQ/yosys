module  \$_DFFE_PN0P_ (input D, C, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET("RESET"), .SRMUX("INV"), .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C) ,.ce(E), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFFE_PN1P_ (input D, C, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET("SET"), .SRMUX("INV"), .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .ce(E), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFFE_PP0P_ (input D, C, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET("RESET"), .SRMUX("SR"),  .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .ce(E), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DFFE_PP1P_ (input D, C, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET("SET"), .SRMUX("SR"), . SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .ce(E), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule

module  \$_SDFFE_PN0P_ (input D, C, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET("RESET"), .SRMUX("INV"), .SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C) ,.ce(E), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFFE_PN1P_ (input D, C, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET("SET"), .SRMUX("INV"), .SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .ce(E), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFFE_PP0P_ (input D, C, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET("RESET"), .SRMUX("SR"),  .SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .ce(E), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_SDFFE_PP1P_ (input D, C, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET("SET"), .SRMUX("SR"), . SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .ce(E), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule

module  \$_DLATCH_NN0_ (input D, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("LATCH"), .REGSET("RESET"), .SRMUX("INV"), .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(E) ,.ce(1'b1), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DLATCH_NN1_ (input D, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("LATCH"), .REGSET("SET"), .SRMUX("INV"), .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(E), .ce(1'b1), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DLATCH_NP0_ (input D, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("LATCH"), .REGSET("RESET"), .SRMUX("SR"),  .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(E), .ce(1'b1), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule
module  \$_DLATCH_NP1_ (input D, R, E, output Q); AL_MAP_SEQ #(.DFFMODE("LATCH"), .REGSET("SET"), .SRMUX("SR"), . SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(E), .ce(1'b1), .sr(R)); wire _TECHMAP_REMOVEINIT_Q_ = 1'b1; endmodule

`ifndef NO_LUT
module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  (* force_downto *)
  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      AL_MAP_LUT1 #(.EQN(""),.INIT(LUT)) _TECHMAP_REPLACE_ (.o(Y), .a(A[0]));
    end else
    if (WIDTH == 2) begin
      AL_MAP_LUT2 #(.EQN(""),.INIT(LUT)) _TECHMAP_REPLACE_ (.o(Y), .a(A[0]), .b(A[1]));
    end else
    if (WIDTH == 3) begin
      AL_MAP_LUT3 #(.EQN(""),.INIT(LUT)) _TECHMAP_REPLACE_ (.o(Y), .a(A[0]), .b(A[1]), .c(A[2]));
    end else
    if (WIDTH == 4) begin
      AL_MAP_LUT4 #(.EQN(""),.INIT(LUT)) _TECHMAP_REPLACE_ (.o(Y), .a(A[0]), .b(A[1]), .c(A[2]), .d(A[3]));
    end else
    if (WIDTH == 5) begin
      AL_MAP_LUT5 #(.EQN(""),.INIT(LUT)) _TECHMAP_REPLACE_ (.o(Y), .a(A[0]), .b(A[1]), .c(A[2]), .d(A[3]), .e(A[4]));
    end else
    if (WIDTH == 6) begin
      AL_MAP_LUT6 #(.EQN(""),.INIT(LUT)) _TECHMAP_REPLACE_ (.o(Y), .a(A[0]), .b(A[1]), .c(A[2]), .d(A[3]), .e(A[4]), .f(A[5]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
`endif
