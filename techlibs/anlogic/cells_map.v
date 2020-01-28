module  \$_DFF_N_ (input D, C, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'bx), .SRMUX("SR"), .SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .ce(1'b1), .sr(1'b0)); endmodule
module  \$_DFF_P_ (input D, C, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'bx), .SRMUX("SR"), .SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C),  .ce(1'b1), .sr(1'b0)); endmodule

module  \$_DFFE_NN_ (input D, C, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'bx), .SRMUX("SR"), .SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .ce(E), .sr(1'b0)); endmodule
module  \$_DFFE_NP_ (input D, C, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'bx), .SRMUX("SR"), .SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .ce(E), .sr(1'b0)); endmodule
module  \$_DFFE_PN_ (input D, C, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'bx), .SRMUX("SR"), .SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C),  .ce(E), .sr(1'b0)); endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'bx), .SRMUX("SR"), .SRMODE("SYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C),  .ce(E), .sr(1'b0)); endmodule

module  \$_DFF_NN0_ (input D, C, R, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'b0), .SRMUX("INV"), .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .ce(1'b1), .sr(R)); endmodule
module  \$_DFF_NN1_ (input D, C, R, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'b1), .SRMUX("INV"), .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .ce(1'b1), .sr(R)); endmodule
module  \$_DFF_NP0_ (input D, C, R, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'b0), .SRMUX("SR"),  .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .ce(1'b1), .sr(R)); endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'b1), .SRMUX("SR"),  .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .ce(1'b1), .sr(R)); endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'b0), .SRMUX("INV"), .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C) , .ce(1'b1), .sr(R)); endmodule
module  \$_DFF_PN1_ (input D, C, R, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'b1), .SRMUX("INV"), .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C),  .ce(1'b1), .sr(R)); endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'b0), .SRMUX("SR"),  .SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C),  .ce(1'b1), .sr(R)); endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); AL_MAP_SEQ #(.DFFMODE("FF"), .REGSET(1'b1), .SRMUX("SR"), . SRMODE("ASYNC")) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C),  .ce(1'b1), .sr(R)); endmodule

module \$_DLATCH_N_ (E, D, Q);
  wire [1023:0] _TECHMAP_DO_ = "simplemap; opt";
  input E, D;
  output Q = !E ? D : Q;
endmodule

module \$_DLATCH_P_ (E, D, Q);
  wire [1023:0] _TECHMAP_DO_ = "simplemap; opt";
  input E, D;
  output Q = E ? D : Q;
endmodule

`ifndef NO_LUT
module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

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
