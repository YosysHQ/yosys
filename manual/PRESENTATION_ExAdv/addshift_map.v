module \$add (A, B, Y);
  parameter A_SIGNED = 0;
  parameter B_SIGNED = 0;
  parameter A_WIDTH = 1;
  parameter B_WIDTH = 1;
  parameter Y_WIDTH = 1;

  input [A_WIDTH-1:0] A;
  input [B_WIDTH-1:0] B;
  output [Y_WIDTH-1:0] Y;

  parameter _TECHMAP_BITS_CONNMAP_ = 0;
  parameter _TECHMAP_CONNMAP_A_ = 0;
  parameter _TECHMAP_CONNMAP_B_ = 0;

  wire _TECHMAP_FAIL_ = A_WIDTH != B_WIDTH || B_WIDTH < Y_WIDTH ||
                        _TECHMAP_CONNMAP_A_ != _TECHMAP_CONNMAP_B_;

  assign Y = A << 1;
endmodule
