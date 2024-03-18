module \$add (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

generate
  if ((A_WIDTH == 32) && (B_WIDTH == 32))
    begin
      wire [16:0] S1 = A[15:0] + B[15:0];
      wire [15:0] S2 = A[31:16] + B[31:16] + S1[16];
      assign Y = {S2[15:0], S1[15:0]};
    end
  else
    wire _TECHMAP_FAIL_ = 1;
endgenerate

endmodule
