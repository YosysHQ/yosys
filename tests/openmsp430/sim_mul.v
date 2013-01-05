
module \$mul (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 0;
parameter B_WIDTH = 0;
parameter Y_WIDTH = 0;

input [A_WIDTH-1:0] A;
generate if (A_SIGNED) begin:A_BUF
	wire signed [A_WIDTH-1:0] val = A;
end else begin:A_BUF
	wire [A_WIDTH-1:0] val = A;
end endgenerate

input [B_WIDTH-1:0] B;
generate if (B_SIGNED) begin:B_BUF
	wire signed [B_WIDTH-1:0] val = B;
end else begin:B_BUF
	wire [B_WIDTH-1:0] val = B;
end endgenerate

output [Y_WIDTH-1:0] Y;

assign Y = A_BUF.val * B_BUF.val;

endmodule

