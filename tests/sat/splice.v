module test(a, b, y);

input [15:0] a, b;
output [15:0] y;

wire [7:0] ah = a[15:8], al = a[7:0];
wire [7:0] bh = b[15:8], bl = b[7:0];

wire [7:0] th = ah + bh, tl = al + bl;
wire [15:0] t = {th, tl}, k = t ^ 16'hcd;

assign y = { k[7:0], k[15:8] };

endmodule
