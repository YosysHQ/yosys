module uut_forgen02(a, b, cin, y, cout);

parameter WIDTH = 8;

input [WIDTH-1:0] a, b;
input cin;

output [WIDTH-1:0] y;
output cout;

genvar i;
wire [WIDTH-1:0] carry;

generate
	for (i = 0; i < WIDTH; i=i+1) begin:adder
		wire [2:0] D;
		assign D[1:0] = { a[i], b[i] };
		if (i == 0) begin:chain
			assign D[2] = cin;
		end else begin:chain
			assign D[2] = carry[i-1];
		end
		assign y[i] = ^D;
		assign carry[i] = &D[1:0] | (^D[1:0] & D[2]);
	end
endgenerate

assign cout = carry[WIDTH-1];

endmodule
