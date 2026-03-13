module fir_4tap(
	input         clk,
	input  [15:0] x,
	input  [15:0] c0, c1, c2, c3,
	output reg [31:0] y
);
	reg [15:0] x1, x2, x3;
	always @(posedge clk) begin
		x1 <= x;
		x2 <= x1;
		x3 <= x2;
	end

	wire [31:0] p0 = x  * c0;
	wire [31:0] p1 = x1 * c1;
	wire [31:0] p2 = x2 * c2;
	wire [31:0] p3 = x3 * c3;

	wire [31:0] sum = p0 + p1 + p2 + p3;

	always @(posedge clk)
		y <= sum;
endmodule

