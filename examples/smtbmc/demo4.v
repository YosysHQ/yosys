// Demo for "final" smtc constraints

module demo4(input clk, rst, inv2, input [15:0] in, output reg [15:0] r1, r2);
	always @(posedge clk) begin
		if (rst) begin
			r1 <= in;
			r2 <= -in;
		end else begin
			r1 <= r1 + in;
			r2 <= inv2 ? -(r2 - in) : (r2 - in);
		end
	end
endmodule
