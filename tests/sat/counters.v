
module counter1(clk, rst, ping);
	input clk, rst;
	output ping;
	reg [31:0] count;

	always @(posedge clk) begin
		if (rst)
			count <= 0;
		else
			count <= count + 1;
	end

	assign ping = &count;
endmodule

module counter2(clk, rst, ping);
	input clk, rst;
	output ping;
	reg [31:0] count;

	integer i;
	reg carry;

	always @(posedge clk) begin
		carry = 1;
		for (i = 0; i < 32; i = i+1) begin
			count[i] <= !rst & (count[i] ^ carry);
			carry = count[i] & carry;
		end
	end

	assign ping = &count;
endmodule

