// coverage for repeat loops outside of constant functions

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
		i = 0;
		repeat (32) begin
			count[i] <= !rst & (count[i] ^ carry);
			carry = count[i] & carry;
			i = i+1;
		end
	end

	assign ping = &count;
endmodule

