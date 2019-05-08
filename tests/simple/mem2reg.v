
module mem2reg_test1(in_addr, in_data, out_addr, out_data);

input [1:0] in_addr, out_addr;
input [3:0] in_data;
output reg [3:0] out_data;

reg [3:0] array [2:0];

always @* begin
	array[0] = 0;
	array[1] = 23;
	array[2] = 42;
	array[in_addr] = in_data;
	out_data = array[out_addr];
end

endmodule

// ------------------------------------------------------

module mem2reg_test2(clk, reset, mode, addr, data);

input clk, reset, mode;
input [2:0] addr;
output [3:0] data;

(* mem2reg *)
reg [3:0] mem [0:7];

assign data = mem[addr];

integer i;

always @(posedge clk) begin
	if (reset) begin
		for (i=0; i<8; i=i+1)
			mem[i] <= i;
	end else
	if (mode) begin
		for (i=0; i<8; i=i+1)
			mem[i] <= mem[i]+1;
	end else begin
		mem[addr] <= 0;
	end
end

endmodule

// ------------------------------------------------------

// http://www.reddit.com/r/yosys/comments/28d9lx/problem_with_concatenation_of_two_dimensional/
module mem2reg_test3( input clk, input [8:0] din_a, output reg [7:0] dout_a, output [7:0] dout_b);
reg [7:0] dint_c [0:7];
always @(posedge clk)
  begin
      {dout_a[0], dint_c[3]} <= din_a;
  end
assign dout_b = dint_c[3];
endmodule

// ------------------------------------------------------

module mem2reg_test4(result1, result2, result3);
	output signed [9:0] result1;
	output signed [9:0] result2;
	output signed [9:0] result3;

	wire signed [9:0] intermediate [0:3];

	function integer depth2Index;
		input integer depth;
		depth2Index = depth;
	endfunction

	assign intermediate[depth2Index(1)] = 1;
	assign intermediate[depth2Index(2)] = 2;
	assign intermediate[3] = 3;
	assign result1 = intermediate[1];
	assign result2 = intermediate[depth2Index(2)];
	assign result3 = intermediate[depth2Index(3)];
endmodule

// ------------------------------------------------------

module mem2reg_test5(input ctrl, output out);
	wire [0:0] foo[0:0];
	wire [0:0] bar[0:1];

	assign foo[0] = ctrl;
	assign bar[0] = 0, bar[1] = 1;
	assign out = bar[foo[0]];
endmodule

// ------------------------------------------------------

module mem2reg_test6 (din, dout);
        input   wire    [3:0] din;
        output  reg     [3:0] dout;

        reg [1:0] din_array  [1:0];
        reg [1:0] dout_array [1:0];

        always @* begin
		din_array[0] = din[0 +: 2];
		din_array[1] = din[2 +: 2];

		dout_array[0] = din_array[0];
		dout_array[1] = din_array[1];

		{dout_array[0][1], dout_array[0][0]} = dout_array[0][0] + dout_array[1][0];

		dout[0 +: 2] = dout_array[0];
		dout[2 +: 2] = dout_array[1];
        end
endmodule
