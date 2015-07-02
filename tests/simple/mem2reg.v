
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

module mem2reg_test2(clk, mode, addr, data);

input clk, mode;
input [2:0] addr;
output [3:0] data;

(* mem2reg *)
reg [3:0] mem [0:7];

assign data = mem[addr];

integer i;

always @(posedge clk) begin
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

