module test1(in_addr, in_data, out_addr, out_data);

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
