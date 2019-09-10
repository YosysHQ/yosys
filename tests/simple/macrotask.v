
macromodule task_func_test01_impl();
reg [7:0] x, y, z, w;

function [7:0] sum_shift;
input [3:0] s1, s2, s3;
sum_shift = s1 + (s2 << 2) + (s3 << 4);
endfunction

task reset_w;
w = 0;
endtask

task add_to;
output [7:0] out;
input [7:0] in;
out = out + in;
endtask

task cycle;
input [7:0] a, b, c;
output [7:0] ret_x, ret_y, ret_z, ret_w;
begin
	x = sum_shift(a, b, c);
	y = sum_shift(a[7:4], b[5:2], c[3:0]);
	z = sum_shift(a[0], b[5:4], c >> 5) ^ sum_shift(1, 2, 3);

	reset_w;
	add_to(w, x);
	add_to(w, y);
	add_to(w, z);
  ret_x = x;
  ret_y = y;
  ret_z = z;
  ret_w = w;
end
endtask

endmodule

module task_func_test01(clk, a, b, c, x, y, z, w);
input clk;
input [7:0] a, b, c;
output reg [7:0] x, y, z, w;
task_func_test01_impl impl();
always @(posedge clk) begin
	impl.cycle(a, b, c, x, y, z, w);
end
endmodule

// -------------------------------------------------------------------

macromodule task_func_test05_impl(data_in,data_out);
	input data_in;
	output reg data_out;

	task myTask;
		data_out = data_in;
	endtask
endmodule

module task_func_test05(data_in,data_out,clk);
	input data_in;
	output data_out;
	input clk;
  task_func_test05_impl impl(data_in, data_out);
	always @(posedge clk) begin
		impl.myTask();
	end
endmodule
