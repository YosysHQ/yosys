
module task_func_test01(clk, a, b, c, x, y, z, w);

input clk;
input [7:0] a, b, c;
output reg [7:0] x, y, z, w;

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

always @(posedge clk) begin
	x = sum_shift(a, b, c);
	y = sum_shift(a[7:4], b[5:2], c[3:0]);
	z = sum_shift(a[0], b[5:4], c >> 5) ^ sum_shift(1, 2, 3);

	reset_w;
	add_to(w, x);
	add_to(w, y);
	add_to(w, z);
end

endmodule

// -------------------------------------------------------------------

module task_func_test02(clk, a, b, c, x, y, z, w);

input clk;
input [7:0] a, b, c;
output reg [7:0] x, y, z, w;

function [7:0] sum_shift(input [3:0] s1, s2, s3);
sum_shift = s1 + (s2 << 2) + (s3 << 4);
endfunction

task reset_w;
w = 0;
endtask

task add_to(output [7:0] out, input [7:0] in);
out = out + in;
endtask

always @(posedge clk) begin
	x = sum_shift(a, b, c);
	y = sum_shift(a[7:4], b[5:2], c[3:0]);
	z = sum_shift(a[0], b[5:4], c >> 5) ^ sum_shift(1, 2, 3);

	reset_w;
	add_to(w, x);
	add_to(w, y);
	add_to(w, z);
end

endmodule

// -------------------------------------------------------------------

module task_func_test03( input [7:0] din_a, input [7:0] din_b, output [7:0] dout_a);
	assign dout_a = test(din_a,din_b);
	function [7:0] test;
		input [7:0] a;
		input [7:0] b;
		begin : TEST
			integer i;
			for (i = 0; i <= 7; i = i + 1)
				test[i] = a[i] & b[i];
		end
	endfunction
endmodule
