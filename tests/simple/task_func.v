
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

module task_func_test03(input [7:0] din_a, input [7:0] din_b, output [7:0] dout_a);
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

// -------------------------------------------------------------------

module task_func_test04(input [7:0] in, output [7:0] out1, out2, out3, out4);
	parameter p = 23;
	parameter px = 42;
	function [7:0] test1;
		input [7:0] i;
		parameter p = 42;
		begin
			test1 = i + p;
		end
	endfunction
	function [7:0] test2;
		input [7:0] i;
		parameter p2 = p+42;
		begin
			test2 = i + p2;
		end
	endfunction
	function [7:0] test3;
		input [7:0] i;
		begin
			test3 = i + p;
		end
	endfunction
	function [7:0] test4;
		input [7:0] i;
		parameter px = p + 13;
		parameter p3 = px - 37;
		parameter p4 = p3 ^ px;
		begin
			test4 = i + p4;
		end
	endfunction
	assign out1 = test1(in);
	assign out2 = test2(in);
	assign out3 = test3(in);
	assign out4 = test4(in);
endmodule
