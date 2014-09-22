module scopes_test_01(input [3:0] k, output reg [15:0] x, y);
	function [15:0] func_01;
		input [15:0] x, y;
		begin
			func_01 = x + y;
			begin:blk
				reg [15:0] x;
				x = y;
				func_01 = func_01 ^ x;
			end
			func_01 = func_01 ^ x;
		end
	endfunction

	function [15:0] func_02;
		input [15:0] x, y;
		begin
			func_02 = x - y;
			begin:blk
				reg [15:0] func_02;
				func_02 = 0;
			end
		end
	endfunction

	task task_01;
		input [3:0] a;
		reg [15:0] y;
		begin
			y = a * 23;
			x = x + y;
		end
	endtask

	task task_02;
		input [3:0] a;
		begin:foo
			reg [15:0] x, z;
			x = y;
			begin:bar
				reg [15:0] x;
				x = 77 + a;
				z = -x;
			end
			y = x ^ z;
		end
	endtask

	always @* begin
		x = func_01(11, 22);
		y = func_02(33, 44);
		task_01(k);
		task_02(k);
		begin:foo
			reg [15:0] y;
			y = x;
			y = y + k;
			x = y;
		end
		x = func_01(y, x);
		y = func_02(y, x);
	end
endmodule
