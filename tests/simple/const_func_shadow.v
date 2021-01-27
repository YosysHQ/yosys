module top(w, x, y, z);
	function [11:0] func;
		input reg [2:0] x;
		input reg [2:0] y;
		begin
			x = x * (y + 1);
			begin : foo
				reg [2:0] y;
				y = x + 1;
				begin : bar
					reg [2:0] x;
					x = y + 1;
					begin : blah
						reg [2:0] y;
						y = x + 1;
						func[2:0] = y;
					end
					func[5:3] = x;
				end
				func[8:6] = y;
			end
			func[11:9] = x;
		end
	endfunction
	output wire [func(2, 3) - 1:0] w;
	output wire [func(1, 3) - 1:0] x;
	output wire [func(3, 1) - 1:0] y;
	output wire [func(5, 2) - 1:0] z;
	assign w = 1'sb1;
	assign x = 1'sb1;
	assign y = 1'sb1;
	assign z = 1'sb1;
endmodule
