// https://github.com/YosysHQ/yosys/issues/5906
module mac_add_u (input [8:0] a, b, input [17:0] c, output [17:0] y);
	assign y = a*b + c;
endmodule

module mac_add_s (input signed [8:0] a, b, input signed [17:0] c, output signed [17:0] y);
	assign y = a*b + c;
endmodule

module mac_sub_u (input [8:0] a, b, input [17:0] c, output [17:0] y);
	assign y = c - a*b;
endmodule

module mac_sub_s (input signed [8:0] a, b, input signed [17:0] c, output signed [17:0] y);
	assign y = c - a*b;
endmodule

module mac_subrev_u (input [8:0] a, b, input [17:0] c, output [17:0] y);
	assign y = a*b - c;
endmodule

module mac_wide_s (input signed [8:0] a, b, input signed [17:0] c, output signed [29:0] y);
	assign y = c - a*b;
endmodule

// https://github.com/YosysHQ/yosys/issues/5929
module mul_pipe_u (input clk, input [8:0] a, b, output reg [17:0] y);
	reg [8:0] a_r;
	reg [8:0] b_r;
	always @(posedge clk) begin 
		a_r <= a;
		b_r <= b;
		y <= a_r * b_r;
	end
endmodule

module mul_pipe_s (input clk, input signed [8:0] a, b, output reg signed [17:0] y);
	reg signed [8:0] a_r;
	reg signed [8:0] b_r;
	always @(posedge clk) begin
		a_r <= a;
		b_r <= b;
		y <= a_r * b_r;
	end
endmodule
