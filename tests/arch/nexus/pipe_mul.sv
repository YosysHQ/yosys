// https://github.com/YosysHQ/yosys/issues/5917

module mul18_pipe(
	input  logic clk,
	input  logic [17:0] a,
	input  logic [17:0] b,
	output logic [35:0] y
);
	logic [17:0] a_r;
	logic [17:0] b_r;

	always_ff @(posedge clk) begin
			a_r <= a;
			b_r <= b;
			y <= a_r * b_r;
	end
endmodule

module mul18_pipe_signed (
	input  logic clk,
	input  logic signed [17:0] a,
	input  logic signed [17:0] b,
	output logic signed [35:0] y
);
	logic signed [17:0] a_r;
	logic signed [17:0] b_r;

	always_ff @(posedge clk) begin
		a_r <= a;
		b_r <= b;
		y   <= a_r * b_r;
	end
endmodule


module mul18_pipe_in_only (
	input  logic clk,
	input  logic [17:0] a,
	input  logic [17:0] b,
	output logic [35:0] y
);
	logic [17:0] a_r;
	logic [17:0] b_r;

	always_ff @(posedge clk) begin
		a_r <= a;
		b_r <= b;
	end

	assign y = a_r * b_r;
endmodule

module mul18_pipe_out_only (
	input  logic clk,
	input  logic [17:0] a,
	input  logic [17:0] b,
	output logic [35:0] y
);
	always_ff @(posedge clk)
		y <= a * b;
endmodule

module mul18_pipe_io_rst (
	input  logic clk,
	input  logic rst,
	input  logic [17:0] a,
	input  logic [17:0] b,
	output logic [35:0] y
);
	logic [17:0] a_r;
	logic [17:0] b_r;

	always_ff @(posedge clk)
		if (rst) begin a_r <= 0; b_r <= 0; y <= 0; end
		else     begin a_r <= a; b_r <= b; y <= a_r * b_r; end
endmodule

module mul24_io (
	input  logic clk,
	input  logic [23:0] a,
	input  logic [23:0] b,
	output logic [47:0] y
);
	logic [23:0] a_r;
	logic [23:0] b_r;

	always_ff @(posedge clk) begin
		a_r <= a;
		b_r <= b;
		y   <= a_r * b_r;
	end
endmodule

module mul32_io (
	input  logic clk,
	input  logic [31:0] a,
	input  logic [31:0] b,
	output logic [63:0] y
);
	logic [31:0] a_r;
	logic [31:0] b_r;

	always_ff @(posedge clk) begin
		a_r <= a;
		b_r <= b;
		y   <= a_r * b_r;
	end
endmodule

module mul18_negedge (
	input  logic clk,
	input  logic [17:0] a,
	input  logic [17:0] b,
	output logic [35:0] y
);
	logic [17:0] a_r;
	logic [17:0] b_r;

	always_ff @(negedge clk) begin
		a_r <= a;
		b_r <= b;
		y   <= a_r * b_r;
	end
endmodule

module mul18_rst_nonzero (
	input  logic clk,
	input  logic rst,
	input  logic [17:0] a,
	input  logic [17:0] b,
	output logic [35:0] y
);
	logic [17:0] a_r;
	logic [17:0] b_r;

	always_ff @(posedge clk)
		if (rst) begin a_r <= 18'h3; b_r <= 18'h7; end
		else     begin a_r <= a; b_r <= b; end
	always_ff @(posedge clk)
		y <= a_r * b_r;
endmodule

module mul18_two_clock (
	input  logic clk0,
	input  logic clk1,
	input  logic [17:0] a,
	input  logic [17:0] b,
	output logic [35:0] y
);
	logic [17:0] a_r;
	logic [17:0] b_r;

	always_ff @(posedge clk0) a_r <= a;
	always_ff @(posedge clk1) b_r <= b;
	assign y = a_r * b_r;
endmodule