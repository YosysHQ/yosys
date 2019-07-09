`define MAXQ 2
module uut (
	input clk,
	input d, r, e,
	output [`MAXQ:0] q
);
	reg q0;
	always @(posedge clk) begin
		if (r)
			q0 <= 0;
		else if (e)
			q0 <= d;
	end

	reg q1;
	always @(posedge clk, posedge r) begin
		if (r)
			q1 <= 0;
		else if (e)
			q1 <= d;
	end

	reg q2;
	always @(posedge clk, negedge r) begin
		if (!r)
			q2 <= 0;
		else if (!e)
			q2 <= d;
	end

	assign q = {q2, q1, q0};
endmodule

`ifdef TESTBENCH
module \$ff #(
	parameter integer WIDTH = 1
) (
	input [WIDTH-1:0] D,
	output reg [WIDTH-1:0] Q
);
	wire sysclk = testbench.sysclk;
	always @(posedge sysclk)
		Q <= D;
endmodule

module testbench;
	reg sysclk;
	always #5 sysclk = (sysclk === 1'b0);

	reg clk;
	always @(posedge sysclk) clk = (clk === 1'b0);

	reg d, r, e;

	wire [`MAXQ:0] q_uut;
	uut uut (.clk(clk), .d(d), .r(r), .e(e), .q(q_uut));

	wire [`MAXQ:0] q_syn;
	syn syn (.clk(clk), .d(d), .r(r), .e(e), .q(q_syn));

	wire [`MAXQ:0] q_prp;
	prp prp (.clk(clk), .d(d), .r(r), .e(e), .q(q_prp));

	wire [`MAXQ:0] q_a2s;
	a2s a2s (.clk(clk), .d(d), .r(r), .e(e), .q(q_a2s));

	wire [`MAXQ:0] q_ffl;
	ffl ffl (.clk(clk), .d(d), .r(r), .e(e), .q(q_ffl));

	task printq;
		reg [5*8-1:0] msg;
		begin
			msg = "OK";
			if (q_uut !== q_syn) msg = "SYN";
			if (q_uut !== q_prp) msg = "PRP";
			if (q_uut !== q_a2s) msg = "A2S";
			if (q_uut !== q_ffl) msg = "FFL";
			$display("%6t %b %b %b %b %b %s", $time, q_uut, q_syn, q_prp, q_a2s, q_ffl, msg);
			if (msg != "OK") $finish;
		end
	endtask

	initial if(0) begin
		$dumpfile("async.vcd");
		$dumpvars(0, testbench);
	end

	initial begin
		@(posedge clk);
		d <= 0;
		r <= 0;
		e <= 0;
		@(posedge clk);
		e <= 1;
		@(posedge clk);
		e <= 0;
		repeat (10000) begin
			@(posedge clk);
			printq;
			d <= $random;
			r <= $random;
			e <= $random;
		end
		$display("PASS");
		$finish;
	end
endmodule
`endif
