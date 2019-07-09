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
module testbench;
	reg clk;
	always #5 clk = (clk === 1'b0);

	reg d, r, e;

	wire [`MAXQ:0] q_uut;
	uut uut (.clk(clk), .d(d), .r(r), .e(e), .q(q_uut));

	wire [`MAXQ:0] q_syn;
	syn syn (.clk(clk), .d(d), .r(r), .e(e), .q(q_syn));

	task printq;
		reg [5*8-1:0] msg;
		begin
			msg = "OK";
			if (q_uut != q_syn) msg = "SYN";
			$display("%6t %b %b %s", $time, q_uut, q_syn, msg);
			if (msg != "OK") $stop;
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
		$display("OK");
		$finish;
	end
endmodule
`endif
