`timescale 1ns / 1ps

module testbench;
	reg clk = 0, d = 0;
	wire q;

	SLE uut (
		.Q(q),
		.ADn(1'b1),
		.ALn(1'b1),
		.CLK(clk),
		.D(d),
		.LAT(1'b0),
		.SD(1'b0),
		.EN(1'b1),
		.SLn(1'b1)
	);

	initial begin
		#1 clk = 1;
		#1 d = 1;
		#1;
		if (q !== 1'b0) begin
			$display("ERROR: q=%b after D changed while CLK was high, expected 0", q);
			$stop;
		end
		$display("All tests passed.");
		$finish;
	end
endmodule
