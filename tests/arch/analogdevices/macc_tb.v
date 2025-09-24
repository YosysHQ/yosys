`timescale 1ns / 1ps

module testbench;

    parameter SIZEIN = 16, SIZEOUT = 40;
	reg clk, ce, rst;
   	reg signed [SIZEIN-1:0] a, b;
	output signed [SIZEOUT-1:0] REF_accum_out, accum_out;
	output REF_overflow, overflow;

	integer errcount = 0;

	reg ERROR_FLAG = 0;

	task clkcycle;
		begin
			#5;
			clk = ~clk;
			#10;
			clk = ~clk;
			#2;
			ERROR_FLAG = 0;
			if (REF_accum_out !== accum_out) begin
				$display("ERROR at %1t: REF_accum_out=%b UUT_accum_out=%b DIFF=%b", $time, REF_accum_out, accum_out, REF_accum_out ^ accum_out);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			if (REF_overflow !== overflow) begin
				$display("ERROR at %1t: REF_overflow=%b UUT_overflow=%b DIFF=%b", $time, REF_overflow, overflow, REF_overflow ^ overflow);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			#3;
		end
	endtask

	initial begin
		//$dumpfile("test_macc.vcd");
		//$dumpvars(0, testbench);

		#2;
		clk = 1'b0;
        ce = 1'b0;
        a = 0;
        b = 0;

        rst = 1'b1;
		repeat (10) begin
			#10;
			clk = 1'b1;
			#10;
			clk = 1'b0;
			#10;
			clk = 1'b1;
			#10;
			clk = 1'b0;
		end
		rst = 1'b0;

		repeat (10000) begin
			clkcycle;
            ce = 1; //$urandom & $urandom;
			//rst = $urandom & $urandom & $urandom & $urandom & $urandom & $urandom;
			a = $urandom & ~(1 << (SIZEIN-1));
			b = $urandom & ~(1 << (SIZEIN-1));
		end

		if (errcount == 0) begin
			$display("All tests passed.");
			$finish;
		end else begin
			$display("Caught %1d errors.", errcount);
			$stop;
		end
	end

	macc2 ref (
        .clk(clk),
        .ce(ce),
        .rst(rst),
        .a(a),
        .b(b),
        .accum_out(REF_accum_out),
        .overflow(REF_overflow)
	);

	macc2_uut uut (
        .clk(clk),
        .ce(ce),
        .rst(rst),
        .a(a),
        .b(b),
        .accum_out(accum_out),
        .overflow(overflow)
	);
endmodule
