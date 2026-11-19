`timescale 1ns/1ns
module tb_sdffe();
	reg clk = 0;
	reg rst = 1;
	reg d = 1;
	reg en = 0;
	wire q;

	sdffe uut(.clk(clk),.d(d),.rst(rst),.en(en),.q(q));

	// wait for q to update before checking correctness
	task check;
		input integer test_id;
		input expected_q;
		begin
			#1;
			if (q !== expected_q)
				$fatal(1, "test %0d: expected Q=%b, actual=%b",
				       test_id, expected_q, q);
			$display("pass test %0d: Q=%b", test_id, q);
		end
	endtask

	initial
	begin
		//save the waveform
		$dumpfile("tb_sdffe");
		$dumpvars(0,tb_sdffe);

		// control clk manually to test signalchanges

		// test 1 at 5 ns: rising edge at clk, reset=1, enable=0, CE=reset|enable=1, CE_latched=1 since clk=0 latched CE=1, rising clk to 1 closed the latch and the latched CE stays 1, GClk is not blcoked by CE_latched at this time
                // so rising edge is recorded on GCLK, but reset has priority and it equals to 1, so the q should be reset to 0 (expeced q = 0)
                // test q can be reset even if enable=0
		#5;
		clk = 1;
		check(1, 0);

		// test 2 at 11 ns: rising edge at clk, reset=0, enable=1, D=1, CE=1,CE_latched=1 (since clk=0 latched CE=1), GClk=0->1 (since CE_latched=1 not blocking clk), rising edge at GCLK and enable=1 with reset=0, d should be updated to q
                //(expeced q =1)
                // test q can be updated normally
		clk = 0;
		rst = 0;
		en = 1;
		d = 1;
		#5;
		clk = 1;
		check(2, 1);

		// test 3 at 17 ns: rising edge at clk, reset=0, enable=0, D=0, CE=0, CE_latched=0 (since when clk=0 CE=0 is latched), GCLK=CE_latched&clk=0 (CE_latched blocks clk's rising edge), therefore there is no rising edge on GCLK, d should not
                // be updated to q (expected q=1)
                // test if the clk is blocked when enable and reset=0
		clk = 0;
		en = 0;
		d = 0;
		#5;
		clk = 1;
		check(3, 1);

		// test 4 at 18 ns: clk=1, reset=0,enable=0->1, D=0, CE=0->1, CE_latched=0 (since when clk=1 CE is not latched and remains 0), so GCLK is still blocked, d=0 is still not updated to q (expected q=1)
                // test accidentally changes enable wont create a rising edge on GCLK and update q, updates needs to wait for the next rising edge
		en = 1;
		check(4, 1);

		// test 5 at 19 ns: clk=1 reset=1 enable=0, D=0, CE=1, CE_latched=0 (since when clk=1 CE is not latched and remains 0), so GCLK is still blocked, q wont be reset until there is a rising edge on GCLK (expeced q=1)
                // test accidentally changes reset won create a rising edge on GCLK and reset q, synchronous reset needs to wait for the next rising edge
		en = 0;
		rst = 1;
		check(5, 1);

		// test 6 at 25 ns: rising edge at clk, reset=1,enable=0, CE=1, CE_latched=1 (since when clk=0 CE is latched and = 1), so GCLK is not blocked, rising edge passes through, so reset happens. (expected q=0)
                // test synchronous reset reset with rising edge
		clk = 0;
		#5;
		clk = 1;
		check(6, 0);

		// Test 7 at 31 ns: rising edge at clk, reset=0,enable=0, CE=0,CE_latched=0(since when clk=0,ce is latched and = 0), so GCLK is blcoked and the rising edge on clk wont produce a rising edge on GCLK, and there wont
                // be any update on q (expect q = 0)
                rst=0;
                clk=0;
		d = 1;
		#5;
		clk = 1;
		check(7, 0);

		// Test 8 at 37 ns: clk=0, reset=0,enable=1, CE=1, CE_latched=1 (since when clk=0, ce is latched and = 1), so GCLK is not blocked and the rising edge on clk will produce a rising edge on GCLK, and there will
                // be a update on q (expect q =1)
		clk = 0;
		en = 1;
		#5;
		clk = 1;
		check(8, 1);

		$display("pass all 8 SDFFE functional tests");
		$finish;
	end
endmodule
