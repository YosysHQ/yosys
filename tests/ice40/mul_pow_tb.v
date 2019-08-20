module testbench;
    reg [7:0] in;

	wire [3:0] outA,outB;
	wire [3:0] poutA,poutB;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 in = 0;
        repeat (10000) begin
            #5 in = in + 1;
        end

        $display("OKAY");
    end

    top uut (
	.x(in[3:0]),
	.y(in[7:4]),
	.A(outA),
	.B(outB)
	);


	assign poutA =  in[3:0] * in[7:4];
	assign poutB =  in[3:0] ** in[7:4];

	check_comb mul_test(outA, poutA);
	check_comb pow_test(outB, poutB);
	assert_comb pow2_test(outB[2], poutB[2]);

endmodule

module check_comb(input [3:0] test, input [3:0] pat);
    always @*
    begin
        #1;
        if (test !== pat)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",test," ",pat);
            $stop;
        end
    end
endmodule

