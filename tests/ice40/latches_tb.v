module testbench;
    reg clk;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end


    reg [2:0] dinA = 0;
    wire doutB,doutB1,doutB2;
	reg lat,latn,latsr = 0;

    top uut (
        .clk (clk ),
        .a (dinA[0] ),
        .pre (dinA[1] ),
        .clr (dinA[2] ),
        .b (doutB ),
        .b1 (doutB1 ),
        .b2 (doutB2 )
    );

    always @(posedge clk) begin
    #3;
    dinA <= dinA + 1;
    end

    	always @*
		if ( clk )
			lat <= dinA[0];


    	always @*
		if ( !clk )
			latn <= dinA[0];


		always @*
		if ( dinA[2] )
			latsr <= 1'b0;
		else if ( dinA[1] )
			latsr <= 1'b1;
		else if ( clk )
			latsr <= dinA[0];

	assert_dff lat_test(.clk(clk), .test(doutB), .pat(lat));
    assert_dff latn_test(.clk(clk), .test(doutB1), .pat(latn));
    assert_dff latsr_test(.clk(clk), .test(doutB2), .pat(latsr));

endmodule
