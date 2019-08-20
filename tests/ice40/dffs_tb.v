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
    wire doutB,doutB1,doutB2,doutB3,doutB4;
	reg dff,ndff,adff,adffn,dffe = 0;

    top uut (
        .clk (clk ),
        .a (dinA[0] ),
        .pre (dinA[1] ),
        .clr (dinA[2] ),
        .b (doutB ),
        .b1 (doutB1 ),
        .b2 (doutB2 ),
        .b3 (doutB3 ),
        .b4 (doutB4 )
    );
    
    always @(posedge clk) begin
    #3;
    dinA <= dinA + 1;
    end
	
	always @( posedge clk, posedge dinA[1], posedge dinA[2] )
		if ( dinA[2] )
			dff <= 1'b0;
		else if ( dinA[1] )
			dff <= 1'b1;
		else
            dff <= dinA[0];
    
    always @( negedge clk, negedge dinA[1], negedge dinA[2] )
		if ( !dinA[2] )
			ndff <= 1'b0;
		else if ( !dinA[1] )
			ndff <= 1'b1;
		else
            ndff <= dinA[0];
            
    always @( posedge clk, posedge dinA[2] )
		if ( dinA[2] )
			adff <= 1'b0;
		else
            adff <= dinA[0];
            
    always @( posedge clk, negedge dinA[2] )
		if ( !dinA[2] )
			adffn <= 1'b0;
		else
            adffn <= dinA[0];

    always @( posedge clk )
		if ( dinA[2] )
            dffe <= dinA[0];
            
	assert_dff dff_test(.clk(clk), .test(doutB), .pat(dff));
    assert_dff ndff_test(.clk(clk), .test(doutB1), .pat(ndff));
    assert_dff adff_test(.clk(clk), .test(doutB2), .pat(adff));    
    assert_dff adffn_test(.clk(clk), .test(doutB3), .pat(adffn));
    assert_dff dffe_test(.clk(clk), .test(doutB4), .pat(dffe));
    
endmodule
