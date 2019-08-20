module testbench;
    reg en;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 en = 0;
        repeat (10000) begin
            #5 en = 1;
            #5 en = 0;
        end

        $display("OKAY");    
    end
   
    
    reg dinA = 0;
    wire doutB;

    top uut (
        .en (en ),
        .a (dinA ),
        .b (doutB )
    );
    
    always @(posedge en) begin
    #3;
    dinA <= !dinA;
    end
	
	assert_tri b_test(.en(en), .A(dinA), .B(doutB));
  
endmodule
