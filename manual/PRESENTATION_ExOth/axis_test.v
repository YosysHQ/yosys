module axis_test(aclk, tready);
    input aclk, tready;
    wire aresetn, tvalid;
    wire [7:0] tdata;

    integer counter = 0;
    reg aresetn = 0;

    axis_master uut (aclk, aresetn, tvalid, tready, tdata);

    always @(posedge aclk) begin
    	if (aresetn && tready && tvalid) begin
	    if (counter == 0) assert(tdata ==  19);
	    if (counter == 1) assert(tdata ==  99);
	    if (counter == 2) assert(tdata ==   1);
	    if (counter == 3) assert(tdata == 244);
	    if (counter == 4) assert(tdata == 133);
	    if (counter == 5) assert(tdata == 209);
	    if (counter == 6) assert(tdata == 241);
	    if (counter == 7) assert(tdata == 137);
	    if (counter == 8) assert(tdata == 176);
	    if (counter == 9) assert(tdata ==   6);
	    counter <= counter + 1;
	end
	aresetn <= 1;
    end
endmodule
