module axis_master(aclk, aresetn, tvalid, tready, tdata);
    input aclk, aresetn, tready;
    output reg tvalid;
    output reg [7:0] tdata;

    reg [31:0] state;
    always @(posedge aclk) begin
        if (!aresetn) begin
	    state <= 314159265;
	    tvalid <= 0;
	    tdata <= 'bx;
	end else begin
	    if (tvalid && tready)
	    	tvalid <= 0;
	    if (!tvalid || !tready) begin
	    //             ^- should not be inverted!
                state = state ^ state << 13;
                state = state ^ state >> 7;
                state = state ^ state << 17;
		if (state[9:8] == 0) begin
		    tvalid <= 1;
		    tdata <= state;
		end
	    end
	end
    end
endmodule
