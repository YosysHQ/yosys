module test(input      CLK, ADDR,
            input      [7:0] DIN,
	    output reg [7:0] DOUT);
    reg [7:0] mem [0:1];
    always @(posedge CLK) begin
        mem[ADDR] <= DIN;
	DOUT <= mem[ADDR];
    end
endmodule
