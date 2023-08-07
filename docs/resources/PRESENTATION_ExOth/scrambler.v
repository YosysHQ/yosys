module scrambler(
        input clk, rst, in_bit,
        output reg out_bit
);
    reg [31:0] xs;
    always @(posedge clk) begin
    	if (rst)
	    xs = 1;
        xs = xs ^ (xs << 13);
        xs = xs ^ (xs >> 17);
        xs = xs ^ (xs << 5);
        out_bit <= in_bit ^ xs[0];
    end
endmodule
