module abc9_test032(input clk, d, r, output reg q);
initial q = 1'b0;
always @(negedge clk or negedge r)
    if (!r) q <= 1'b0;
    else q <= d;
endmodule
