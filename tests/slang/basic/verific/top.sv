module top(input clk, a, en);
    reg a_q = '0;
    reg en_q = '0;

    always @(posedge clk) begin
        a_q <= a;
        en_q <= en;
    end
endmodule
