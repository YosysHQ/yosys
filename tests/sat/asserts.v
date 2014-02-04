// http://www.reddit.com/r/yosys/comments/1vljks/new_support_for_systemveriloglike_asserts/
module test(input clk, input rst, output y);
reg [2:0] state;
always @(posedge clk) begin
    if (rst || state == 3) begin
        state <= 0;
    end else begin
        assert(state < 3);
        state <= state + 1;
    end
end
assign y = state[2];
assert property (y !== 1'b1);
endmodule
