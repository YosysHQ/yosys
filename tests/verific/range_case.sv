module top(input clk, input signed [3:0] sel_w , output reg out);

always @ (posedge clk)
begin
    case (sel_w) inside
        [-4:3] : out <= 1'b1;
        [4:5] : out <= 1'b0;
    endcase
end

endmodule
