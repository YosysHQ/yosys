module top(
    input clk,
    input rst,
    input [2:0] a,
    output [1:0] b
);
    reg [2:0] b_reg;
    initial begin
        b_reg <= 3'b0;
    end

    assign b = b_reg[1:0];
    always @(posedge clk or posedge rst) begin
        if(rst) begin
            b_reg <= 3'b0;
        end else begin
            b_reg <= a;
        end
    end
endmodule

