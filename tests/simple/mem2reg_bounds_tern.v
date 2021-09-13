module top(
    input clk,
    input wire [1:0] sel,
    input wire [7:0] base,
    output reg [7:0] line
);
    reg [0:7] mem [0:2];

    generate
        genvar i;
        for (i = 0; i < 4; i = i + 1) begin : gen
            always @(posedge clk)
                mem[i] <= i == 0 ? base : mem[i - 1] + 1;
        end
    endgenerate

    always @(posedge clk)
        line = mem[sel];
endmodule
