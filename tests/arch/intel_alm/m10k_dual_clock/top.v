module top #(
    parameter WIDTH = 10,
    parameter ABITS = 6
) (
    input wr_clk, rd_clk, wr_en, rd_en,
    input [ABITS-1:0] wr_addr, rd_addr,
    input [WIDTH-1:0] wr_data,
    output reg [WIDTH-1:0] rd_data
);
    (* ramstyle = "M10K" *) reg [WIDTH-1:0] mem [0:(1 << ABITS)-1];
    integer i;
    initial
        for (i = 0; i < (1 << ABITS); i = i + 1)
            mem[i] = (i * 73) ^ 166;
    always @(posedge wr_clk)
        if (wr_en)
            mem[wr_addr] <= wr_data;
    always @(posedge rd_clk)
        if (rd_en)
            rd_data <= mem[rd_addr];
endmodule
