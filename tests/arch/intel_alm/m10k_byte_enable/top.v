module top #(
    parameter ABITS = 9
) (
    input wr_clk, rd_clk, wr_en,
    input [1:0] wr_be,
    input rd_en,
    input [ABITS-1:0] wr_addr, rd_addr,
    input [19:0] wr_data,
    output reg [19:0] rd_data
);
    (* ramstyle = "M10K" *) reg [19:0] mem [0:(1 << ABITS)-1];
    integer i;
    initial
        for (i = 0; i < (1 << ABITS); i = i + 1)
            mem[i] = (i * 73) ^ 20'ha6;

    always @(posedge wr_clk) begin
        if (wr_en) begin
            if (wr_be[0])
                mem[wr_addr][9:0] <= wr_data[9:0];
            if (wr_be[1])
                mem[wr_addr][19:10] <= wr_data[19:10];
        end
    end

    always @(posedge rd_clk)
        if (rd_en)
            rd_data <= mem[rd_addr];
endmodule
