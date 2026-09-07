module legacy #(
    parameter WIDTH = 10,
    parameter ABITS = 3
) (
    input wr_clk, rd_clk, wr_en, rd_en,
    input [ABITS-1:0] wr_addr, rd_addr,
    input [WIDTH-1:0] wr_data
);
    function [(1 << ABITS)*WIDTH-1:0] initial_contents;
        integer i;
        begin
            for (i = 0; i < (1 << ABITS); i = i + 1)
                initial_contents[i*WIDTH +: WIDTH] = (i * 73) ^ 166;
        end
    endfunction
    wire [WIDTH-1:0] reference_data, primitive_data;
    top #(.WIDTH(WIDTH), .ABITS(ABITS)) reference (
        .wr_clk(wr_clk), .rd_clk(wr_clk), .wr_en(wr_en), .rd_en(rd_en),
        .wr_addr(wr_addr), .rd_addr(rd_addr), .wr_data(wr_data), .rd_data(reference_data)
    );
    // CFG_DUAL_CLOCK is deliberately omitted in both instances. Cover an
    // absent CLK2 as well as a connected CLK2 that must be ignored.
    if (WIDTH != 40) begin
        MISTRAL_M10K #(.CFG_ABITS(ABITS), .CFG_DBITS(WIDTH), .INIT(initial_contents())) ram (
            .CLK1(wr_clk), .A1ADDR(wr_addr), .A1DATA(wr_data), .A1EN(!wr_en),
            .B1ADDR(rd_addr), .B1DATA(primitive_data), .B1EN(rd_en)
        );
    end else begin
        MISTRAL_M10K #(.CFG_ABITS(ABITS), .CFG_DBITS(WIDTH), .INIT(initial_contents())) ram (
            .CLK1(wr_clk), .CLK2(rd_clk), .A1ADDR(wr_addr), .A1DATA(wr_data), .A1EN(wr_en),
            .B1ADDR(rd_addr), .B1DATA(primitive_data), .B1EN(rd_en)
        );
    end
    always @* assert(reference_data == primitive_data);
endmodule
