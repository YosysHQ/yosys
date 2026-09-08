// Each logical byte occupies the low bits of a physical 10-bit lane.
module \$__MISTRAL_M10K_TDP_BYTE_ (PORT_A_CLK, PORT_A_CLK_EN, PORT_A_ADDR,
    PORT_A_WR_DATA, PORT_A_WR_EN, PORT_A_WR_BE, PORT_A_RD_DATA,
    PORT_B_CLK, PORT_B_CLK_EN, PORT_B_ADDR,
    PORT_B_WR_DATA, PORT_B_WR_EN, PORT_B_WR_BE, PORT_B_RD_DATA);
parameter OPTION_BYTE = 10;
parameter [512*2*OPTION_BYTE-1:0] INIT = 0;
input PORT_A_CLK, PORT_A_CLK_EN, PORT_A_WR_EN;
input PORT_B_CLK, PORT_B_CLK_EN, PORT_B_WR_EN;
input [1:0] PORT_A_WR_BE, PORT_B_WR_BE;
input [8:0] PORT_A_ADDR, PORT_B_ADDR;
input [2*OPTION_BYTE-1:0] PORT_A_WR_DATA, PORT_B_WR_DATA;
output [2*OPTION_BYTE-1:0] PORT_A_RD_DATA, PORT_B_RD_DATA;
wire [19:0] data_a, data_b, q_a, q_b;
function [10239:0] pad_init;
    input [512*2*OPTION_BYTE-1:0] logical_init;
    integer word, lane;
    begin
        pad_init = 0;
        for (word = 0; word < 512; word = word + 1)
            for (lane = 0; lane < 2; lane = lane + 1)
                pad_init[word*20 + lane*10 +: OPTION_BYTE] = logical_init[(word*2+lane)*OPTION_BYTE +: OPTION_BYTE];
    end
endfunction
localparam [10239:0] PHYSICAL_INIT = pad_init(INIT);
genvar lane;
generate for (lane = 0; lane < 2; lane = lane + 1) begin
    assign data_a[lane*10 +: 10] = {{(10-OPTION_BYTE){1'b0}}, PORT_A_WR_DATA[lane*OPTION_BYTE +: OPTION_BYTE]};
    assign data_b[lane*10 +: 10] = {{(10-OPTION_BYTE){1'b0}}, PORT_B_WR_DATA[lane*OPTION_BYTE +: OPTION_BYTE]};
    assign PORT_A_RD_DATA[lane*OPTION_BYTE +: OPTION_BYTE] = q_a[lane*10 +: OPTION_BYTE];
    assign PORT_B_RD_DATA[lane*OPTION_BYTE +: OPTION_BYTE] = q_b[lane*10 +: OPTION_BYTE];
end endgenerate
MISTRAL_M10K_TDP #(.CFG_ABITS(9), .CFG_DBITS(20), .CFG_BYTE_ENABLE(1), .INIT(PHYSICAL_INIT))
    _TECHMAP_REPLACE_ (
    .CLK1(PORT_A_CLK), .CLK2(PORT_B_CLK),
    .A1EN(PORT_A_CLK_EN), .B1EN(PORT_B_CLK_EN),
    .A1WE(PORT_A_WR_EN), .B1WE(PORT_B_WR_EN),
    .A1BE(PORT_A_WR_BE), .B1BE(PORT_B_WR_BE),
    .A1ADDR(PORT_A_ADDR), .B1ADDR(PORT_B_ADDR),
    .A1DATA(data_a), .B1DATA(data_b), .A1Q(q_a), .B1Q(q_b));
endmodule
