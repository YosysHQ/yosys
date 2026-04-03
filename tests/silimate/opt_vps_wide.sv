// 128-bit register with 16-bit lane writes indexed by a 3-bit selector (VPS).
module opt_vps_wide (
    input  logic        clk,
    input  logic        wr_en,
    input  logic [2:0]  lane,
    input  logic [15:0] wdata,
    output logic [127:0] q
);
    logic [127:0] reg_data;
    always_ff @(posedge clk)
        if (wr_en)
            reg_data[((lane + 1) * 16) - 1 -: 16] <= wdata;
    assign q = reg_data;
endmodule
