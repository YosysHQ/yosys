// 32-bit register with byte-lane writes indexed by a 2-bit selector (VPS).
module opt_vps_byte_write (
    input  logic        clk,
    input  logic        wr_en,
    input  logic [1:0]  lane,
    input  logic [7:0]  wdata,
    output logic [31:0] q
);
    logic [31:0] reg_data;
    always_ff @(posedge clk)
        if (wr_en)
            reg_data[((lane + 1) * 8) - 1 -: 8] <= wdata;
    assign q = reg_data;
endmodule
