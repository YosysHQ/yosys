// Reference for VPS read: uses right-shift instead of variable part-select.
module opt_vps_read (
    input  logic        clk,
    input  logic        wr_en,
    input  logic [7:0]  index,
    input  logic [255:0] wdata,
    output logic [31:0]  q
);
    logic [255:0] reg_data;

    always_ff @(posedge clk)
        if (wr_en)
            reg_data <= wdata;

    assign q = (reg_data >> index);
endmodule
