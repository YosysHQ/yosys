// Minimal variable-part-select (VPS) read: extracts a 32-bit word
// from a 256-bit register at a dynamic byte offset.
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

    assign q = reg_data[index +: 32];
endmodule
