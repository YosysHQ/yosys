// Reference: equivalent design WITHOUT variable-part-select.
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
            case (lane)
                2'd0: reg_data[ 7: 0] <= wdata;
                2'd1: reg_data[15: 8] <= wdata;
                2'd2: reg_data[23:16] <= wdata;
                2'd3: reg_data[31:24] <= wdata;
            endcase
    assign q = reg_data;
endmodule
