// Writable initialized MLAB diagnostic using the misteross 040 HPS GP layout.
module storage_port(input FPGA_CLK1_50, we, input [4:0] addr,
                    input [7:0] wdata, output reg [7:0] rdata);
    (* ramstyle = "mlab" *) reg [7:0] stored [0:31];
    integer i;
    initial begin
        rdata = 0;
        for (i = 0; i < 32; i = i + 1)
            stored[i] = ((i * 73) ^ (i >> 1) ^ 8'ha6) & 8'hff;
    end
    always @(posedge FPGA_CLK1_50) begin
        if (we) stored[addr] <= wdata;
        rdata <= stored[addr];
    end
endmodule

module top(input FPGA_CLK1_50);
    wire [31:0] gp_in, gp_out;
    wire [7:0] rdata;
    reg [1:0] beat = 0;
    cyclonev_hps_interface_mpu_general_purpose hps_gp(.gp_in(gp_in), .gp_out(gp_out));
    storage_port storage(.FPGA_CLK1_50(FPGA_CLK1_50), .we(gp_out[16]),
                         .addr(gp_out[4:0]), .wdata(gp_out[15:8]), .rdata(rdata));
    always @(posedge FPGA_CLK1_50) beat <= beat + 1'b1;
    assign gp_in = {16'hD410, 6'b0, beat, rdata};
endmodule
