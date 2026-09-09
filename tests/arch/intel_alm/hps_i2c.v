module top (
    input  wire scl,
    input  wire sda,
    output wire out_data,
    output wire out_clk
);
    cyclonev_hps_interface_peripheral_i2c i2c (
        .scl(scl),
        .sda(sda),
        .out_data(out_data),
        .out_clk(out_clk)
    );
endmodule
