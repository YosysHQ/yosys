module my_lut (
    input  wire [3:0] i,
    output wire       o
);

    LUT4 #(.INIT(16'hAAAA)) my_lut (
        .I0 (i[0]),
        .I1 (i[1]),
        .I2 (i[2]),
        .I3 (1'bx),
        .O  (o)
    );

endmodule

module my_top (
    input  wire i,
    output wire o
);

    my_lut my_lut (
        .i ({1'b0, 1'b1, i}),
        .o (o)
    );

endmodule
