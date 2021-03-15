module subtractor (
    input  wire [`WIDTH-1:0] A,
    input  wire [`WIDTH-1:0] B,
    output wire [`WIDTH  :0] S,
);

    // Implicit subtractor
    assign S = A - B;

endmodule
