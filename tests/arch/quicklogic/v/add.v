module adder (
    input  wire [`WIDTH-1:0] A,
    input  wire [`WIDTH-1:0] B,
    output wire [`WIDTH  :0] S,
);

    // Implicit adder
    assign S = A + B;

endmodule
