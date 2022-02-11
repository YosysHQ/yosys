module top (
    input wire signed x,
    output reg [31:0] y
);
    wire signed fail = ~x;

    always @*
        case (x)
            1'b0: y = 0;
            1'b1: y = 1;
            default: y = fail;
        endcase

    always @*
        case (x)
            2'sb00: y = 0;
            2'sb00: y = fail;
        endcase

    always @*
        case (x)
            2'sb00: y = 0;
            default: y = fail;
            2'sb01: y = 1;
            2'sb10: y = 2;
            2'sb11: y = 3;
            2'sb00: y = fail;
            2'sb01: y = fail;
            2'sb10: y = fail;
            2'sb11: y = fail;
        endcase


    always @*
        case ({x, x})
            2'b00: y = 0;
            2'b01: y = 1;
            2'b10: y = 2;
            2'b11: y = 3;
            default: y = fail;
            2'b00: y = fail;
            2'b01: y = fail;
            2'b10: y = fail;
            2'b11: y = fail;
        endcase
endmodule
