`default_nettype none

module gate(x, y);
    output reg [15:0] x, y;
    if (1) begin : gen
        integer x, y;
        for (genvar x = 0; x < 2; x++)
            if (x == 0)
                initial gen.x = 10;
        assign y = x + 1;
    end
    initial x = gen.x;
    assign y = gen.y;
endmodule

module gold(x, y);
    output reg [15:0] x, y;
    if (1) begin : gen
        integer x, y;
        genvar z;
        for (z = 0; z < 2; z++)
            if (z == 0)
                initial x = 10;
        assign y = x + 1;
    end
    initial x = gen.x;
    assign y = gen.y;
endmodule
