module IBUF(input I, output O);
    assign O = I;
endmodule

module IOBUFE(input I, input E, output O, inout IO);
    assign O = IO;
    assign IO = E ? I : 1'bz;
endmodule

module ANDTERM(IN, OUT);
    parameter WIDTH = 0;

    input [(WIDTH*2)-1:0] IN;
    output reg OUT;

    integer i;

    always @(*) begin
        OUT = 1;
        for (i = 0; i < WIDTH; i=i+1) begin
            OUT = OUT & ~IN[i * 2 + 0];
            OUT = OUT & IN[i * 2 + 1];
        end
    end
endmodule

module ORTERM(IN, OUT);
    parameter WIDTH = 0;

    input [WIDTH-1:0] IN;
    output reg OUT;

    integer i;

    always @(*) begin
        OUT = 0;
        for (i = 0; i < WIDTH; i=i+1) begin
            OUT = OUT | IN[i];
        end
    end
endmodule
