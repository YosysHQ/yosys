module IBUF(input I, output O);
    assign O = I;
endmodule

module IOBUFE(input I, input E, output O, inout IO);
    assign O = IO;
    assign IO = E ? I : 1'bz;
endmodule

module ANDTERM(IN, IN_B, OUT);
    parameter TRUE_INP = 0;
    parameter COMP_INP = 0;

    input [TRUE_INP-1:0] IN;
    input [COMP_INP-1:0] IN_B;
    output reg OUT;

    integer i;

    always @(*) begin
        OUT = 1;
        for (i = 0; i < TRUE_INP; i=i+1)
            OUT = OUT & IN[i];
        for (i = 0; i < COMP_INP; i=i+1)
            OUT = OUT & ~IN_B[i];
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
