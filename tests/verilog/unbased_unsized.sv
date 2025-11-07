module pass_through(
    input [63:0] inp,
    output [63:0] out
);
    assign out = inp;
endmodule

module set_param #(
    parameter logic [63:0] VALUE
) (
    output logic [63:0] out
);
    assign out = VALUE;
endmodule

module top;
    localparam logic [63:0]
        l01 = '0,
        l02 = '1,
        l03 = 'x,
        l04 = 'z;
    logic [63:0]
        o01, o02, o03, o04,
        o05, o06, o07, o08,
        o09, o10, o11, o12,
        o13, o14, o15, o16;
    assign o01 = '0;
    assign o02 = '1;
    assign o03 = 'x;
    assign o04 = 'z;
    assign o05 = 3'('0);
    assign o06 = 3'('1);
    assign o07 = 3'('x);
    assign o08 = 3'('z);
    pass_through pt09('0, o09);
    pass_through pt10('1, o10);
    pass_through pt11('x, o11);
    pass_through pt12('z, o12);
    set_param #('0) sp13(o13);
    set_param #('1) sp14(o14);
    set_param #('x) sp15(o15);
    set_param #('z) sp16(o16);
    always @* begin
        assert (o01 === {64 {1'b0}});
        assert (o02 === {64 {1'b1}});
        assert (o03 === {64 {1'bx}});
        assert (o04 === {64 {1'bz}});
        assert (o05 === {61'b0, 3'b000});
        assert (o06 === {61'b0, 3'b111});
        assert (o07 === {61'b0, 3'bxxx});
        assert (o08 === {61'b0, 3'bzzz});
        assert (o09 === {64 {1'b0}});
        assert (o10 === {64 {1'b1}});
        assert (o11 === {64 {1'bx}});
        assert (o12 === {64 {1'bz}});
        assert (l01 === {64 {1'b0}});
        assert (l02 === {64 {1'b1}});
        assert (l03 === {64 {1'bx}});
        assert (l04 === {64 {1'bz}});
        assert (o13 === {64 {1'b0}});
        assert (o14 === {64 {1'b1}});
        assert (o15 === {64 {1'bx}});
        assert (o16 === {64 {1'bz}});
    end
endmodule
