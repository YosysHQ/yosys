module gate(out);
    parameter integer a = -1;
    parameter int b = -2;
    parameter shortint c = -3;
    parameter longint d = -4;
    parameter byte e = -5;
    output wire [1023:0] out;
    assign out = {a, b, c, d, e};
endmodule

module gold(out);
    integer a = -1;
    int b = -2;
    shortint c = -3;
    longint d = -4;
    byte e = -5;
    output wire [1023:0] out;
    assign out = {a, b, c, d, e};
endmodule
