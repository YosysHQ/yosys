module top(...);
    input a, b, s;
    output y;
    assign y = s?a:b;
endmodule
