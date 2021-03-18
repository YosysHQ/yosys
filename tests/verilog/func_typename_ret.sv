typedef logic [1:0] T;

package P;
    typedef logic [3:0] S;
endpackage

module gate(
    output wire [31:0] out1, out2
);
    function automatic T func1;
        input reg signed inp;
        func1 = inp;
    endfunction
    assign out1 = func1(1);
    function automatic P::S func2;
        input reg signed inp;
        func2 = inp;
    endfunction
    assign out2 = func2(1);
endmodule

module gold(
    output wire [31:0] out1, out2
);
    function automatic [1:0] func1;
        input reg signed inp;
        func1 = inp;
    endfunction
    assign out1 = func1(1);
    function automatic [3:0] func2;
        input reg signed inp;
        func2 = inp;
    endfunction
    assign out2 = func2(1);
endmodule
