module tristate(en, i, o);
    input en;
    input i;
    output reg o;

    always @(en or i)
        o <= (en)? i : 1'bZ;
endmodule
