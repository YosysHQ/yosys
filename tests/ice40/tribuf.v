module tristate (en, i, o);
    input en;
    input i;
    output reg o;

    always @(en or i)
		o <= (en)? i : 1'bZ;
endmodule


module top (
input en,
input a,
output b
);

tristate u_tri (
        .en (en ),
        .i (a ),
        .o (b )
    );

endmodule
