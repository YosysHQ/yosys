module tristate (en, i, o);
    input en;
    input i;
    output o;

	assign o = en ? i : 1'bz;

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
