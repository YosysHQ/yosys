module tristate (en, i, o);
    input en;
    input i;
    output o;

	assign o = en ? i : 1'bz;

endmodule
