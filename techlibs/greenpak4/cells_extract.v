//Wrapper module to patch up output of iopadmap
module GP_IOBUF(input IN, output OUT, input OE, inout IO);

	GP_IBUF ibuf(
		.IN(IO),
		.OUT(OUT)
	);
	
	$_TBUF_ tbuf(
		.A(IN),
		.E(OE),
		.Y(OUT)
	);

endmodule
