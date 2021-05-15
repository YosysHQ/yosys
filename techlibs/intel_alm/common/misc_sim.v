module MISTRAL_IB((* iopad_external_pin *)  input PAD, output O);
	assign O = PAD;
endmodule

module MISTRAL_OB((* iopad_external_pin *)  output PAD, input I);
	assign PAD = I;
endmodule

module MISTRAL_IO((* iopad_external_pin *)  inout PAD, input I, input OE, output O);
	assign PAD = OE ? I : 1'bz;
	assign O = PAD;
endmodule
