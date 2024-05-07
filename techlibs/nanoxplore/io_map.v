module \$__BEYOND_IBUF (input PAD, output O);
	NX_IOB_I _TECHMAP_REPLACE_ (.IO(PAD), .O(O), .C(1'b0));
endmodule

module \$__BEYOND_OBUF (output PAD, input I);
	NX_IOB_O _TECHMAP_REPLACE_ (.IO(PAD), .I(I), .C(1'b1));
endmodule

module \$__BEYOND_TOBUF (output PAD, input I, input C);
	NX_IOB _TECHMAP_REPLACE_ (.IO(PAD), .I(I), .C(C));
endmodule

module \$__BEYOND_IOBUF (output PAD, input I, output O, output C);
	NX_IOB _TECHMAP_REPLACE_ (.IO(PAD), .I(I), .O(O), .C(C));
endmodule
