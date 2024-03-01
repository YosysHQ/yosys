module \$__BEYOND_IBUF (input PAD, output O);
	NX_IOB_I _TECHMAP_REPLACE_ (.IO(PAD), .O(O), .C(1'b0));
endmodule

module \$__BEYOND_OBUF (output PAD, input I);
	NX_IOB_O _TECHMAP_REPLACE_ (.IO(PAD), .I(I), .C(1'b1));
endmodule

