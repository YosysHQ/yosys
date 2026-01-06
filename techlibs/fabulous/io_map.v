module \$__FABULOUS_IBUF (input PAD, output O);
	IO_1_bidirectional_frame_config_pass _TECHMAP_REPLACE_ (.PAD(PAD), .O(O), .T(1'b1));
endmodule

module \$__FABULOUS_OBUF (output PAD, input I);
	IO_1_bidirectional_frame_config_pass _TECHMAP_REPLACE_ (.PAD(PAD), .I(I), .T(1'b0));
endmodule

