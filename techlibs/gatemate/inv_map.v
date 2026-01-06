// Any inverters not folded into LUTs are mapped to a LUT of their own
module \$__CC_NOT (input A, output Y);
	CC_LUT1 #(.INIT(2'b01)) _TECHMAP_REPLACE_ (.I0(A), .O(Y));
endmodule
