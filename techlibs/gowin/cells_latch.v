`default_nettype none

// DL			 D Latch with Positive Gate
module \$_DLATCH_P_ (input E, D, output Q);
	DL _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DLN			 D Latch with Negative Gate
module \$_DLATCH_N_ (input E, D, output Q);
	DLN _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DLC			 D Latch with Positive Gate and Asynchronous Clear
module \$_DLATCH_PP0_ (input E, R, D, output Q);
	DLC _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(E), .CLEAR(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DLNC			 D Latch with Negative Gate and Asynchronous Clear
module \$_DLATCH_NP0_ (input E, R, D, output Q);
	DLNC _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(E), .CLEAR(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DLP			 D Latch with Positive Gate and Asynchronous Preset
module \$_DLATCH_PP1_ (input E, R, D, output Q);
	DLP _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(E), .PRESET(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DLNP			 D Latch with Negative Gate and Asynchronous Preset
module \$_DLATCH_NP1_ (input E, R, D, output Q);
	DLNP _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(E), .PRESET(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
