module real_rtoi(output [31:0] a);
	assign a = $rtoi(1.0e20);
endmodule
