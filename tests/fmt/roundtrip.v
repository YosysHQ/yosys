module m(input clk, input `SIGN [31:0] data);

	always @(posedge clk)
		// All on a single line to avoid order effects.
`ifdef BASE_DEC
		$display(":%d:%-d:%+d:%+-d:%0d:%-0d:%+0d:%+-0d:%20d:%-20d:%+20d:%+-20d:%020d:%-020d:%+020d:%+-020d:",
		         data, data, data, data, data, data, data, data, data, data, data, data, data, data, data, data);
`endif
`ifdef BASE_HEX
		$display(":%h:%-h:%0h:%-0h:%20h:%-20h:%020h:%-020h:",
		         data, data, data, data, data, data, data, data);
`endif
`ifdef BASE_OCT
		$display(":%o:%-o:%0o:%-0o:%20o:%-20o:%020o:%-020o:",
		         data, data, data, data, data, data, data, data);
`endif
`ifdef BASE_BIN
		$display(":%b:%-b:%0b:%-0b:%20b:%-20b:%020b:%-020b:",
		         data, data, data, data, data, data, data, data);
`endif

endmodule
