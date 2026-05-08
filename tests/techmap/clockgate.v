module dffe_00( input clk, en,
			input d1, output reg q1,
		);
	always @( negedge clk ) begin
		if ( ~en )
			q1 <= d1;
	end
endmodule

module dffe_01( input clk, en,
			input d1, output reg q1,
		);
	always @( negedge clk ) begin
		if ( en )
			q1 <= d1;
	end
endmodule

module dffe_10( input clk, en,
			input d1, output reg q1,
		);
	always @( posedge clk ) begin
		if ( ~en )
			q1 <= d1;
	end
endmodule

module dffe_11( input clk, en,
			input d1, output reg q1,
		);
	always @( posedge clk ) begin
		if ( en )
			q1 <= d1;
	end
endmodule

module dffe_wide_11( input clk, en,
			input [3:0] d1, output reg [3:0] q1,
		);
	always @( posedge clk ) begin
		if ( en )
			q1 <= d1;
	end
endmodule