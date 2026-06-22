module dffe_wide_11( input clk, input [1:0] en,
			input [3:0] d1, output reg [3:0] q1,
		);
	always @( posedge clk ) begin
		if ( en[0] )
			q1 <= d1;
	end
endmodule