`ifndef CLOCKGATE_ICG_MODELS
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

// falling edge, active-low enable, synchronous reset has priority.
module sdffe_00( input clk, en, rst,
			input d1, output reg q1
		);
	always @( negedge clk ) begin
		if ( rst )
			q1 <= 1'b0;
		else if ( ~en )
			q1 <= d1;
	end
endmodule

// falling edge, active-high enable, reset must also work when en=0
module sdffe_01( input clk, en, rst,
			input d1, output reg q1
		);
	always @( negedge clk ) begin
		if ( rst )
			q1 <= 1'b0;
		else if ( en )
			q1 <= d1;
	end
endmodule

// rising edge, active-low enable, reset must also work when en=1
module sdffe_10( input clk, en, rst,
			input d1, output reg q1
		);
	always @( posedge clk ) begin
		if ( rst )
			q1 <= 1'b0;
		else if ( ~en )
			q1 <= d1;
	end
endmodule

// rising edge, active-high enable, synchronous reset has priority.
module sdffe_11( input clk, en, rst,
			input d1, output reg q1
		);
	always @( posedge clk ) begin
		if ( rst )
			q1 <= 1'b0;
		else if ( en )
			q1 <= d1;
	end
endmodule

// four bits share one clock gate, reset is active low and has priority
// the mixed reset value checks that every reset bit survives clock gating
module sdffe_wide( input clk, en, rst,
			input [3:0] d1, output reg [3:0] q1
		);
	always @( posedge clk ) begin
		if ( ~rst )
			q1 <= 4'hA;
		else if ( en )
			q1 <= d1;
	end
endmodule


// these sdffes share CLK/EN but they need separate gates because resets are different
// independent data inputs and reset values make accidental sharing observable
module sdffe_separate_reset( input clk, en, rst1, rst2,
			input d1, d2, output reg q1, q2
		);
	always @( posedge clk ) begin
		if ( rst1 )
			q1 <= 1'b0;
		else if ( en )
			q1 <= d1;
	end

	always @( posedge clk ) begin
		if ( rst2 )
			q2 <= 1'b1;
		else if ( en )
			q2 <= d2;
	end
endmodule

`else


module pos_small(input CE, CLK, output GCLK);
    reg ce_latched;
    always @* begin
        if (!CLK) ce_latched = CE;
    end
    assign GCLK = CLK & ce_latched;
endmodule

module neg_small(input CE, CLK, output GCLK);
    reg ce_latched;
    always @* begin
        if (CLK) ce_latched = CE;
    end
    assign GCLK = CLK | !ce_latched;
endmodule

`endif
