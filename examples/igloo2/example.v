module example (
	input  clk,
	input  SW1,
	input  SW2,
	output LED1,
	output LED2,
	output LED3,
	output LED4,

	output AA, AB, AC, AD,
	output AE, AF, AG, CA
);

	localparam BITS = 8;
	localparam LOG2DELAY = 22;

	reg [BITS+LOG2DELAY-1:0] counter = 0;
	reg [BITS-1:0] outcnt;

	always @(posedge clk) begin
		counter <= counter + SW1 + SW2 + 1;
		outcnt <= counter >> LOG2DELAY;
	end

	assign {LED1, LED2, LED3, LED4} = outcnt ^ (outcnt >> 1);

	// assign CA = counter[10];
	// seg7enc seg7encinst (
	// 	.seg({AA, AB, AC, AD, AE, AF, AG}),
	// 	.dat(CA ? outcnt[3:0] : outcnt[7:4])
	// );

	assign {AA, AB, AC, AD, AE, AF, AG} = ~(7'b 100_0000 >> outcnt[6:4]);
	assign CA = outcnt[7];
endmodule

module seg7enc (
	input [3:0] dat,
	output [6:0] seg
);
	reg [6:0] seg_inv;
	always @* begin
		seg_inv = 0;
		case (dat)
			4'h0: seg_inv = 7'b 0111111;
			4'h1: seg_inv = 7'b 0000110;
			4'h2: seg_inv = 7'b 1011011;
			4'h3: seg_inv = 7'b 1001111;
			4'h4: seg_inv = 7'b 1100110;
			4'h5: seg_inv = 7'b 1101101;
			4'h6: seg_inv = 7'b 1111101;
			4'h7: seg_inv = 7'b 0000111;
			4'h8: seg_inv = 7'b 1111111;
			4'h9: seg_inv = 7'b 1101111;
			4'hA: seg_inv = 7'b 1110111;
			4'hB: seg_inv = 7'b 1111100;
			4'hC: seg_inv = 7'b 0111001;
			4'hD: seg_inv = 7'b 1011110;
			4'hE: seg_inv = 7'b 1111001;
			4'hF: seg_inv = 7'b 1110001;
		endcase
	end
	assign seg = ~seg_inv;
endmodule
