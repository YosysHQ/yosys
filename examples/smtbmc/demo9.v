module demo9;
	(* maximize *) wire[7:0] h = $anyconst;
	wire [7:0] i = $allconst;

	wire [7:0] t0 = ((i << 8'b00000010) + 8'b00000011);
	wire trigger = (t0 > h)	&& (h < 8'b00000100);

	always @* begin
		assume(trigger == 1'b1);
		cover(1);
	end
endmodule

