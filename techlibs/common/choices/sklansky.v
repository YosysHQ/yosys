(* techmap_celltype = "$lcu" *)
module _80_lcu_sklansky (P, G, CI, CO);
	parameter WIDTH = 2;

	(* force_downto *)
	input [WIDTH-1:0] P, G;
	input CI;

	(* force_downto *)
	output [WIDTH-1:0] CO;

	integer i, j;
	(* force_downto *)
	reg [WIDTH-1:0] p, g;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	always @* begin
		p = P;
		g = G;

		// in almost all cases CI will be constant zero
		g[0] = g[0] | (p[0] & CI);

		for (i = 0; i < $clog2(WIDTH); i = i + 1) begin
			// iterate in reverse so we don't confuse a result from this stage and the previous
			for (j = WIDTH - 1; j >= 0; j = j - 1) begin
				if (j & 2**i) begin
					g[j] = g[j] | p[j] & g[(j & ~(2**i - 1)) - 1];
					p[j] = p[j] & p[(j & ~(2**i - 1)) - 1];
				end
			end
		end
	end

	assign CO = g;
endmodule
