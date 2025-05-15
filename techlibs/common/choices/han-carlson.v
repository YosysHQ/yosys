(* techmap_celltype = "$lcu" *)
module _80_lcu_han_carlson (P, G, CI, CO);
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
		i = 0;
		p = P;
		g = G;

		// in almost all cases CI will be constant zero
		g[0] = g[0] | (p[0] & CI);
		if (i < $clog2(WIDTH)) begin

			// First layer: BK
			for (j = WIDTH - 1; j >= 0; j = j - 1) begin
				if (j % 2 == 1) begin
					g[j] = g[j] | p[j] & g[j - 1];
					p[j] = p[j] & p[j - 1];
				end
			end

			// Inner (log(WIDTH) - 1) layers: KS
			for (i = 1; i < $clog2(WIDTH); i = i + 1) begin
				for (j = WIDTH - 1; j >= 2**i; j = j - 1) begin
					if (j % 2 == 1) begin
						g[j] = g[j] | p[j] & g[j - 2**i];
						p[j] = p[j] & p[j - 2**i];
					end
				end
			end

			// Last layer: BK
			if (i < ($clog2(WIDTH) + 1)) begin
				for (j = WIDTH - 1; j >= 0; j = j - 1) begin
					if ((j % 2 == 0) && (j > 0)) begin
						g[j] = g[j] | p[j] & g[j - 1];
						p[j] = p[j] & p[j - 1];
					end
				end
			end

		end
	end

	assign CO = g;
endmodule
