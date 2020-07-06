(* techmap_celltype = "$adff" *)
module adff2dff (CLK, ARST, D, Q);
	parameter WIDTH = 1;
	parameter CLK_POLARITY = 1;
	parameter ARST_POLARITY = 1;
	parameter ARST_VALUE = 0;

	input CLK, ARST;
	input [WIDTH-1:0] D;
	output reg [WIDTH-1:0] Q;
	wire reg [WIDTH-1:0] NEXT_Q;

	wire [1023:0] _TECHMAP_DO_ = "proc;;";

	always @*
		if (ARST == ARST_POLARITY)
			NEXT_Q <= ARST_VALUE;
		else
			NEXT_Q <= D;

	if (CLK_POLARITY)
		always @(posedge CLK)
			Q <= NEXT_Q;
	else
		always @(negedge CLK)
			Q <= NEXT_Q;
endmodule
