// Copied from techlibs/common/simlib.v
// with this condition removed: (^{P, G, CI} !== 1'bx)
module lcu (P, G, CI, CO);

parameter WIDTH = 2;

input [WIDTH-1:0] P;    // Propagate
input [WIDTH-1:0] G;    // Generate
input CI;               // Carry-in

output reg [WIDTH-1:0] CO; // Carry-out

integer i;
always @* begin
	CO[0] = G[0] || (P[0] && CI);
	for (i = 1; i < WIDTH; i = i+1)
		CO[i] = G[i] || (P[i] && CO[i-1]);
end

endmodule
