
module dff(clk, d, q);
input clk, d;
output reg q;
always @(posedge clk)
	q <= d;
endmodule

module dffa(clk, arst, d, q);
input clk, arst, d;
output reg q;
always @(posedge clk or posedge arst) begin
	if (arst)
		q <= 1;
	else
		q <= d;
end
endmodule

module dffa1(clk, arst, d, q);
input clk, arst, d;
output reg q;
always @(posedge clk or negedge arst) begin
	if (~arst)
		q <= 0;
	else
		q <= d;
end
endmodule

module dffa2(clk, arst, d, q);
input clk, arst, d;
output reg q;
always @(posedge clk or negedge arst) begin
	if (!arst)
		q <= 0;
	else
		q <= d;
end
endmodule

module dffa3(clk, arst, d, q);
input clk, arst, d;
output reg q;
always @(posedge clk or negedge arst) begin
	if (~(!arst))
		q <= d;
	else
		q <= 1;
end
endmodule

module dffa4(clk, arst1, arst2, arst3, d, q);
input clk, arst1, arst2, arst3, d;
output reg q;
always @(posedge clk, posedge arst1, posedge arst2, negedge arst3) begin
	if (arst1)
		q <= 0;
	else if (arst2)
		q <= 0;
	else if (!arst3)
		q <= 0;
	else
		q <= d;
end
endmodule

// SR-Flip-Flops are on the edge of well defined Verilog constructs in terms of
// simulation-implementation mismatches. The following testcases try to cover the
// part that is defined and avoid the undefined cases.

module dffsr1(clk, arst, d, q);
input clk, arst, d;
output reg q;
always @(posedge clk, posedge arst) begin
	if (arst)
		q <= d^d; // constant expression -- but the frontend optimizer does not know that..
	else
		q <= d;
end
endmodule

module dffsr2(clk, preset, clear, d, q);
input clk, preset, clear, d;
output q;
(* gentb_clock *)
wire clk, preset, clear, d;
dffsr2_sub uut (clk, preset && !clear, !preset && clear, d, q);
endmodule

(* gentb_skip *)
module dffsr2_sub(clk, preset, clear, d, q);
input clk, preset, clear, d;
output reg q;
always @(posedge clk, posedge preset, posedge clear) begin
	if (preset)
		q <= 1;
	else if (clear)
		q <= 0;
	else
		q <= d;
end
endmodule


