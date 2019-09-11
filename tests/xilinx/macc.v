// Signed 40-bit streaming accumulator with 16-bit inputs
// File: HDL_Coding_Techniques/multipliers/multipliers4.v
//
// Source:
// https://www.xilinx.com/support/documentation/sw_manuals/xilinx2014_2/ug901-vivado-synthesis.pdf p.90
//
module macc # (parameter SIZEIN = 16, SIZEOUT = 40) (
	input clk, ce, sload,
	input signed [SIZEIN-1:0] a, b,
	output signed [SIZEOUT-1:0] accum_out
);
// Declare registers for intermediate values
reg signed [SIZEIN-1:0] a_reg, b_reg;
reg sload_reg;
reg signed [2*SIZEIN-1:0] mult_reg;
reg signed [SIZEOUT-1:0] adder_out, old_result;
always @* /*(adder_out or sload_reg)*/ begin // Modification necessary to fix sim/synth mismatch
	if (sload_reg)
		old_result <= 0;
	else
		// 'sload' is now active (=low) and opens the accumulation loop.
		// The accumulator takes the next multiplier output in
		// the same cycle.
		old_result <= adder_out;
end

always @(posedge clk)
	if (ce)
	begin
		a_reg <= a;
		b_reg <= b;
		mult_reg <= a_reg * b_reg;
		sload_reg <= sload;
		// Store accumulation result into a register
		adder_out <= old_result + mult_reg;
	end

// Output accumulation result
assign accum_out = adder_out;

endmodule

// Adapted variant of above
module macc2 # (parameter SIZEIN = 16, SIZEOUT = 40) (
	input clk, ce, rst,
	input signed [SIZEIN-1:0] a, b,
	output signed [SIZEOUT-1:0] accum_out
);
// Declare registers for intermediate values
reg signed [SIZEIN-1:0] a_reg, b_reg;
reg rst_reg;
reg signed [2*SIZEIN-1:0] mult_reg;
reg signed [SIZEOUT-1:0] adder_out, old_result;
always @(posedge clk) begin
	if (ce)
	begin
		a_reg <= a;
		b_reg <= b;
		mult_reg <= a_reg * b_reg;
		rst_reg <= rst;
		// Store accumulation result into a register
		adder_out <= adder_out + mult_reg;
	end
	if (rst) begin
		a_reg <= 0;
		b_reg <= 0;
		mult_reg <= 0;
		adder_out <= 0;
	end
end

// Output accumulation result
assign accum_out = adder_out;

endmodule
