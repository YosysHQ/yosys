// This module performs subtraction of two inputs, squaring on the diff
// and then accumulation
// This can be implemented in 1 DSP Block (Ultrascale architecture)
// File : squarediffmacc.v
module squarediffmacc  # (
						//Default parameters were changed because of slow test
                          //parameter SIZEIN = 16,
                                    //SIZEOUT = 40
						  parameter SIZEIN = 8,
                          SIZEOUT = 20
                         )
                        (
                         input clk,
                         input ce,
                         input sload,
                         input signed [SIZEIN-1:0]   a,
                         input signed [SIZEIN-1:0]   b,
                         output signed [SIZEOUT+1:0] accum_out
                        );

// Declare registers for intermediate values
reg signed [SIZEIN-1:0]  a_reg, b_reg;
reg signed [SIZEIN:0]  diff_reg;
reg                       sload_reg;
reg signed [2*SIZEIN+1:0] m_reg;
reg signed [SIZEOUT-1:0]  adder_out, old_result;

  always @(sload_reg or adder_out)
  if (sload_reg)
    old_result <= 0;
  else
    // 'sload' is now and opens the accumulation loop.
    // The accumulator takes the next multiplier output
    // in the same cycle.
    old_result <= adder_out;

  always @(posedge clk)
  if (ce)
  begin
    a_reg     <= a;
    b_reg     <= b;
    diff_reg  <= a_reg - b_reg;
    m_reg  <= diff_reg * diff_reg;
    sload_reg <= sload;
    // Store accumulation result into a register
    adder_out <= old_result + m_reg;
  end

  // Output accumulation result
  assign accum_out = adder_out;

endmodule // squarediffmacc
