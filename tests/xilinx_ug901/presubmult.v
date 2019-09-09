//
// Pre-adder support in subtract mode for DSP block
// File: presubmult.v

module presubmult  # (//Default parameters were changed because of slow test
					// parameter SIZEIN = 16
                      parameter SIZEIN = 8
                     )
                     (
                      input clk, ce, rst,
                      input  signed [SIZEIN-1:0] a, b, c,
                      output signed [2*SIZEIN:0] presubmult_out
                     );

// Declare registers for intermediate values
reg signed [SIZEIN-1:0] a_reg, b_reg, c_reg;
reg signed [SIZEIN:0]   add_reg;
reg signed [2*SIZEIN:0] m_reg, p_reg;

always @(posedge clk)
 if (rst)
  begin
     a_reg   <= 0;
     b_reg   <= 0;
     c_reg   <= 0;
     add_reg <= 0;
     m_reg   <= 0;
     p_reg   <= 0;
  end
 else if (ce)
  begin
     a_reg   <= a;
     b_reg   <= b;
     c_reg   <= c;
     add_reg <= a - b;
     m_reg   <= add_reg * c_reg;
     p_reg   <= m_reg;
  end

// Output accumulation result
assign presubmult_out = p_reg;

endmodule // presubmult
