// Pre-add/subtract select with Dynamic control
// dynpreaddmultadd.v
//Default parameters were changed because of slow test.
//module dynpreaddmultadd  # (parameter SIZEIN = 16)
module dynpreaddmultadd  # (parameter SIZEIN = 8)
        (
          input clk, ce, rst, subadd,
          input  signed [SIZEIN-1:0] a, b, c, d,
          output signed [2*SIZEIN:0] dynpreaddmultadd_out
        );

// Declare registers for intermediate values
reg signed [SIZEIN-1:0] a_reg, b_reg, c_reg;
reg signed [SIZEIN:0]   add_reg;
reg signed [2*SIZEIN:0] d_reg, m_reg, p_reg;

always @(posedge clk)
begin
 if (rst)
  begin
   a_reg   <= 0;
   b_reg   <= 0;
   c_reg   <= 0;
   d_reg   <= 0;
   add_reg <= 0;
   m_reg   <= 0;
   p_reg   <= 0;
  end
 else if (ce)
  begin
   a_reg   <= a;
   b_reg   <= b;
   c_reg   <= c;
   d_reg   <= d;
   if (subadd)
    add_reg <= a_reg - b_reg;
   else
    add_reg <= a_reg + b_reg;
   m_reg   <= add_reg * c_reg;
   p_reg   <= m_reg + d_reg;
  end
end

// Output accumulation result
assign dynpreaddmultadd_out = p_reg;

endmodule // dynpreaddmultadd
