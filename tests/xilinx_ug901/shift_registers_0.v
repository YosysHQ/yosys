//  8-bit Shift Register
//  Rising edge clock
//  Active high clock enable
//  Concatenation-based template
//  File: shift_registers_0.v

module shift_registers_0 (clk, clken, SI, SO);
parameter WIDTH = 32; 
input clk, clken, SI; 
output SO;

reg [WIDTH-1:0] shreg;

always @(posedge clk)
  begin
    if (clken)
      shreg = {shreg[WIDTH-2:0], SI};
  end

assign SO = shreg[WIDTH-1];

endmodule
