// 8-bit Register with
// Rising-edge Clock
// Active-high Synchronous Clear
// Active-high Clock Enable
// File: registers_1.v

module registers_1(d_in,ce,clk,clr,dout);
input [7:0] d_in;
input ce;
input clk;
input clr;
output [7:0] dout;
reg [7:0] d_reg;

always @ (posedge clk)
begin
 if(clr)
  d_reg <= 8'b0;
 else if(ce)
  d_reg <= d_in;
end

assign dout = d_reg;
endmodule

