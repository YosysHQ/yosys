// Single-Port Block RAM Read-First Mode
// rams_sp_rf.v
module rams_sp_rf (clk, en, we, addr, di, dout);

input clk; 
input we; 
input en;
input [9:0] addr; 
input [15:0] di; 
output [15:0] dout;

reg [15:0] RAM [1023:0];
reg [15:0] dout;

always @(posedge clk)
begin
  if (en)
    begin
      if (we)
        RAM[addr]<=di;
      dout <= RAM[addr];
    end
end

endmodule

