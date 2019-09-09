// Simple Dual-Port Block RAM with Two Clocks
// File: simple_dual_two_clocks.v

module simple_dual_two_clocks (clka,clkb,ena,enb,wea,addra,addrb,dia,dob);

input clka,clkb,ena,enb,wea;
input [9:0] addra,addrb;
input [15:0] dia;
output [15:0] dob;
reg [15:0] ram [1023:0];
reg [15:0] dob;

always @(posedge clka) 
begin 
  if (ena)
    begin
      if (wea)
        ram[addra] <= dia;
    end
end

always @(posedge clkb) 
begin
  if (enb)
    begin
      dob <= ram[addrb];
    end
end

endmodule
