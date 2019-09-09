// Dual-Port Block RAM with Two Write Ports
// File: rams_tdp_rf_rf.v

module rams_tdp_rf_rf (clka,clkb,ena,enb,wea,web,addra,addrb,dia,dib,doa,dob);

input clka,clkb,ena,enb,wea,web;
input [9:0] addra,addrb;
input [15:0] dia,dib;
output [15:0] doa,dob;
reg [15:0] ram [1023:0];
reg [15:0] doa,dob;

always @(posedge clka)
begin 
  if (ena)
    begin
      if (wea)
        ram[addra] <= dia;
      doa <= ram[addra];
    end
end

always @(posedge clkb) 
begin 
  if (enb)
    begin
      if (web)
        ram[addrb] <= dib;
      dob <= ram[addrb];
    end
end

endmodule
