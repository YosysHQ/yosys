// Initializing Block RAM (Single-Port Block RAM)
// File: rams_sp_rom 
module rams_sp_rom (clk, we, addr, di, dout);
input clk;
input we;
input [5:0] addr;
input [19:0] di;
output [19:0] dout;

reg [19:0] ram [63:0];
reg [19:0] dout;

initial 
begin
  ram[63] = 20'h0200A; ram[62] = 20'h00300; ram[61] = 20'h08101;
  ram[60] = 20'h04000; ram[59] = 20'h08601; ram[58] = 20'h0233A;
  ram[57] = 20'h00300; ram[56] = 20'h08602; ram[55] = 20'h02310;
  ram[54] = 20'h0203B; ram[53] = 20'h08300; ram[52] = 20'h04002;
  ram[51] = 20'h08201; ram[50] = 20'h00500; ram[49] = 20'h04001;
  ram[48] = 20'h02500; ram[47] = 20'h00340; ram[46] = 20'h00241;
  ram[45] = 20'h04002; ram[44] = 20'h08300; ram[43] = 20'h08201;
  ram[42] = 20'h00500; ram[41] = 20'h08101; ram[40] = 20'h00602;
  ram[39] = 20'h04003; ram[38] = 20'h0241E; ram[37] = 20'h00301;
  ram[36] = 20'h00102; ram[35] = 20'h02122; ram[34] = 20'h02021;
  ram[33] = 20'h00301; ram[32] = 20'h00102; ram[31] = 20'h02222;
  ram[30] = 20'h04001; ram[29] = 20'h00342; ram[28] = 20'h0232B; 
  ram[27] = 20'h00900; ram[26] = 20'h00302; ram[25] = 20'h00102; 
  ram[24] = 20'h04002; ram[23] = 20'h00900; ram[22] = 20'h08201; 
  ram[21] = 20'h02023; ram[20] = 20'h00303; ram[19] = 20'h02433; 
  ram[18] = 20'h00301; ram[17] = 20'h04004; ram[16] = 20'h00301; 
  ram[15] = 20'h00102; ram[14] = 20'h02137; ram[13] = 20'h02036; 
  ram[12] = 20'h00301; ram[11] = 20'h00102; ram[10] = 20'h02237; 
  ram[9]  = 20'h04004; ram[8]  = 20'h00304; ram[7] = 20'h04040; 
  ram[6]  = 20'h02500; ram[5]  = 20'h02500; ram[4] = 20'h02500; 
  ram[3]  = 20'h0030D; ram[2]  = 20'h02341; ram[1] = 20'h08201; 
  ram[0]  = 20'h0400D;
end
 
always @(posedge clk)
begin
  if (we)
    ram[addr] <= di;
  dout <= ram[addr];
end 

endmodule
