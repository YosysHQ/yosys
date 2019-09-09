// ROMs Using Block RAM Resources.
// File: rams_sp_rom_1.v
//
module rams_sp_rom_1 (clk, en, addr, dout);
input clk;
input en;
input [5:0] addr;
output  [19:0] dout;

(*rom_style = "block" *) reg [19:0] data;

always @(posedge clk) 
begin 
  if (en)
    case(addr)
      6'b000000: data <= 20'h0200A; 6'b100000: data <= 20'h02222;
      6'b000001: data <= 20'h00300; 6'b100001: data <= 20'h04001;
      6'b000010: data <= 20'h08101; 6'b100010: data <= 20'h00342;
      6'b000011: data <= 20'h04000; 6'b100011: data <= 20'h0232B;
      6'b000100: data <= 20'h08601; 6'b100100: data <= 20'h00900;
      6'b000101: data <= 20'h0233A; 6'b100101: data <= 20'h00302;
      6'b000110: data <= 20'h00300; 6'b100110: data <= 20'h00102;
      6'b000111: data <= 20'h08602; 6'b100111: data <= 20'h04002;
      6'b001000: data <= 20'h02310; 6'b101000: data <= 20'h00900;
      6'b001001: data <= 20'h0203B; 6'b101001: data <= 20'h08201;
      6'b001010: data <= 20'h08300; 6'b101010: data <= 20'h02023;
      6'b001011: data <= 20'h04002; 6'b101011: data <= 20'h00303;
      6'b001100: data <= 20'h08201; 6'b101100: data <= 20'h02433;
      6'b001101: data <= 20'h00500; 6'b101101: data <= 20'h00301;
      6'b001110: data <= 20'h04001; 6'b101110: data <= 20'h04004;
      6'b001111: data <= 20'h02500; 6'b101111: data <= 20'h00301;
      6'b010000: data <= 20'h00340; 6'b110000: data <= 20'h00102;
      6'b010001: data <= 20'h00241; 6'b110001: data <= 20'h02137;
      6'b010010: data <= 20'h04002; 6'b110010: data <= 20'h02036;
      6'b010011: data <= 20'h08300; 6'b110011: data <= 20'h00301;
      6'b010100: data <= 20'h08201; 6'b110100: data <= 20'h00102;
      6'b010101: data <= 20'h00500; 6'b110101: data <= 20'h02237;
      6'b010110: data <= 20'h08101; 6'b110110: data <= 20'h04004;
      6'b010111: data <= 20'h00602; 6'b110111: data <= 20'h00304;
      6'b011000: data <= 20'h04003; 6'b111000: data <= 20'h04040;
      6'b011001: data <= 20'h0241E; 6'b111001: data <= 20'h02500;
      6'b011010: data <= 20'h00301; 6'b111010: data <= 20'h02500;
      6'b011011: data <= 20'h00102; 6'b111011: data <= 20'h02500;
      6'b011100: data <= 20'h02122; 6'b111100: data <= 20'h0030D;
      6'b011101: data <= 20'h02021; 6'b111101: data <= 20'h02341;
      6'b011110: data <= 20'h00301; 6'b111110: data <= 20'h08201;
      6'b011111: data <= 20'h00102; 6'b111111: data <= 20'h0400D;
    endcase
end 

assign dout = data;

endmodule
