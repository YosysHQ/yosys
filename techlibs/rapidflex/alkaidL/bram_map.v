//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_256x36 (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 1;
  parameter [0:0] CLKPOL3 = 1;

  input CLK2;
  input CLK3;
  input [0:7] A1ADDR;
  input A1EN;
  output [0:35] A1DATA;
  input [0:7] B1ADDR;
  input B1EN;
  input [0:35] B1DATA;

  generate
    tdpram_core #(
      .ADDR_WIDTH(8),
      .BYTE_WIDTH(9),
      .NUM_BYTES(4),
    ) _TECHMAP_REPLACE_ (
      .rclk_i     (CLK2),
      .wclk_i     (CLK3),
      .bwen_ni    (|1),
      .wen_ni     (B1EN),
      .waddr_i   (B1ADDR),
      .data_i     (B1DATA),
      .ren_ni     (A1EN),
      .raddr_i    (A1ADDR),
      .q_o        (A1DATA) 
     );
  endgenerate

endmodule
