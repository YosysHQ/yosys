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
    dpram256x36 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_256x36_WCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 1;
  parameter [0:0] CLKPOL3 = 0;

  input CLK2;
  input CLK3;
  input [0:7] A1ADDR;
  input A1EN;
  output [0:35] A1DATA;
  input [0:7] B1ADDR;
  input B1EN;
  input [0:35] B1DATA;

  generate
    dpram256x36_wclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_256x36_RCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 0;
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
    dpram256x36_rclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_256x36_RWCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 0;
  parameter [0:0] CLKPOL3 = 0;

  input CLK2;
  input CLK3;
  input [0:7] A1ADDR;
  input A1EN;
  output [0:35] A1DATA;
  input [0:7] B1ADDR;
  input B1EN;
  input [0:35] B1DATA;

  generate
    dpram256x36_rwclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_512x18 (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 1;
  parameter [0:0] CLKPOL3 = 1;

  input CLK2;
  input CLK3;
  input [0:8] A1ADDR;
  input A1EN;
  output [0:17] A1DATA;
  input [0:8] B1ADDR;
  input B1EN;
  input [0:17] B1DATA;

  generate
    dpram512x18 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_512x18_WCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 1;
  parameter [0:0] CLKPOL3 = 0;

  input CLK2;
  input CLK3;
  input [0:8] A1ADDR;
  input A1EN;
  output [0:17] A1DATA;
  input [0:8] B1ADDR;
  input B1EN;
  input [0:17] B1DATA;

  generate
    dpram512x18_wclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_512x18_RCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 0;
  parameter [0:0] CLKPOL3 = 1;

  input CLK2;
  input CLK3;
  input [0:8] A1ADDR;
  input A1EN;
  output [0:17] A1DATA;
  input [0:8] B1ADDR;
  input B1EN;
  input [0:17] B1DATA;

  generate
    dpram512x18_rclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_512x18_RWCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 0;
  parameter [0:0] CLKPOL3 = 0;

  input CLK2;
  input CLK3;
  input [0:8] A1ADDR;
  input A1EN;
  output [0:17] A1DATA;
  input [0:8] B1ADDR;
  input B1EN;
  input [0:17] B1DATA;

  generate
    dpram512x18_rwclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_1024x9 (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 1;
  parameter [0:0] CLKPOL3 = 1;

  input CLK2;
  input CLK3;
  input [0:9] A1ADDR;
  input A1EN;
  output [0:8] A1DATA;
  input [0:9] B1ADDR;
  input B1EN;
  input [0:8] B1DATA;

  generate
    dpram1024x9 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_1024x9_WCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 1;
  parameter [0:0] CLKPOL3 = 0;

  input CLK2;
  input CLK3;
  input [0:9] A1ADDR;
  input A1EN;
  output [0:8] A1DATA;
  input [0:9] B1ADDR;
  input B1EN;
  input [0:8] B1DATA;

  generate
    dpram1024x9_wclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_1024x9_RCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 0;
  parameter [0:0] CLKPOL3 = 1;

  input CLK2;
  input CLK3;
  input [0:9] A1ADDR;
  input A1EN;
  output [0:8] A1DATA;
  input [0:9] B1ADDR;
  input B1EN;
  input [0:8] B1DATA;

  generate
    dpram1024x9_rclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_1024x9_RWCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 0;
  parameter [0:0] CLKPOL3 = 0;

  input CLK2;
  input CLK3;
  input [0:9] A1ADDR;
  input A1EN;
  output [0:8] A1DATA;
  input [0:9] B1ADDR;
  input B1EN;
  input [0:8] B1DATA;

  generate
    dpram1024x9_rwclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_2048x4 (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 1;
  parameter [0:0] CLKPOL3 = 1;

  input CLK2;
  input CLK3;
  input [0:10] A1ADDR;
  input A1EN;
  output [0:3] A1DATA;
  input [0:10] B1ADDR;
  input B1EN;
  input [0:3] B1DATA;

  generate
    dpram2048x4 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_2048x4_WCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 1;
  parameter [0:0] CLKPOL3 = 0;

  input CLK2;
  input CLK3;
  input [0:10] A1ADDR;
  input A1EN;
  output [0:3] A1DATA;
  input [0:10] B1ADDR;
  input B1EN;
  input [0:3] B1DATA;

  generate
    dpram2048x4_wclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_2048x4_RCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 0;
  parameter [0:0] CLKPOL3 = 1;

  input CLK2;
  input CLK3;
  input [0:10] A1ADDR;
  input A1EN;
  output [0:3] A1DATA;
  input [0:10] B1ADDR;
  input B1EN;
  input [0:3] B1DATA;

  generate
    dpram2048x4_rclkn 
      _TECHMAP_REPLACE_ (
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

//-----------------------------
// This is a true dual-port RAM
// BUT without support on Byte-Write-Enable
// Due to limited support from Yosys
//-----------------------------
module \$__FLEX_TDPRAM_2048x4_RWCLKN (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

  parameter [0:0] CLKPOL2 = 0;
  parameter [0:0] CLKPOL3 = 0;

  input CLK2;
  input CLK3;
  input [0:10] A1ADDR;
  input A1EN;
  output [0:3] A1DATA;
  input [0:10] B1ADDR;
  input B1EN;
  input [0:3] B1DATA;

  generate
    dpram2048x4_rwclkn 
      _TECHMAP_REPLACE_ (
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
