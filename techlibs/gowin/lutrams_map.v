module \$__GW1NR_RAM16S4 (CLK1, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 4;
	parameter CFG_DBITS = 4;

        parameter [63:0] INIT = 64'bx;
	input CLK1;

	input  [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;   
        input                  A1EN;

	input  [CFG_ABITS-1:0] B1ADDR;
	input  [CFG_DBITS-1:0] B1DATA;
	input  B1EN;

        `include "brams_init3.vh"

  RAM16S4
   #(.INIT_0(INIT_0),
     .INIT_1(INIT_1),
     .INIT_2(INIT_2),
     .INIT_3(INIT_3))
   _TECHMAP_REPLACE_
     (.AD(B1ADDR),
      .DI(B1DATA),
      .DO(A1DATA),
      .CLK(CLK1),
      .WRE(B1EN));

	
endmodule
