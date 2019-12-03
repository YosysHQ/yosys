module EFX_LUT4(
   output O, 
   input I0,
   input I1,
   input I2,
   input I3
);
	parameter LUTMASK = 16'h0000;

	wire [7:0] s3 = I3 ? LUTMASK[15:8] : LUTMASK[7:0];
	wire [3:0] s2 = I2 ?      s3[ 7:4] :      s3[3:0];
	wire [1:0] s1 = I1 ?      s2[ 3:2] :      s2[1:0];
	assign O = I0 ? s1[1] : s1[0];	   
endmodule

module EFX_ADD(
   output O,
   output CO,
   input I0,
   input I1,
   input CI
);
   parameter I0_POLARITY   = 1;
   parameter I1_POLARITY   = 1;

   wire i0;
   wire i1;

   assign i0 = I0_POLARITY ? I0 : ~I0;
   assign i1 = I1_POLARITY ? I1 : ~I1;

   assign {CO, O} = i0 + i1 + CI;
endmodule

module EFX_FF(
   output reg Q,
   input D,
   input CE,
   input CLK,
   input SR
);
   parameter CLK_POLARITY = 1;
   parameter CE_POLARITY = 1;
   parameter SR_POLARITY = 1;
   parameter SR_SYNC = 0;
   parameter SR_VALUE = 0;
   parameter SR_SYNC_PRIORITY = 0;
   parameter D_POLARITY = 1;

   wire clk;
   wire ce;
   wire sr;
   wire d;
   wire prio;
   wire sync;
   wire async;

   assign clk = CLK_POLARITY ? CLK : ~CLK;
   assign ce = CE_POLARITY ? CE : ~CE;
   assign sr = SR_POLARITY ? SR : ~SR;
   assign d = D_POLARITY ? D : ~D;

	initial Q = 1'b0;

   generate
   	if (SR_SYNC == 1) 
      begin
         if (SR_SYNC_PRIORITY == 1) 
         begin
            always @(posedge clk)
               if (sr)
                  Q <= SR_VALUE;
               else if (ce)
                  Q <= d;
         end
         else
         begin
            always @(posedge clk)
               if (ce)
               begin
                  if (sr)
                     Q <= SR_VALUE;
                  else
                     Q <= d;
               end
         end
      end
      else
      begin
         always @(posedge clk or posedge sr)
            if (sr)
               Q <= SR_VALUE;
            else if (ce)
               Q <= d;
         
      end
   endgenerate
endmodule

module EFX_GBUFCE(
   input CE,
   input I,
   output O
);
   parameter CE_POLARITY = 1'b1;

   wire ce;
   assign ce = CE_POLARITY ? CE : ~CE;
   
   assign O = I & ce;
   
endmodule

module EFX_RAM_5K(
   input [WRITE_WIDTH-1:0] WDATA,
   input [WRITE_ADDR_WIDTH-1:0] WADDR,
   input WE, 
   input WCLK,
   input WCLKE, 
   output [READ_WIDTH-1:0] RDATA, 
   input [READ_ADDR_WIDTH-1:0] RADDR,
   input RE, 
   input RCLK
);
   parameter READ_WIDTH = 20;
   parameter WRITE_WIDTH = 20;
   parameter OUTPUT_REG = 1'b0;
   parameter RCLK_POLARITY  = 1'b1;
   parameter RE_POLARITY    = 1'b1;
   parameter WCLK_POLARITY  = 1'b1;
   parameter WE_POLARITY    = 1'b1;
   parameter WCLKE_POLARITY = 1'b1;
   parameter WRITE_MODE = "READ_FIRST";
   parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_10 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_11 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_12 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
   parameter INIT_13 = 256'h0000000000000000000000000000000000000000000000000000000000000000;

   localparam READ_ADDR_WIDTH = 
			    (READ_WIDTH == 16) ? 8 :  // 256x16
			    (READ_WIDTH == 8)  ? 9 :  // 512x8
			    (READ_WIDTH == 4)  ? 10 : // 1024x4
			    (READ_WIDTH == 2)  ? 11 : // 2048x2
			    (READ_WIDTH == 1)  ? 12 : // 4096x1
			    (READ_WIDTH == 20) ? 8 :  // 256x20
			    (READ_WIDTH == 10) ? 9 :  // 512x10
			    (READ_WIDTH == 5)  ? 10 : -1; // 1024x5
   
   localparam WRITE_ADDR_WIDTH = 
			    (WRITE_WIDTH == 16) ? 8 :  // 256x16
			    (WRITE_WIDTH == 8)  ? 9 :  // 512x8
			    (WRITE_WIDTH == 4)  ? 10 : // 1024x4
			    (WRITE_WIDTH == 2)  ? 11 : // 2048x2
			    (WRITE_WIDTH == 1)  ? 12 : // 4096x1
			    (WRITE_WIDTH == 20) ? 8 :  // 256x20
			    (WRITE_WIDTH == 10) ? 9 :  // 512x10
			    (WRITE_WIDTH == 5)  ? 10 : -1; // 1024x5
   
endmodule