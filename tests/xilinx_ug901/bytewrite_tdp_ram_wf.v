// True-Dual-Port BRAM with Byte-wide Write Enable
//      Write-First mode
// File: HDL_Coding_Techniques/rams/bytewrite_tdp_ram_wf.v
//
// ByteWide Write Enable, - WRITE_FIRST mode template - Vivado recomended
module bytewrite_tdp_ram_wf
  #(
    //----------------------------------------------------------------------
parameter   NUM_COL         =   4,
parameter   COL_WIDTH       =   8,
parameter   ADDR_WIDTH      =  10, 
// Addr  Width in bits : 2**ADDR_WIDTH = RAM Depth
parameter   DATA_WIDTH      =  NUM_COL*COL_WIDTH  // Data  Width in bits
    //----------------------------------------------------------------------
    ) (
       input clkA,
       input enaA, 
       input [NUM_COL-1:0] weA,
       input [ADDR_WIDTH-1:0] addrA,
       input [DATA_WIDTH-1:0] dinA,
       output reg [DATA_WIDTH-1:0] doutA,
       
       input clkB,
       input enaB,
       input [NUM_COL-1:0] weB,
       input [ADDR_WIDTH-1:0] addrB,
       input [DATA_WIDTH-1:0] dinB,
       output reg [DATA_WIDTH-1:0] doutB
       );
   
   
   // Core Memory  
   reg [DATA_WIDTH-1:0]            ram_block [(2**ADDR_WIDTH)-1:0];
   
   // Port-A Operation
   generate
      genvar                       i;
      for(i=0;i<NUM_COL;i=i+1) begin
         always @ (posedge clkA) begin
            if(enaA) begin
               if(weA[i]) begin
                  ram_block[addrA][i*COL_WIDTH +: COL_WIDTH] <= dinA[i*COL_WIDTH +: COL_WIDTH];
                  doutA[i*COL_WIDTH +: COL_WIDTH]  <= dinA[i*COL_WIDTH +: COL_WIDTH] ;
               end else begin
                  doutA[i*COL_WIDTH +: COL_WIDTH]  <= ram_block[addrA][i*COL_WIDTH +: COL_WIDTH] ;
               end
            end
         end
      end
   endgenerate
   
   // Port-B Operation:
   generate
      for(i=0;i<NUM_COL;i=i+1) begin
         always @ (posedge clkB) begin
            if(enaB) begin
               if(weB[i]) begin
                  ram_block[addrB][i*COL_WIDTH +: COL_WIDTH] <= dinB[i*COL_WIDTH +: COL_WIDTH];
                  doutB[i*COL_WIDTH +: COL_WIDTH]  <= dinB[i*COL_WIDTH +: COL_WIDTH] ;
               end else begin 
                  doutB[i*COL_WIDTH +: COL_WIDTH]  <= ram_block[addrB][i*COL_WIDTH +: COL_WIDTH] ;
               end
            end     
         end
      end
   endgenerate
   
endmodule // bytewrite_tdp_ram_wf
