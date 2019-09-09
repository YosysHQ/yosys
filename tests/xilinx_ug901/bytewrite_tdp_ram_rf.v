// True-Dual-Port BRAM with Byte-wide Write Enable
//      Read-First mode 
// bytewrite_tdp_ram_rf.v
//

module bytewrite_tdp_ram_rf
 #(
//--------------------------------------------------------------------------
parameter   NUM_COL             =   4,
parameter   COL_WIDTH           =   8,
parameter   ADDR_WIDTH          =  10, 
// Addr  Width in bits : 2 *ADDR_WIDTH = RAM Depth
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
   reg [DATA_WIDTH-1:0]   ram_block [(2**ADDR_WIDTH)-1:0];

   integer                i;
   // Port-A Operation
   always @ (posedge clkA) begin
      if(enaA) begin
         for(i=0;i<NUM_COL;i=i+1) begin
            if(weA[i]) begin
               ram_block[addrA][i*COL_WIDTH +: COL_WIDTH] <= dinA[i*COL_WIDTH +: COL_WIDTH];
            end
         end
         doutA <= ram_block[addrA];  
      end
   end

   // Port-B Operation:
   always @ (posedge clkB) begin
      if(enaB) begin
         for(i=0;i<NUM_COL;i=i+1) begin
            if(weB[i]) begin
               ram_block[addrB][i*COL_WIDTH +: COL_WIDTH] <= dinB[i*COL_WIDTH +: COL_WIDTH];
            end
         end     
         
         doutB <= ram_block[addrB];  
      end
   end

endmodule // bytewrite_tdp_ram_rf
