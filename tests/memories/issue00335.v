// expect-wr-ports 1
// expect-rd-ports 1
// expect-rd-clk \clk

module ram2 (input clk,
             input             sel,
             input             we, 
             input [SIZE-1:0]  adr, 
             input [63:0]      dat_i, 
             output reg [63:0] dat_o);
   parameter  SIZE = 5; // Address size

   reg [63:0] mem [0:(1 << SIZE)-1];
   integer    i;

   initial begin
      for (i = 0; i < (1<<SIZE) - 1; i = i + 1)
        mem[i] <= 0;
   end
   
   always @(posedge clk)
     if (sel) begin
       if (~we)
         dat_o <= mem[adr];
       else
         mem[adr] <= dat_i;
     end
endmodule
