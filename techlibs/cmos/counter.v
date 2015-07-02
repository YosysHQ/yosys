module counter (clk, rst, en, count);

   input clk, rst, en;
   output reg [2:0] count;

   always @(posedge clk)
      if (rst)
         count <= 3'd0;
      else if (en)
         count <= count + 3'd1;

endmodule
