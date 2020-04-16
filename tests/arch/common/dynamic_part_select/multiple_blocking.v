module multiple_blocking #(parameter WIDTH=256, SELW=2)
   (input 	         clk ,
    input [9:0] 	 ctrl ,
    input [15:0] 	 din ,
    input [SELW-1:0] 	 sel ,
    output reg [WIDTH:0] dout);

   localparam SLICE = WIDTH/(SELW**2);
   reg [9:0] 		 a;
   reg [SELW-1:0] 	 b;
   reg [15:0] 		 c;
   always @(posedge clk) begin
      a = ctrl + 1;
      b = sel - 1;
      c = ~din;
      dout = dout + 1;
      dout[a*b+:SLICE] = c;
   end
endmodule
