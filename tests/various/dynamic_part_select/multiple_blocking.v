`default_nettype none
module multiple_blocking #(parameter WIDTH=32, SELW=1, CTRLW=$clog2(WIDTH), DINW=2**SELW)
   (input wire             clk,
    input wire [CTRLW-1:0] ctrl,
    input wire [DINW-1:0]  din,
    input wire [SELW-1:0]  sel,
    output reg [WIDTH-1:0] dout);
   
   localparam SLICE = WIDTH/(SELW**2);
   reg [CTRLW:0] 	   a;
   reg [SELW-1:0] 	   b;
   reg [DINW:0] 	   c;
   always @(posedge clk) begin
      a = ctrl + 1;
      b = sel - 1;
      c = ~din;
      dout = dout + 1;
      dout[a*b+:SLICE] = c;
   end
endmodule
