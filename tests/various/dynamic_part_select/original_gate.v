`default_nettype none
module original_gate (clk, ctrl, din, sel, dout);
   input wire clk;
   input wire [4:0] ctrl;
   input wire [1:0] din;
   input wire [0:0] sel;
   output reg [31:0] dout;
   always @(posedge clk)
     case (({(ctrl)*(sel)})+(0))
       0:
         dout[31:0] <= din;
       1:
         dout[31:1] <= din;
       2:
         dout[31:2] <= din;
       3:
         dout[31:3] <= din;
       4:
         dout[31:4] <= din;
       5:
         dout[31:5] <= din;
       6:
         dout[31:6] <= din;
       7:
         dout[31:7] <= din;
       8:
         dout[31:8] <= din;
       9:
         dout[31:9] <= din;
       10:
         dout[31:10] <= din;
       11:
         dout[31:11] <= din;
       12:
         dout[31:12] <= din;
       13:
         dout[31:13] <= din;
       14:
         dout[31:14] <= din;
       15:
         dout[31:15] <= din;
       16:
         dout[31:16] <= din;
       17:
         dout[31:17] <= din;
       18:
         dout[31:18] <= din;
       19:
         dout[31:19] <= din;
       20:
         dout[31:20] <= din;
       21:
         dout[31:21] <= din;
       22:
         dout[31:22] <= din;
       23:
         dout[31:23] <= din;
       24:
         dout[31:24] <= din;
       25:
         dout[31:25] <= din;
       26:
         dout[31:26] <= din;
       27:
         dout[31:27] <= din;
       28:
         dout[31:28] <= din;
       29:
         dout[31:29] <= din;
       30:
         dout[31:30] <= din;
       31:
         dout[31:31] <= din;
     endcase
endmodule
