`default_nettype none
module reversed_gate (clk, ctrl, din, sel, dout);
   input wire clk;
   input wire [4:0] ctrl;
   input wire [15:0] din;
   input wire [3:0]  sel;
   output reg [31:0] dout;
   always @(posedge clk)
     case ((({(32)-((ctrl)*(sel))})+(1))-(2))
       0:
         dout[1:0] <= din;
       1:
         dout[2:1] <= din;
       2:
         dout[3:2] <= din;
       3:
         dout[4:3] <= din;
       4:
         dout[5:4] <= din;
       5:
         dout[6:5] <= din;
       6:
         dout[7:6] <= din;
       7:
         dout[8:7] <= din;
       8:
         dout[9:8] <= din;
       9:
         dout[10:9] <= din;
       10:
         dout[11:10] <= din;
       11:
         dout[12:11] <= din;
       12:
         dout[13:12] <= din;
       13:
         dout[14:13] <= din;
       14:
         dout[15:14] <= din;
       15:
         dout[16:15] <= din;
       16:
         dout[17:16] <= din;
       17:
         dout[18:17] <= din;
       18:
         dout[19:18] <= din;
       19:
         dout[20:19] <= din;
       20:
         dout[21:20] <= din;
       21:
         dout[22:21] <= din;
       22:
         dout[23:22] <= din;
       23:
         dout[24:23] <= din;
       24:
         dout[25:24] <= din;
       25:
         dout[26:25] <= din;
       26:
         dout[27:26] <= din;
       27:
         dout[28:27] <= din;
       28:
         dout[29:28] <= din;
       29:
         dout[30:29] <= din;
       30:
         dout[31:30] <= din;
       31:
         dout[31:31] <= din;
     endcase
endmodule
