`default_nettype none
module multiple_blocking_gate (clk, ctrl, din, sel, dout);
   input wire clk;
   input wire [4:0] ctrl;
   input wire [1:0] din;
   input wire [0:0] sel;
   output reg [31:0] dout;
   reg [5:0] 	     a;
   reg [0:0] 	     b;
   reg [2:0] 	     c;
   always @(posedge clk)
     begin
        a = (ctrl)+(1);
        b = (sel)-(1);
        c = ~(din);
        dout = (dout)+(1);
        case (({(a)*(b)})+(0))
          0:
            dout[31:0] = c;
          1:
            dout[31:1] = c;
          2:
            dout[31:2] = c;
          3:
            dout[31:3] = c;
          4:
            dout[31:4] = c;
          5:
            dout[31:5] = c;
          6:
            dout[31:6] = c;
          7:
            dout[31:7] = c;
          8:
            dout[31:8] = c;
          9:
            dout[31:9] = c;
          10:
            dout[31:10] = c;
          11:
            dout[31:11] = c;
          12:
            dout[31:12] = c;
          13:
            dout[31:13] = c;
          14:
            dout[31:14] = c;
          15:
            dout[31:15] = c;
          16:
            dout[31:16] = c;
          17:
            dout[31:17] = c;
          18:
            dout[31:18] = c;
          19:
            dout[31:19] = c;
          20:
            dout[31:20] = c;
          21:
            dout[31:21] = c;
          22:
            dout[31:22] = c;
          23:
            dout[31:23] = c;
          24:
            dout[31:24] = c;
          25:
            dout[31:25] = c;
          26:
            dout[31:26] = c;
          27:
            dout[31:27] = c;
          28:
            dout[31:28] = c;
          29:
            dout[31:29] = c;
          30:
            dout[31:30] = c;
          31:
            dout[31:31] = c;
        endcase
     end
endmodule
