`default_nettype none
module reset_test_gate (clk, reset, ctrl, din, sel, dout);
   input wire clk;
   input wire reset;
   input wire [4:0] ctrl;
   input wire [1:0] din;
   input wire [0:0] sel;
   output reg [31:0] dout;
   reg [1:0] 	     i;
   wire [0:0] 	     rval;
   assign rval = {reset, 1'b0 };
   always @(posedge clk)
     begin
        case (|(reset))
          1'b 1:
            begin
               case (({(0)*(rval)})+(0))
                 0:
                   dout[31:0] <= 57005;
                 1:
                   dout[31:1] <= 57005;
                 2:
                   dout[31:2] <= 57005;
                 3:
                   dout[31:3] <= 57005;
                 4:
                   dout[31:4] <= 57005;
                 5:
                   dout[31:5] <= 57005;
                 6:
                   dout[31:6] <= 57005;
                 7:
                   dout[31:7] <= 57005;
                 8:
                   dout[31:8] <= 57005;
                 9:
                   dout[31:9] <= 57005;
                 10:
                   dout[31:10] <= 57005;
                 11:
                   dout[31:11] <= 57005;
                 12:
                   dout[31:12] <= 57005;
                 13:
                   dout[31:13] <= 57005;
                 14:
                   dout[31:14] <= 57005;
                 15:
                   dout[31:15] <= 57005;
                 16:
                   dout[31:16] <= 57005;
                 17:
                   dout[31:17] <= 57005;
                 18:
                   dout[31:18] <= 57005;
                 19:
                   dout[31:19] <= 57005;
                 20:
                   dout[31:20] <= 57005;
                 21:
                   dout[31:21] <= 57005;
                 22:
                   dout[31:22] <= 57005;
                 23:
                   dout[31:23] <= 57005;
                 24:
                   dout[31:24] <= 57005;
                 25:
                   dout[31:25] <= 57005;
                 26:
                   dout[31:26] <= 57005;
                 27:
                   dout[31:27] <= 57005;
                 28:
                   dout[31:28] <= 57005;
                 29:
                   dout[31:29] <= 57005;
                 30:
                   dout[31:30] <= 57005;
                 31:
                   dout[31:31] <= 57005;
               endcase
               i = 1;
            end
        endcase
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
     end
endmodule
