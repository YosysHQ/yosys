`default_nettype none
module forloop_select_gate (clk, ctrl, din, en, dout);
      input wire clk;
      input wire [3:0] ctrl;
      input wire [15:0] din;
      input wire en;
      output reg [15:0] dout;
      reg [4:0] sel;
      always @(posedge clk)
        case (|(en))
          1'b 1:
            begin
              case (({(ctrl)*(0)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 00001)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 00010)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 00011)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 00100)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 00101)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 00110)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 00111)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 01000)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 01001)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 01010)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 01011)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 01100)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 01101)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 01110)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              case (({(ctrl)*(5'b 01111)})+(0))
                0:
                  dout[0:0] <= din;
                1:
                  dout[1:1] <= din;
                2:
                  dout[2:2] <= din;
                3:
                  dout[3:3] <= din;
                4:
                  dout[4:4] <= din;
                5:
                  dout[5:5] <= din;
                6:
                  dout[6:6] <= din;
                7:
                  dout[7:7] <= din;
                8:
                  dout[8:8] <= din;
                9:
                  dout[9:9] <= din;
                10:
                  dout[10:10] <= din;
                11:
                  dout[11:11] <= din;
                12:
                  dout[12:12] <= din;
                13:
                  dout[13:13] <= din;
                14:
                  dout[14:14] <= din;
                15:
                  dout[15:15] <= din;
              endcase
              sel = 5'b 10000;
            end
        endcase
    endmodule
