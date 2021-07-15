// Taken from: https://github.com/YosysHQ/yosys/issues/2867

`define MIN(x, y) ((x) < (y) ? (x) : (y))
`define CEIL_DIV(x, y) (((x) / (y)) + `MIN((x) % (y), 1))

module pad_msg1 (input logic [`MIN(512*`CEIL_DIV(64, 512), 64)-1:0] x,
                output logic [`MIN(512*`CEIL_DIV(64, 512), 64)-1:0] y);
   assign y[63:0] = x;
endmodule

module pad_msg2 (input logic [((512*`CEIL_DIV(64, 512)) < (64) ? (512*`CEIL_DIV(64,512)) : (64))-1:0] x,
                output logic [((512*`CEIL_DIV(64, 512)) < (64) ? (512*`CEIL_DIV(64,512)) : (64))-1:0] y);
   assign y[63:0] = x;
endmodule

module top(...);
`define add(x) x +
input [3:0] A;
output [3:0] B;
assign B = `add(`add(3)A)A;
endmodule
