
(* top *)
module top(a, b, y1, y2, y3, y4);
input [3:0] a;
input signed [3:0] b;
output [7:0] y1, y2, y3, y4;

// this version triggers a bug in Icarus Verilog
// submod #(-3'sd1, 3'b111 + 3'b001) foo (a, b, y1, y2, y3, y4);

// this version is handled correctly by Icarus Verilog
submod #(-3'sd1, -3'sd1) foo (a, b, y1, y2, y3, y4);

endmodule

(* gentb_skip *)
module submod(a, b, y1, y2, y3, y4);
parameter c = 0;
parameter [7:0] d = 0;
input [3:0] a, b;
output [7:0] y1, y2, y3, y4;
assign y1 = a;
assign y2 = b;
assign y3 = c;
assign y4 = d;
endmodule

