// Lower $fa to word-level $xor/$and/$or instead of gates.
//
// Consumers that model word-level operators (rather than mapped gates) need the
// carry-save compressors emitted by arith_tree to stay at operator granularity,
// so a full adder becomes wide bitwise ops rather than a bit-blasted cloud.

(* techmap_celltype = "$fa" *)
module _fa_wordlevel_ (A, B, C, X, Y);

parameter WIDTH = 1;

input [WIDTH-1:0] A, B, C;
output [WIDTH-1:0] X, Y;

wire [WIDTH-1:0] t1 = A ^ B;

assign Y = t1 ^ C;  // sum
assign X = (A & B) | (C & t1);  // carry-out (majority)

endmodule
