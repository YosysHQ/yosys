// Tristate Description Using Concurrent Assignment
// File: tristates_2.v
//
module tristates_2 (T, I, O);
input  T, I;
output O;

assign O = (~T) ? I: 1'bZ;

endmodule
