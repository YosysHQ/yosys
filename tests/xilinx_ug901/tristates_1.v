// Tristate Description Using Combinatorial Always Block
// File: tristates_1.v
//
module tristates_1 (T, I, O);
input  T, I;
output O;
reg    O;

always @(T or I)
begin
  if (~T)
    O = I;
  else
   O = 1'bZ;
end

endmodule
