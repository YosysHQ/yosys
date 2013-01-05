//-----------------------------------------------------
// Design Name : full_subtracter_gates
// File Name   : full_subtracter_gates.v
// Function    : Full Subtracter Using Gates
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module full_subtracter_gates(x,y,z,difference,borrow);
input x,y,z;
output difference,borrow;

wire inv_x,borrow1,borrow2,borrow3;

not (inv_x,x);
and U_borrow1 (borrow1,inv_x,y),
    U_borrow2 (borrow2,inv_x,z),
    U_borrow3 (borrow3,y,z);

xor U_diff (difference,borrow1,borrow2,borrows);

endmodule
