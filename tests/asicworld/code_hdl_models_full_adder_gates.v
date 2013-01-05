//-----------------------------------------------------
// Design Name : full_adder_gates
// File Name   : full_adder_gates.v
// Function    : Full Adder Using Gates
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module full_adder_gates(x,y,z,sum,carry);
input x,y,z;
output sum,carry;
wire and1,and2,and3,sum1;

and U_and1 (and1,x,y),
    U_and2 (and2,x,z),
    U_and3 (and3,y,z);
or  U_or   (carry,and1,and2,and3);
xor U_sum (sum,x,y,z);

endmodule
