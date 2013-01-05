//-----------------------------------------------------
// Design Name : half_adder_gates
// File Name   : half_adder_gates.v
// Function    : CCITT Serial CRC
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module half_adder_gates(x,y,sum,carry);
input x,y;
output sum,carry;

and U_carry (carry,x,y);
xor U_sum (sum,x,y);

endmodule
