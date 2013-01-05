//-----------------------------------------------------
// Design Name : mux_2to1_gates
// File Name   : mux_2to1_gates.v
// Function    : 2:1 Mux using Gate Primitives
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module mux_2to1_gates(a,b,sel,y);
input a,b,sel;
output y;

wire sel,a_sel,b_sel;

not U_inv (inv_sel,sel);
and U_anda (asel,a,inv_sel),
    U_andb (bsel,b,sel);
or U_or (y,asel,bsel);

endmodule
