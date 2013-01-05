//-----------------------------------------------------
// Design Name : mux_using_assign
// File Name   : mux_using_assign.v
// Function    : 2:1 Mux using Assign
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module  mux_using_assign(
din_0      , // Mux first input
din_1      , // Mux Second input
sel        , // Select input
mux_out      // Mux output
);
//-----------Input Ports---------------
input din_0, din_1, sel ;
//-----------Output Ports---------------
output mux_out;
//------------Internal Variables--------
wire  mux_out;
//-------------Code Start-----------------
assign mux_out = (sel) ? din_1 : din_0;

endmodule //End Of Module mux
