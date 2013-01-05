//-----------------------------------------------------
// Design Name : rom_using_case
// File Name   : rom_using_case.v
// Function    : ROM using case
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module rom_using_case (
address , // Address input
data    , // Data output
read_en , // Read Enable 
ce        // Chip Enable
);
input [3:0] address;
output [7:0] data;
input read_en;
input ce;

reg [7:0] data ;
       
always @ (ce or read_en or address)
begin
  case (address)
    0 : data = 10;
    1 : data = 55;
    2 : data = 244;
    3 : data = 0;
    4 : data = 1;
    5 : data = 8'hff;
    6 : data = 8'h11;
    7 : data = 8'h1;
    8 : data = 8'h10;
    9 : data = 8'h0;
    10 : data = 8'h10;
    11 : data = 8'h15;
    12 : data = 8'h60;
    13 : data = 8'h90;
    14 : data = 8'h70;
    15 : data = 8'h90;
  endcase
end

endmodule
