//-----------------------------------------------------
// Design Name : serial_crc_ccitt
// File Name   : serial_crc.v
// Function    : CCITT Serial CRC
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module serial_crc_ccitt (
clk     ,
reset   ,
enable  ,
init    , 
data_in , 
crc_out
);
//-----------Input Ports---------------
input clk     ;
input reset   ;
input enable  ;
input init    ;
input data_in ;
//-----------Output Ports---------------
output [15:0] crc_out;
//------------Internal Variables--------
reg   [15:0] lfsr;
//-------------Code Start-----------------
assign crc_out = lfsr;
// Logic to CRC Calculation
always @ (posedge clk)
if (reset) begin
  lfsr <= 16'hFFFF;
end else if (enable) begin
  if (init) begin
    lfsr <=  16'hFFFF;
  end else begin
    lfsr[0]  <= data_in ^ lfsr[15];
    lfsr[1]  <= lfsr[0];
    lfsr[2]  <= lfsr[1];
    lfsr[3]  <= lfsr[2];
    lfsr[4]  <= lfsr[3];
    lfsr[5]  <= lfsr[4] ^ data_in ^ lfsr[15];
    lfsr[6]  <= lfsr[5];
    lfsr[7]  <= lfsr[6];
    lfsr[8]  <= lfsr[7];
    lfsr[9]  <= lfsr[8];
    lfsr[10] <= lfsr[9];
    lfsr[11] <= lfsr[10];
    lfsr[12] <= lfsr[11] ^ data_in ^ lfsr[15];
    lfsr[13] <= lfsr[12];
    lfsr[14] <= lfsr[13];
    lfsr[15] <= lfsr[14];
  end
end 

endmodule
