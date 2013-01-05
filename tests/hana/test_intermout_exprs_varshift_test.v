module test(vin0, vout0);
input [2:0] vin0;
output reg [7:0] vout0;

wire [7:0] myreg0, myreg1, myreg2;
integer i;
assign myreg0 = vout0 << vin0;

assign myreg1 = myreg2 >> i;
endmodule
