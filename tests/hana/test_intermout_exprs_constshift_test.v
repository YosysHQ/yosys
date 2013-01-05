module test(in, out, vin, vout, vin1, vout1, vin2, vout2);

input in;
input [3:0] vin, vin1, vin2;
output [3:0] vout, vout1, vout2;
output out;

assign out = in << 1;
assign vout = vin << 2;
assign vout1 = vin1 >> 2;
assign vout2 = vin2 >>> 2;
endmodule
