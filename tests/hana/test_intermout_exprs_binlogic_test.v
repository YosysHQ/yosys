module test(in1, in2, vin1, vin2, out, vout, vin3, vin4, vout1 );
input in1, in2;
input [1:0] vin1;
input [3:0] vin2;
input [1:0] vin3;
input [3:0] vin4;
output vout, vout1;
output out;

assign out = in1 && in2;
assign vout = vin1 && vin2;
assign vout1 = vin3 || vin4;
endmodule
