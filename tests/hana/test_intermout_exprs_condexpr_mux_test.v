module test(in1, in2, out,  vin1, vin2, vin3, vin4, vout1, vout2, en1, ven1, ven2);
input in1, in2, en1, ven1;
input [1:0] ven2;
output out;
input [1:0] vin1,  vin2, vin3, vin4;
output [1:0] vout1, vout2;

assign out = en1 ? in1 : in2;
assign vout1 = ven1 ? vin1 : vin2;
assign vout2 = ven2 ? vin3 : vin4;
endmodule
