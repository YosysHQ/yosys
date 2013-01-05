module test(out, in1, in2, vin1, vin2, vout1);
output out;
input in1, in2;
input [1:0] vin1;
input [2:0] vin2;
output [3:0] vout1;

assign out = in1 * in2;
assign vout1 = vin1 * vin2;
endmodule
