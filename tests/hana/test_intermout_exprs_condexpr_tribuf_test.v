module test(in, out, en, vin1, vout1, en1);
input in, en, en1;
output out;
input [1:0] vin1;
output [1:0] vout1;

assign out = en ? in : 1'bz;
assign vout1 = en1 ? vin1 : 2'bzz;
endmodule
