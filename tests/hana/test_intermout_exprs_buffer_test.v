module buffer(in, out, vin, vout);
input  in;
output out;
input [1:0] vin;
output [1:0] vout;

assign out = in;
assign vout = vin;
endmodule
