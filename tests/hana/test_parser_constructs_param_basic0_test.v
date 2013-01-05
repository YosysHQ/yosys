module test #( parameter v2kparam = 5)
(in, out, io, vin, vout, vio);
input in;
output out;
inout io;
input [3:0] vin;
output [v2kparam:0] vout;
inout [0:3] vio;
parameter myparam = 10;
endmodule
