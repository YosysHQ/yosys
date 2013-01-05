module test(output out, input in, output [31:0] vout, input [31:0] vin);

assign out = -in;
assign vout = -vin;
endmodule
