module test(output out, input in, output [1:0] vout, input [1:0] vin);

assign out = ~in;
assign vout = ~vin;
endmodule
