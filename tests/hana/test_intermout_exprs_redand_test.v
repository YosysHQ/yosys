module test(output out, input [1:0] vin, output out1, input [3:0] vin1);

assign out = &vin;
assign out1 = &vin1;
endmodule
