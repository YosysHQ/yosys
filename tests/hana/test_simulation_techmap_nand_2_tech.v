module TECH_NAND18(input [17:0] in, output out);
assign out = ~(&in);
endmodule

module TECH_NAND4(input [3:0] in, output out);
assign out = ~(&in);
endmodule

module TECH_NAND2(input [1:0] in, output out);
assign out = ~(&in);
endmodule
