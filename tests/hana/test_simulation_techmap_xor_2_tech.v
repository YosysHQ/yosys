module TECH_XOR5(input [4:0] in, output out);
assign out = in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4];
endmodule
module TECH_XOR2(input [1:0] in, output out);
assign out = in[0] ^ in[1];
endmodule
