module TECH_NOR18(input [17:0] in, output out);
assign out = ~(|in);
endmodule

module TECH_NOR4(input [3:0] in, output out);
assign out = ~(|in);
endmodule

module TECH_NOR2(input [1:0] in, output out);
assign out = ~(|in);
endmodule
