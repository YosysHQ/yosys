module peepopt_shiftmul_0 #(parameter N=3, parameter W=3) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output [W-1:0] o);
assign o = i[s*W+:W];
endmodule

module peepopt_shiftmul_1 (output y, input [2:0] w);
assign y = 1'b1 >> (w * (3'b110));
endmodule

module peepopt_muldiv_0(input [1:0] i, output [1:0] o);
wire [3:0] t;
assign t = i * 3;
assign o = t / 3;
endmodule
