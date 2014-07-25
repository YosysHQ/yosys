module undef_eqx_nex(y);
output [7:0] y;
assign y[0] = 0/0;
assign y[1] = 0/1;
assign y[2] = 0/0 ==  32'bx;
assign y[3] = 0/0 !=  32'bx;
assign y[4] = 0/0 === 32'bx;
assign y[5] = 0/0 !== 32'bx;
assign y[6] = 0/1 === 32'bx;
assign y[7] = 0/1 !== 32'bx;
endmodule
