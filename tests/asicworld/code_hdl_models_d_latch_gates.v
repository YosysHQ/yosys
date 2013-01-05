module d_latch_gates(d,clk,q,q_bar);
input d,clk;
output q, q_bar;

wire n1,n2,n3;

not (n1,d);

nand (n2,d,clk);
nand (n3,n1,clk);

nand (q,q_bar,n2);
nand (q_bar,q,n3);

endmodule
