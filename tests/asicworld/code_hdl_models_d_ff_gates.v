module d_ff_gates(d,clk,q,q_bar);
input d,clk;
output q, q_bar;

wire n1,n2,n3,q_bar_n;
wire cn,dn,n4,n5,n6;

// First Latch
not (n1,d);

nand (n2,d,clk);
nand (n3,n1,clk);

nand (dn,q_bar_n,n2);
nand (q_bar_n,dn,n3);

// Second Latch
not (cn,clk);

not (n4,dn);

nand (n5,dn,cn);
nand (n6,n4,cn);

nand (q,q_bar,n5);
nand (q_bar,q,n6);


endmodule
