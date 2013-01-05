module nand_switch(a,b,out);
input a,b;
output out;

supply0 vss;
supply1 vdd;
wire net1;

pmos p1 (vdd,out,a);
pmos p2 (vdd,out,b);
nmos n1 (vss,net1,a);
nmos n2 (net1,out,b);

endmodule