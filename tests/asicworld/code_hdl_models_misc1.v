module misc1 (a,b,c,d,y);
input a, b,c,d;
output y;

wire net1,net2,net3;

supply1 vdd;
supply0 vss;

// y = !((a+b+c).d)

pmos p1 (vdd,net1,a);
pmos p2 (net1,net2,b);
pmos p3 (net2,y,c);
pmos p4 (vdd,y,d);

nmos n1 (vss,net3,a);
nmos n2 (vss,net3,b);
nmos n3 (vss,net3,c);
nmos n4 (net3,y,d);

endmodule
