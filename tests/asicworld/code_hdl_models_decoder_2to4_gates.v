module decoder_2to4_gates (x,y,f0,f1,f2,f3);
input x,y;
output f0,f1,f2,f3;

wire n1,n2;

not i1 (n1,x);
not i2 (n2,y);
and a1 (f0,n1,n2);
and a2 (f1,n1,y);
and a3 (f2,x,n2);
and a4 (f3,x,y);

endmodule
