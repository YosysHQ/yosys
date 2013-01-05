module encoder_4to2_gates (i0,i1,i2,i3,y);
input i0,i1,i2,i3;
output [1:0] y;

or o1 (y[0],i1,i3);
or o2 (y[1],i2,i3);

endmodule
