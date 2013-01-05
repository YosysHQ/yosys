module n_out_primitive();

wire out,out_0,out_1,out_2,out_3,out_a,out_b,out_c;
wire in;

// one output Buffer gate
buf u_buf0 (out,in);
// four output Buffer gate 
buf u_buf1 (out_0, out_1, out_2, out_3, in);
// three output Invertor gate 
not u_not0 (out_a, out_b, out_c, in);
 
endmodule
