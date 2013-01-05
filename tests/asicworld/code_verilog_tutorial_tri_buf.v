module tri_buf (a,b,enable);
 input a;
 output b;
 input enable;
 wire b;
 
assign b = (enable) ? a : 1'bz;
  	  	 
endmodule
