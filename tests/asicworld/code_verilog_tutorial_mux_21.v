module mux_21 (a,b,sel,y);
  	  	input a, b;
  	  	output y;
  	  	input sel;
  	  	wire y;
  	  	 
  	  	assign y = (sel) ? b : a;
  	  	 
endmodule
