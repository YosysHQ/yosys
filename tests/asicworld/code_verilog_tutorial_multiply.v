module muliply (a,product);
  	  	input [3:0] a;
  	  	output [4:0] product;
  	  	wire [4:0] product;
  	  	 
  	  	assign product  = a << 1;
  	  	 
endmodule
