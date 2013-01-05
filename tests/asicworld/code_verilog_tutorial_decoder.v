module decoder (in,out);
input [2:0] in;
output [7:0] out;
wire [7:0] out;
assign out  =  	(in == 3'b000 ) ? 8'b0000_0001 : 
(in == 3'b001 ) ? 8'b0000_0010 : 
(in == 3'b010 ) ? 8'b0000_0100 : 
(in == 3'b011 ) ? 8'b0000_1000 : 
(in == 3'b100 ) ? 8'b0001_0000 : 
(in == 3'b101 ) ? 8'b0010_0000 : 
(in == 3'b110 ) ? 8'b0100_0000 : 
(in == 3'b111 ) ? 8'b1000_0000 : 8'h00;
  	  	 
endmodule
