module flif_flop (clk,reset, q, d);
input clk, reset, d;
output q;
reg q;
  	  	 
always @ (posedge clk )
begin
  if (reset == 1) begin
    q <= 0;
  end else begin
    q <= d;
  end
end
  	  	 
endmodule
