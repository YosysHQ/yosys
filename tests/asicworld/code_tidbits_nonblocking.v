module nonblocking (clk,a,c);
input clk;
input a;
output c;
 
wire clk;
wire a;
reg c;
reg b;
  
always @ (posedge clk )
begin
  b <= a;
  c <= b;
end
   
endmodule
