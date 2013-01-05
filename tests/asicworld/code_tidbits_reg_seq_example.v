module reg_seq_example( clk, reset, d, q);
input clk, reset, d;
output q;
  
reg   q;
wire clk, reset, d;

always @ (posedge clk or posedge reset)
if (reset) begin
  q <= 1'b0;
end else begin
  q <= d;
end

endmodule
