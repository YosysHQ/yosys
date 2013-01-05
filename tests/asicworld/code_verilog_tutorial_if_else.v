module if_else();

reg dff;
wire clk,din,reset;

always @ (posedge clk)
if (reset) begin
  dff <= 0;
end else  begin
  dff <= din;
end

endmodule
