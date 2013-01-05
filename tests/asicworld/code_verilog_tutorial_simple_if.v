module simple_if();

reg latch;
wire enable,din;

always @ (enable or din)
if (enable) begin
  latch <= din;
end  

endmodule
