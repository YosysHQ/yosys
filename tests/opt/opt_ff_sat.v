module top(
					 input 	clk,
					 input 	a,
					 output b
					 );
  reg 						b_reg;
  initial begin
    b_reg <= 0;
  end

  assign b = b_reg;
  always @(posedge clk) begin
    b_reg <= a && b_reg;
  end
endmodule
