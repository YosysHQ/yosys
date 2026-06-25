// hierarchy; proc;; simplemap
module gold(
  input clk,
  input [1:0] in,
  output reg [1:0] out
);
  reg [0:1] r;

  always @(posedge clk) begin
    out <= r;
    r <= in;
  end
endmodule
