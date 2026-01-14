module bottom(input clk, input wire [1:0] i, output reg [1:0] q);
  reg [1:0] q1;
  always @(posedge clk) begin
     q1 <= i;
     q <= q1;
  end
endmodule

module top(input clk, input wire [1:0] i, output wire [1:0] q);
  wire [1:0] q1;
  bottom u1 (.clk(clk), .i(i), .q(q1));
  assign q = ~q1;
endmodule
