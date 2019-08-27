module test(input clk, input [3:0] bar, output [3:0] foo);
  reg [3:0] foo = 0;
  reg [3:0] last_bar = 0;

  always @*
    foo[1:0] <= bar[1:0];

  always @(posedge clk)
    foo[3:2] <= bar[3:2];

  always @(posedge clk)
    last_bar <= bar;

  assert property (foo == {last_bar[3:2], bar[1:0]});
endmodule
