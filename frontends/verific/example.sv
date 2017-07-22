module top (
  input clk, rst,
  output reg [3:0] cnt
);
  initial cnt = 0;

  always @(posedge clk) begin
    if (rst)
      cnt <= 0;
    else
      cnt <= cnt + 4'd 1;
  end

  always @(posedge clk) begin
    assume (cnt != 10);
    assert (cnt != 15);
  end
endmodule
