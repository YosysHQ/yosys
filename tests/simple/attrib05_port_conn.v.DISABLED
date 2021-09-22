module attrib05_bar(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output reg  out;

  always @(posedge clk)
    if (rst) out <= 1'd0;
    else     out <= ~inp;

endmodule

module attrib05_foo(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output wire out;

  attrib05_bar bar_instance ( (* clock_connected *) clk, rst, (* this_is_the_input *) inp, out);
endmodule

