module attrib08_bar(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output reg  out;

  always @(posedge clk)
    if (rst) out <= 1'd0;
    else     out <= ~inp;

endmodule

module attrib08_foo(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output wire out;

  (* my_module_instance = 99 *)
  attrib08_bar bar_instance (clk, rst, inp, out);
endmodule

