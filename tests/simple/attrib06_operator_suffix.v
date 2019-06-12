module bar(clk, rst, inp_a, inp_b, out);
  input  wire clk;
  input  wire rst;
  input  wire [7:0] inp_a;
  input  wire [7:0] inp_b;
  output reg  [7:0] out;

  always @(posedge clk)
    if (rst) out <= 0;
    else     out <= inp_a + (* ripple_adder *) inp_b;

endmodule

module foo(clk, rst, inp_a, inp_b, out);
  input  wire clk;
  input  wire rst;
  input  wire [7:0] inp_a;
  input  wire [7:0] inp_b;
  output wire [7:0] out;

  bar bar_instance (clk, rst, inp_a, inp_b, out);
endmodule

