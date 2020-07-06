function [7:0] do_add;
  input [7:0] inp_a;
  input [7:0] inp_b;

  do_add = inp_a + inp_b;

endfunction

module foo(clk, rst, inp_a, inp_b, out);
  input  wire clk;
  input  wire rst;
  input  wire [7:0] inp_a;
  input  wire [7:0] inp_b;
  output wire [7:0] out;

  always @(posedge clk)
    if (rst) out <= 0;
    else     out <= do_add (* combinational_adder *) (inp_a, inp_b);

endmodule

