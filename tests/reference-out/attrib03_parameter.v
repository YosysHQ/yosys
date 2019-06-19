module bar(clk, rst, inp, out);

  parameter _TECHMAP_CELLTYPE_ = "this should be skipped";

  (* this_is_bar_const_param = 1 *)
  parameter BAR_CONST_PARAM = 11;

  (* this_is_bar_real_param = 1 *)
  parameter BAR_REAL_PARAM = 10.5;

  (* this_is_string_param = 1 *)
  parameter BAR_STR_PARAM = "This is a string";

  (* this_is_a_param_with_width = 1*)
  parameter [7:0] BAR_PARAM_WITH_WIDTH = 17;

  input  wire clk;
  input  wire rst;
  input  wire inp;
  output reg  out;

  always @(posedge clk)
    if (rst) out <= 1'd0;
    else     out <= ~inp;

endmodule

module foo(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output wire out;

  bar bar_instance (clk, rst, inp, out);
endmodule

