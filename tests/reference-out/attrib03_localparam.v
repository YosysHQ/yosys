module bar(clk, rst, inp, out);

  (* this_is_bar_const_localparam = 1 *)
  localparam BAR_CONST_LOCALPARAM = 11;

  (* this_is_bar_real_localparam = 1 *)
  localparam BAR_REAL_LOCALPARAM = 10.5;

  (* this_is_string_localparam = 1 *)
  localparam BAR_STR_LOCALPARAM = "This is a string";

  (* this_is_a_localparam_with_width = 1*)
  localparam [7:0] BAR_LOCALPARAM_WITH_WIDTH = 17;

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

