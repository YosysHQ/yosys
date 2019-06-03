module bar(clk, rst, inp, out);
  (* this_is_clock = 1 *)
  input  wire clk;
  (* this_is_reset = 1 *)
  input  wire rst;
  input  wire inp;
  (* an_output_register = 1*)
  output reg  out;

  always @(posedge clk)
    if (rst) out <= 1'd0;
    else     out <= ~inp;

endmodule

module foo(clk, rst, inp, out);
  (* this_is_the_master_clock *)
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output wire out;

  bar bar_instance (clk, rst, inp, out);
endmodule

