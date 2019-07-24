module bar(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output reg  out;

  (* this_is_a_prescaler *)
  reg [7:0] counter;

  (* temp_wire *)
  wire out_val;

  always @(posedge clk)
    counter <= counter + 1;

  assign out_val = inp ^ counter[4];

  always @(posedge clk)
    if (rst) out <= 1'd0;
    else     out <= out_val;

endmodule

module foo(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire inp;
  output wire out;

  bar bar_instance (clk, rst, inp, out);
endmodule

