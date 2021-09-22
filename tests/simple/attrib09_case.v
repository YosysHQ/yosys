module attrib09_bar(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire [1:0] inp;
  output reg  [1:0] out;

  always @(inp)
    (* full_case, parallel_case *)
    case(inp)
      2'd0: out <= 2'd3;
      2'd1: out <= 2'd2;
      2'd2: out <= 2'd1;
      2'd3: out <= 2'd0;
    endcase

endmodule

module attrib09_foo(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire [1:0] inp;
  output wire [1:0] out;

  attrib09_bar bar_instance (clk, rst, inp, out);
endmodule

