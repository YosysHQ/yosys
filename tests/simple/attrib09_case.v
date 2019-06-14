module bar(clk, rst, inp, out);
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

module foo(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire [1:0] inp;
  output wire [1:0] out;

  bar bar_instance (clk, rst, inp, out);
endmodule

