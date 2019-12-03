module bar(clk, rst, inp, out);

  (* bus_width *)
  parameter WIDTH = 2;

  (* an_attribute_on_localparam = 55 *)
  localparam INCREMENT = 5;

  input  wire clk;
  input  wire rst;
  input  wire [WIDTH-1:0] inp;
  output reg  [WIDTH-1:0] out;

  always @(posedge clk)
    if (rst) out <= 0;
    else     out <= inp + INCREMENT;

endmodule

module foo(clk, rst, inp, out);
  input  wire clk;
  input  wire rst;
  input  wire [7:0] inp;
  output wire [7:0] out;

  bar # (.WIDTH(8)) bar_instance (clk, rst, inp, out);
endmodule

