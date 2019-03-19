`default_nettype none

module hierdefparam_top(input [7:0] A, output [7:0] Y);
  generate begin:foo
    hierdefparam_a mod_a(.A(A), .Y(Y));
  end endgenerate
  defparam foo.mod_a.bar[0].mod_b.addvalue = 42;
  defparam foo.mod_a.bar[1].mod_b.addvalue = 43;
endmodule

module hierdefparam_a(input [7:0] A, output [7:0] Y);
  genvar i;
  generate
    for (i = 0; i < 2; i=i+1) begin:bar
      wire [7:0] a, y;
      hierdefparam_b mod_b(.A(a), .Y(y));
    end
  endgenerate
  assign bar[0].a = A, bar[1].a = bar[0].y, Y = bar[1].y;
endmodule

module hierdefparam_b(input [7:0] A, output [7:0] Y);
  parameter [7:0] addvalue = 44;
  assign Y = A + addvalue;
endmodule
