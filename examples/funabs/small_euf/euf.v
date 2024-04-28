function [6:0] ident;
  input [6:0] a;
  begin
    ident = a;
  end
endfunction

module test1 (
  input clk
);

  reg [6:0] v;
  reg [6:0] v2;

`ifdef FORMAL
  always @(posedge clk) begin
    assume property (ident(ident(ident(v)))==v);
    assume property (ident(ident(v))==v);
    assert property (ident(v2)==v2);
  end
`endif
endmodule
