function [0:0] ident;
  input [0:0] a;
  begin
    ident = a;
  end
endfunction

module euf (
  input clk
);

  reg v;
  reg v2;

`ifdef FORMAL
  always @(posedge clk) begin
    assert property (ident(v2)==v2);
  end
`endif
endmodule
