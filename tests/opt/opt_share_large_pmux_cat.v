module opt_share_test(
  input [15:0]      a,
  input [15:0]      b,
  input [15:0]      c,
  input [2:0]       sel,
  output reg [31:0] res
  );

  always @* begin
    case(sel)
      0: res = {a + b, a};
      1: res = {a - b, b};
      2: res = {a + c, c};
      3: res = {a - c, a};
      4: res = {b, b};
      5: res = {c, c};
      default: res = 32'bx;
    endcase
  end

endmodule
