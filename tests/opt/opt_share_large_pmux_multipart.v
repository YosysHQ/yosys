module opt_share_test(
  input [15:0]      a,
  input [15:0]      b,
  input [15:0]      c,
  input [15:0]      d,
  input [2:0]       sel,
  output reg [15:0] res
  );

  always @* begin
    case(sel)
      0: res = a + d;
      1: res = a - b;
      2: res = b;
      3: res = b - c;
      4: res = b - a;
      5: res = c;
      6: res = a - c;
      default: res = 16'bx;
    endcase
  end

endmodule
