module opt_share_test(
  input [15:0]      a,
  input [15:0]      b,
  input [15:0]      c,
  input [2:0]       sel,
  output reg [15:0] res
  );

  always @* begin
    case(sel)
      0: res = a + b;
      1: res = a - b;
      2: res = a + c;
      3: res = a - c;
      4: res = b;
      5: res = c;
      default: res = 16'bx;
    endcase
  end

endmodule
