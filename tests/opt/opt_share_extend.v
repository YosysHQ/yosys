module opt_share_test(
  input signed [7:0]       a,
  input signed [10:0]      b,
  input signed [15:0]      c,
  input [1:0]              sel,
  output reg signed [15:0] res
  );

  always @* begin
    case(sel)
      0: res = a + b;
      1: res = a - b;
      2: res = a + c;
      default: res = 16'bx;
    endcase
  end

endmodule
