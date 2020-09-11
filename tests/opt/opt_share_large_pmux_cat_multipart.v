module opt_share_test(
  input [15:0]      a,
  input [15:0]      b,
  input [15:0]      c,
  input [15:0]      d,
  input [2:0]       sel,
  output reg [31:0] res
  );

  wire [15:0]       add0_res = a+d;

  always @* begin
    case(sel)
      0: res = {add0_res, a};
      1: res = {a - b, add0_res[7], 15'b0};
      2: res = {b-a, b};
      3: res = {d, b - c};
      4: res = {d, b - a};
      5: res = {c, d};
      6: res = {a - c, b-d};
      default: res = 32'bx;
    endcase
  end

endmodule
