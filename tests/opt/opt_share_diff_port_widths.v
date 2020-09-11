module opt_share_test(
  input [15:0]       a,
  input [15:0]       b,
  input [15:0]       c,
  input [1:0]      sel,
  output reg [15:0] res
  );

  wire [15:0]       add0_res = a+b;
  wire [15:0]       add1_res = a+c;

  always @* begin
    case(sel)
      0: res = add0_res[10:0];
      1: res = add1_res[10:0];
      2: res = a - b;
      default: res = 32'bx;
    endcase
  end

endmodule
