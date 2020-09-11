module opt_share_test(
  input [15:0]      a,
  input [15:0]      b,
  input [15:0]      c,
  input [15:0]      d,
  input             sel,
  output reg [47:0] res,
  );

  wire [15:0]       add_res = a+b;
  wire [15:0]       sub_res = a-b;
  wire [31: 0]      cat1 = {add_res, c+d};
  wire [31: 0]      cat2 = {sub_res, c-d};

  always @* begin
    case(sel)
      0: res = {cat1, add_res};
      1: res = {cat2, add_res};
    endcase
  end

endmodule
