module split_shiftx_test01(i, s, o);
  wire [3:0] _0_;
  input [8:0] i;
  output [2:0] o;
  input [1:0] s;
  \$macc  #(
    .A_WIDTH(32'd4),
    .B_WIDTH(32'd0),
    .CONFIG(10'h282),
    .CONFIG_WIDTH(32'd10),
    .Y_WIDTH(32'd4)
  ) _1_ (
    .A({ 2'h3, s }),
    .B(),
    .Y(_0_)
  );
  \$shiftx  #(
    .A_SIGNED(32'd0),
    .A_WIDTH(32'd9),
    .B_SIGNED(32'd1),
    .B_WIDTH(32'd5),
    .Y_WIDTH(32'd3)
  ) _2_ (
    .A(i),
    .B({ 1'h0, _0_ }),
    .Y(o)
  );
endmodule

// Sign bit is 1
module split_shiftx_test02(i, s, o);
  wire [3:0] _0_;
  input [8:0] i;
  output [2:0] o;
  input [1:0] s;
  \$macc  #(
    .A_WIDTH(32'd4),
    .B_WIDTH(32'd0),
    .CONFIG(10'h282),
    .CONFIG_WIDTH(32'd10),
    .Y_WIDTH(32'd4)
  ) _1_ (
    .A({ 2'h3, s }),
    .B(),
    .Y(_0_)
  );
  \$shiftx  #(
    .A_SIGNED(32'd0),
    .A_WIDTH(32'd9),
    .B_SIGNED(32'd1),
    .B_WIDTH(32'd5),
    .Y_WIDTH(32'd3)
  ) _2_ (
    .A(i),
    .B({ 1'h1, _0_ }),
    .Y(o)
  );
endmodule

// Non constant $macc
module split_shiftx_test03(i, s, o);
  wire [3:0] _0_;
  input [8:0] i;
  output [2:0] o;
  input [1:0] s;
  \$macc  #(
    .A_WIDTH(32'd4),
    .B_WIDTH(32'd0),
    .CONFIG(10'h282),
    .CONFIG_WIDTH(32'd10),
    .Y_WIDTH(32'd4)
  ) _1_ (
    .A({ s, s }),
    .B(),
    .Y(_0_)
  );
  \$shiftx  #(
    .A_SIGNED(32'd0),
    .A_WIDTH(32'd9),
    .B_SIGNED(32'd1),
    .B_WIDTH(32'd5),
    .Y_WIDTH(32'd3)
  ) _2_ (
    .A(i),
    .B({ 1'h0, _0_ }),
    .Y(o)
  );
endmodule

// Wrong constant $macc
module split_shiftx_test04(i, s, o);
  wire [3:0] _0_;
  input [8:0] i;
  output [2:0] o;
  input [1:0] s;
  \$macc  #(
    .A_WIDTH(32'd4),
    .B_WIDTH(32'd0),
    .CONFIG(10'h282),
    .CONFIG_WIDTH(32'd10),
    .Y_WIDTH(32'd4)
  ) _1_ (
    .A({ 2'h2, s }),
    .B(),
    .Y(_0_)
  );
  \$shiftx  #(
    .A_SIGNED(32'd0),
    .A_WIDTH(32'd9),
    .B_SIGNED(32'd1),
    .B_WIDTH(32'd5),
    .Y_WIDTH(32'd3)
  ) _2_ (
    .A(i),
    .B({ 1'h0, _0_ }),
    .Y(o)
  );
endmodule
