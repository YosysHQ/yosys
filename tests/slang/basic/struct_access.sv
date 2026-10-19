module dut();
typedef struct packed {
  logic a;
  logic b;
} sub_sub_struct_t;

typedef struct packed {
  sub_sub_struct_t c;
} sub_struct_t;

typedef struct packed {
  sub_struct_t d;
  sub_struct_t e;
} struct_t;

parameter struct_t P = 4'b1100;

localparam sub_struct_t f = P.d;
localparam sub_struct_t g = P.e;
localparam sub_sub_struct_t h = f.c;
localparam logic i = P.d.c.a;
localparam logic j = P.d.c.b;
localparam x = P.e;
localparam y = x.c;
localparam z = y.a;
localparam q = P.d;
localparam n = q.c.a;

always_comb begin
  assert(P == 4'b1100);
  assert(f == 2'b11);
  assert(g == 2'b00);
  assert(h == 2'b11);
  assert(i == 1'b1);
  assert(j == 1'b1);
  assert(x == 2'b00);
  assert(y == 2'b00);
  assert(x.c == 2'b00);
  assert(y.b == 1'b0);
  assert(n == 1'b1);
  assert(z == 1'b0);
end
endmodule
