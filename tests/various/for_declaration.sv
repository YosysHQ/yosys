module foo;
`default_nettype none
integer out;
initial begin
int i;
i = 10;
for (int i = 0; i < 5; i++)
  out = i;
out = i;
end

logic [7:0] outa = 8'b00000000;
genvar a;
for (a = 0 ; a < 8; a++) begin
  assign outa[a] = 1'b1;
end

logic [6:0] outb = 7'b1111111;
for (genvar b = 0 ; b < 7; b++) begin
  assign outb[b] = 1'b0;
end


logic [5:0] outc = 6'b000000;
always @(*) begin
  for (int c = 0 ; c < 6; c++) begin
    outc[c] = 1'b1;
  end
end

logic [4:0] outd = 5'b11111;
always @(*) begin
  for (int unsigned d = 0 ; d < 5; d++) begin
    outd[d] = 1'b0;
  end
end

logic [3:0] oute = 4'b0000;
always @(*) begin
  for (int signed e = 0 ; e < 4; e++) begin
    oute[e] = 1'b1;
  end
end

logic x;
for (genvar x = 0; x < 2; x++) begin : loop
    logic [x:0] y;
end
assign x = 1'sb1;
assign loop[0].y = 1'sb1;
assign loop[1].y = 2'sb10;

reg [15:0] k;
if (1) begin : gen
  integer k;
  initial begin
    for (integer k = 5; k < 10; k++)
      if (k == 5)
        gen.k = 0;
      else
        gen.k += 2 ** k;
    k = k * 2;
  end
end
initial k = gen.k;

wire [3:0] l;
for (genvar l = 0; l < 2; l++) begin : blk
  localparam w = l;
  if (l == 0) begin : sub
    wire [w:0] l;
  end
end
assign l = 2;
assign blk[0].sub.l = 1;

always_comb begin
  assert(8'b11111111 == outa);
  assert(7'b0000000 == outb);
  assert(6'b111111 == outc);
  assert(5'b00000 == outd);
  assert(4'b1111 == oute);
  assert(10 == out);
  assert(1'sb1 == x);
  assert(1'sb1 == loop[0].y);
  assert(2'sb10 == loop[1].y);
  assert(k == gen.k);
  assert(k == 16'b0000011110000000);
  assert(l == 2);
  assert(blk[0].sub.l == 1);
end

endmodule
