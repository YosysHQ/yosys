module foo;
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
always_comb begin
  assert(8'b11111111 == outa);
  assert(7'b0000000 == outb);
  assert(6'b111111 == outc);
  assert(5'b00000 == outd);
  assert(4'b1111 == oute);
end

endmodule
