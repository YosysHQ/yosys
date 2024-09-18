// test multirange array assignement (copy)

module top;

logic a [1:0][1:0];
logic b [1:0][1:0];

assign a[0][0] = 1'b0;
assign a[0][1] = 1'b1;
assign a[1][0] = 1'b1;
assign a[1][1] = 1'b1;

assign b = a;

always_comb begin
	assert(b[0][0] == 1'b0);
	assert(b[0][1] == 1'b1);
	assert(b[1][0] == 1'b1);
	assert(b[1][1] == 1'b1);
end

// reversed indicies
logic r_a [1:0][1:0];
logic r_b [1:0][0:1];

assign r_a[0][0] = 1'b0;
assign r_a[0][1] = 1'b1;
assign r_a[1][0] = 1'b1;
assign r_a[1][1] = 1'b1;

assign r_b = r_a;

always_comb begin
  assert(r_b[0][1] == 1'b0);
  assert(r_b[0][0] == 1'b1);
  assert(r_b[1][1] == 1'b1);
  assert(r_b[1][0] == 1'b1);
end

endmodule
