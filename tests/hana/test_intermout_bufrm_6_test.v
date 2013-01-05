module test(in, out);
input in;
output out;

wire w1, w2, w3, w4;
assign w1 = in;
assign w2 = w1;
assign w4 = w3;
assign out = w4;
mybuf _mybuf(w2, w3);
endmodule

module mybuf(in, out);
input in;
output out;
wire w1, w2, w3, w4;

assign w1 = in;
assign w2 = w1;
assign out = w2;
endmodule

