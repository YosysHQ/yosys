module test(in1, in2, out);
input in1, in2;
output out;
// Y with cluster of mybuf instances at the junction

wire w1, w2, w3, w4, w5, w6, w7, w8, w9, w10;
assign w1 = in1;
assign w2 = w1;
assign w5 = in2;
assign w6 = w5;
assign w10 = w9;
assign out = w10;

mybuf _mybuf0(w2, w3);
mybuf _mybuf1(w3, w4);

mybuf _mybuf2(w6, w7);
mybuf _mybuf3(w7, w4);

mybuf _mybuf4(w4, w8);
mybuf _mybuf5(w8, w9);
endmodule

module mybuf(in, out);
input in;
output out;
wire w1, w2, w3, w4;

assign w1 = in;
assign w2 = w1;
assign out = w2;
endmodule

