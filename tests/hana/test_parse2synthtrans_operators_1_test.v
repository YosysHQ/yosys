module test(in, out);
input in;
output out;
parameter p1 = 10;
parameter p2 = 5;

assign out = +p1;
assign out = -p2;
assign out = p1 + p2;
assign out = p1 - p2;
endmodule
