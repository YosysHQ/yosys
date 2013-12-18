module test(a, y);
`define MSB_LSB_SEP :
`define get_msb(off, len) ((off)+(len)-1)
`define get_lsb(off, len) (off)
`define sel_bits(offset, len) `get_msb(offset, len) `MSB_LSB_SEP `get_lsb(offset, len)
input [31:0] a;
output [7:0] y;
assign y = a[`sel_bits(16, 8)];
endmodule
