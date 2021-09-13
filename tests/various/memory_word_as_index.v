`define DATA 64'h492e5c4d7747e032

`define GATE(n, expr) \
module gate``n(sel, out); \
	input wire [3:0] sel; \
	output wire out; \
	reg [63:0] bits; \
	reg [5:0] ptrs[15:0]; \
	initial bits = `DATA; \
	initial $readmemh("memory_word_as_index.data", ptrs); \
	assign out = expr; \
endmodule

`GATE(1, bits[ptrs[sel]])
`GATE(2, bits[ptrs[sel][5:0]])
`GATE(3, bits[ptrs[sel]+:1])

module gold(sel, out);
	input wire [3:0] sel;
	output wire out = `DATA >> (sel * 4);
endmodule
