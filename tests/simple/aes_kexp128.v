
// test taken from aes_core from iwls2005

module aes_key_expand_128(clk, kld, key, wo_0, wo_1, wo_2, wo_3);

input		clk, kld;
input	[15:0]	key;
output	[3:0]	wo_0, wo_1, wo_2, wo_3;
reg	[3:0]	w[3:0];

assign wo_0 = w[0];
assign wo_1 = w[1];
assign wo_2 = w[2];
assign wo_3 = w[3];

always @(posedge clk) begin
	w[0] <= kld ? key[15:12] : w[0];
	w[1] <= kld ? key[11: 8] : w[0]^w[1];
	w[2] <= kld ? key[ 7: 4] : w[0]^w[1]^w[2];
	w[3] <= kld ? key[ 3: 0] : w[0]^w[1]^w[2]^w[3];
end

endmodule

