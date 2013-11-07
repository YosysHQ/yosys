module constpower(ys, yu);

output [8*8*8-1:0] ys, yu;

genvar i, j;

generate
	for (i = 0; i < 8; i = i+1)
	for (j = 0; j < 8; j = j+1) begin:V
		assign ys[i*8 + j*64 + 7 : i*8 + j*64] = $signed(i-4) ** $signed(j-4);
		assign yu[i*8 + j*64 + 7 : i*8 + j*64] = $unsigned(i) ** $unsigned(j);
	end
endgenerate

endmodule
