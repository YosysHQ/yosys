module uut_forgen01(a, y);

input [4:0] a;
output y;

integer i, j;
reg [31:0] lut;

initial begin
	for (i = 0; i < 32; i = i+1) begin
		lut[i] = i > 1;
		for (j = 2; j*j <= i; j = j+1)
			if (i % j == 0)
				lut[i] = 0;
	end
end

assign y = lut[a];

endmodule
