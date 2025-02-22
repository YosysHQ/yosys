module gold(a, b);
	output wire [1:0] a;
	input wire [1:0] b;
	genvar i;
	for (i = 0; i < 2; i++) begin
		wire x;
		assign x = b[i];
		assign a[i] = x;
	end
endmodule

module gate(a, b);
	output wire [1:0] a;
	input wire [1:0] b;
	genvar i;
	for (i = 0; i < 2; i++) begin
		assign x = b[i];
		assign a[i] = x;
	end
endmodule
