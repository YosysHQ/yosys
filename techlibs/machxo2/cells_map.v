module \$lut (A, Y);
	parameter WIDTH = 0;
	parameter LUT = 0;
	input [WIDTH-1:0] A;
	output Y;

	localparam rep = 1<<(4-WIDTH);
	wire [3:0] I;

	generate
		if(WIDTH == 2) begin
			assign I = {1'b0, 1'b0, A[1], A[0]};
		end else if(WIDTH == 3) begin
			assign I = {1'b0, A[2], A[1], A[0]};
		end else if(WIDTH == 4) begin
			assign I = {A[3], A[2], A[1], A[0]};
		end
	endgenerate

	LUT4 #(.INIT({rep{LUT}})) _TECHMAP_REPLACE_ (.A(I[0]), .B(I[1]), .C(I[2]), .D(I[3]), .F(Y));
endmodule

module  \$_DFF_P_ (input D, C, output Q); FACADE_FF #(.CEMUX("1"), .CLKMUX("CLK"), .LSRMUX("LSR"), .REGSET("RESET")) _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .D(D), .Q(Q)); endmodule
