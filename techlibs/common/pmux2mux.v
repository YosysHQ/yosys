module \$pmux (A, B, S, Y);

wire [1023:0] _TECHMAP_DO_ = "proc; clean";

parameter WIDTH = 1;
parameter S_WIDTH = 1;

input [WIDTH-1:0] A;
input [WIDTH*S_WIDTH-1:0] B;
input [S_WIDTH-1:0] S;
output reg [WIDTH-1:0] Y;

integer i;

always @* begin
	Y <= A;
	for (i = 0; i < S_WIDTH; i=i+1)
		if (S[i]) Y <= B[WIDTH*i +: WIDTH];
end

endmodule
