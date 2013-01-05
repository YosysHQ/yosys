module test(a, b, c, d, z);
input a, b, c, d;
output z;
reg z, temp1, temp2;

always @(a or b or c or d)
begin
    temp1 = a ^ b;
	temp2 = c ^ d;
	z = temp1 ^ temp2;
end	

endmodule
