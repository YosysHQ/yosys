module NonBlockingEx(clk, merge, er, xmit, fddi, claim);
input clk, merge, er, xmit, fddi;
output reg claim;
reg fcr;

always @(posedge clk)
begin
    fcr <= er | xmit;

	if(merge)
	    claim <= fcr & fddi;
	else
	    claim <= fddi;
end
endmodule
