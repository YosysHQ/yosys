module test(input D, C, R, output reg Q);
    always @(posedge C, posedge R)
        if (R)
	    Q <= 0;
	else
	    Q <= D;
endmodule
