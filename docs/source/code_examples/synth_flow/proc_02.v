module test(input D, C, R, RV,
            output reg Q);
    always @(posedge C, posedge R)
        if (R)
	    Q <= RV;
	else
	    Q <= D;
endmodule
