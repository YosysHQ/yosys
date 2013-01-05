module test(input [15:0] in, input [3:0] select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	    2: out = in[2];
	    3: out = in[3];
	    4: out = in[4];
	    5: out = in[5];
	    6: out = in[6];
	    7: out = in[7];
	    8: out = in[8];
	    9: out = in[9];
	    10: out = in[10];
	    11: out = in[11];
	    12: out = in[12];
	    13: out = in[13];
	    14: out = in[14];
	    15: out = in[15];
	endcase
endmodule
