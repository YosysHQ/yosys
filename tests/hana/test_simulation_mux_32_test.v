module test(input [31:0] in, input [4:0] select, output reg out);

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
	    16: out = in[16];
	    17: out = in[17];
	    18: out = in[18];
	    19: out = in[19];
	    20: out = in[20];
	    21: out = in[21];
	    22: out = in[22];
	    23: out = in[23];
	    24: out = in[24];
	    25: out = in[25];
	    26: out = in[26];
	    27: out = in[27];
	    28: out = in[28];
	    29: out = in[29];
	    30: out = in[30];
	    31: out = in[31];
	endcase
endmodule	

