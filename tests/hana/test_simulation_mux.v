
// test_simulation_mux_16_test.v
module f1_test(input [15:0] in, input [3:0] select, output reg out);

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

// test_simulation_mux_2_test.v
module f2_test(input [1:0] in, input select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	endcase
endmodule	

// test_simulation_mux_32_test.v
module f3_test(input [31:0] in, input [4:0] select, output reg out);

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


// test_simulation_mux_4_test.v
module f4_test(input [3:0] in, input [1:0] select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	    2: out = in[2];
	    3: out = in[3];
	endcase
endmodule	

// test_simulation_mux_64_test.v
module f5_test(input [63:0] in, input [5:0] select, output reg out);

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
	    32: out = in[32];
	    33: out = in[33];
	    34: out = in[34];
	    35: out = in[35];
	    36: out = in[36];
	    37: out = in[37];
	    38: out = in[38];
	    39: out = in[39];
	    40: out = in[40];
	    41: out = in[41];
	    42: out = in[42];
	    43: out = in[43];
	    44: out = in[44];
	    45: out = in[45];
	    46: out = in[46];
	    47: out = in[47];
	    48: out = in[48];
	    49: out = in[49];
	    50: out = in[50];
	    51: out = in[51];
	    52: out = in[52];
	    53: out = in[53];
	    54: out = in[54];
	    55: out = in[55];
	    56: out = in[56];
	    57: out = in[57];
	    58: out = in[58];
	    59: out = in[59];
	    60: out = in[60];
	    61: out = in[61];
	    62: out = in[62];
	    63: out = in[63];
	endcase
endmodule	


// test_simulation_mux_8_test.v
module f6_test(input [7:0] in, input [2:0] select, output reg out);

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
	endcase
endmodule
