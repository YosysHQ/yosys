
// test_simulation_techmap_buf_test.v
module f1_test(input in, output out);
assign out = in;
endmodule

// test_simulation_techmap_inv_test.v
module f2_test(input in, output out);
assign out = ~in;
endmodule

// test_simulation_techmap_mux_0_test.v
module f3_test(input [1:0] in, input select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	endcase
endmodule	

// test_simulation_techmap_mux_128_test.v
module f4_test(input [127:0] in, input [6:0] select, output reg out);

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
	    64: out = in[64];
	    65: out = in[65];
	    66: out = in[66];
	    67: out = in[67];
	    68: out = in[68];
	    69: out = in[69];
	    70: out = in[70];
	    71: out = in[71];
	    72: out = in[72];
	    73: out = in[73];
	    74: out = in[74];
	    75: out = in[75];
	    76: out = in[76];
	    77: out = in[77];
	    78: out = in[78];
	    79: out = in[79];
	    80: out = in[80];
	    81: out = in[81];
	    82: out = in[82];
	    83: out = in[83];
	    84: out = in[84];
	    85: out = in[85];
	    86: out = in[86];
	    87: out = in[87];
	    88: out = in[88];
	    89: out = in[89];
	    90: out = in[90];
	    91: out = in[91];
	    92: out = in[92];
	    93: out = in[93];
	    94: out = in[94];
	    95: out = in[95];
	    96: out = in[96];
	    97: out = in[97];
	    98: out = in[98];
	    99: out = in[99];
	    100: out = in[100];
	    101: out = in[101];
	    102: out = in[102];
	    103: out = in[103];
	    104: out = in[104];
	    105: out = in[105];
	    106: out = in[106];
	    107: out = in[107];
	    108: out = in[108];
	    109: out = in[109];
	    110: out = in[110];
	    111: out = in[111];
	    112: out = in[112];
	    113: out = in[113];
	    114: out = in[114];
	    115: out = in[115];
	    116: out = in[116];
	    117: out = in[117];
	    118: out = in[118];
	    119: out = in[119];
	    120: out = in[120];
	    121: out = in[121];
	    122: out = in[122];
	    123: out = in[123];
	    124: out = in[124];
	    125: out = in[125];
	    126: out = in[126];
	    127: out = in[127];
	endcase
endmodule

// test_simulation_techmap_mux_8_test.v
module f5_test(input [7:0] in, input [2:0] select, output reg out);

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
