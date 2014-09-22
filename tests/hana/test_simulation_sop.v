
// test_simulation_sop_basic_10_test.v
module f1_test(input [1:0] in, input select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	endcase
endmodule	

// test_simulation_sop_basic_11_test.v
module f2_test(input [3:0] in, input [1:0] select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	    2: out = in[2];
	    3: out = in[3];
	endcase
endmodule	

// test_simulation_sop_basic_12_test.v
module f3_test(input [7:0] in, input [2:0] select, output reg out);

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

// test_simulation_sop_basic_18_test.v
module f4_test(input [7:0] in, output out);

assign out = ~^in;

endmodule

// test_simulation_sop_basic_3_test.v
module f5_test(input in, output out);
assign out = ~in;
endmodule

// test_simulation_sop_basic_7_test.v
module f6_test(input in, output out);
assign out = in;
endmodule

// test_simulation_sop_basic_8_test.v
module f7_test(output out);
assign out = 1'b0;
endmodule

// test_simulation_sop_basic_9_test.v
module f8_test(input in, output out);
assign out = ~in;
endmodule
