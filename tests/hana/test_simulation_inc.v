
// test_simulation_inc_16_test.v
module f1_test(input [15:0] in, output [15:0] out);

assign out = -in;

endmodule

// test_simulation_inc_1_test.v
module f2_test(input in, output  out);

assign out = -in;

endmodule

// test_simulation_inc_2_test.v
module f3_test(input [1:0] in, output [1:0] out);

assign out = -in;

endmodule

// test_simulation_inc_32_test.v
module f4_test(input [31:0] in, output [31:0] out);

assign out = -in;

endmodule

// test_simulation_inc_4_test.v
module f5_test(input [3:0] in, output [3:0] out);

assign out = -in;

endmodule

// test_simulation_inc_8_test.v
module f6_test(input [7:0] in, output [7:0] out);

assign out = -in;

endmodule
