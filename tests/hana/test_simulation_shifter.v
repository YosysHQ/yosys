
// test_simulation_shifter_left_16_test.v
module f1_test(input [15:0] IN, input [4:0] SHIFT, output [15:0] OUT);

assign OUT = IN << SHIFT;
endmodule

// test_simulation_shifter_left_32_test.v
module f2_test(input [31:0] IN, input [5:0] SHIFT, output [31:0] OUT);

assign OUT = IN << SHIFT;
endmodule

// test_simulation_shifter_left_4_test.v
module f3_test(input [3:0] IN, input [2:0] SHIFT, output [3:0] OUT);

assign OUT = IN << SHIFT;
endmodule

// test_simulation_shifter_left_64_test.v
module f4_test(input [63:0] IN, input [6:0] SHIFT, output [63:0] OUT);

assign OUT = IN << SHIFT;
endmodule

// test_simulation_shifter_left_8_test.v
module f5_test(input [7:0] IN, input [3:0] SHIFT, output [7:0] OUT);

assign OUT = IN << SHIFT;
endmodule

// test_simulation_shifter_right_16_test.v
module f6_test(input [15:0] IN, input [4:0] SHIFT, output [15:0] OUT);

assign OUT = IN >> SHIFT;
endmodule

// test_simulation_shifter_right_32_test.v
module f7_test(input [31:0] IN, input [5:0] SHIFT, output [31:0] OUT);

assign OUT = IN >> SHIFT;
endmodule

// test_simulation_shifter_right_4_test.v
module f8_test(input [3:0] IN, input [2:0] SHIFT, output [3:0] OUT);

assign OUT = IN >> SHIFT;
endmodule

// test_simulation_shifter_right_64_test.v
module f9_test(input [63:0] IN, input [6:0] SHIFT, output [63:0] OUT);

assign OUT = IN >> SHIFT;
endmodule

// test_simulation_shifter_right_8_test.v
module f10_test(input [7:0] IN, input [3:0] SHIFT, output [7:0] OUT);

assign OUT = IN >> SHIFT;
endmodule
