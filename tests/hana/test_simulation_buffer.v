
// test_simulation_buffer_1_test.v
module f1_test(input in, output out);
assign out = in;
endmodule

// test_simulation_buffer_2_test.v
module f2_test(input [1:0] in, output [1:0] out);
assign out[0] = in[0];
assign out[1] = in[1];
endmodule

// test_simulation_buffer_3_test.v
module f3_test(input in, output [1:0] out);
assign out[0] = in;
assign out[1] = in;
endmodule
