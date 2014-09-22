
// test_parser_constructs_module_basic1_test.v
module f1_test;
endmodule

// test_parser_constructs_param_basic0_test.v
module f2_test #( parameter v2kparam = 5)
(in, out, io, vin, vout, vio);
input in;
output out;
inout io;
input [3:0] vin;
output [v2kparam:0] vout;
inout [0:3] vio;
parameter myparam = 10;
endmodule

// test_parser_constructs_port_basic0_test.v
module f3_test(in, out, io, vin, vout, vio);
input in;
output out;
inout io;
input [3:0] vin;
output [3:0] vout;
inout [0:3] vio;
endmodule

// test_parser_directives_define_simpledef_test.v
`define parvez ahmad
`define  WIRE wire
`define TEN 10

module f4_`parvez();
parameter param = `TEN;
`WIRE w;
assign w = `TEN;
endmodule

// test_parser_misc_operators_test.v
module f5_test(out, i0, i1, i2, i3, s1, s0);
output out;
input i0, i1, i2, i3;
input s1, s0;

assign out = (~s1 & s0 & i0) |
			 (~s1 & s0 & i1) |
			 (s1 & ~s0 & i2) |
			 (s1 & s0 & i3);

endmodule

module f5_ternaryop(out, i0, i1, i2, i3, s1, s0);
output out;
input i0, i1, i2, i3;
input s1, s0;

assign out = s1 ? (s0 ? i3 : i2) : (s0 ? i1 : i0);

endmodule

module f5_fulladd4(sum, c_out, a, b, c_in);
output [3:0] sum;
output c_out;
input [3:0] a, b;
input c_in;

assign {c_out, sum} = a + b + c_in;
endmodule

// test_parser_v2k_comb_port_data_type_test.v
module f6_adder(sum , co, a, b, ci);
output	reg		[31:0]	sum;
output	reg				co;
input	wire	[31:0]	a, b;
input wire				ci;
endmodule

// test_parser_v2k_comma_sep_sens_list_test.v
module f7_test(q, d, clk, reset);
output reg q;
input d, clk, reset;

always @ (posedge clk, negedge reset)
	if(!reset) q <= 0;
	else q <= d;

endmodule
