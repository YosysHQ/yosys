module andor_pmux_basic (
	input  [2:0] sel,
	input  [5:0] d,
	input        a,
	output [2:0] y
);
	assign y = ({3{sel == 3'd1}} & d[2:0]) |
	           ({3{sel == 3'd3}} & {d[3] & a, d[4], d[5]}) |
	           ({3{sel == 3'd6}} & 3'b001);
endmodule

module andor_pmux_outer_enable (
	input  [2:0] sel,
	input  [5:0] d,
	input        en,
	output [2:0] y
);
	wire [2:0] body;

	assign body = ({3{sel == 3'd2}} & {1'b0, d[0], d[1]}) |
	              ({3{sel == 3'd5}} & {d[2], d[3], d[4]}) |
	              ({3{sel == 3'd7}} & {d[5], 1'b1, d[0]});
	assign y = {3{en}} & body;
endmodule

module andor_pmux_duplicate (
	input  [1:0] sel,
	input  [11:0] d,
	output [3:0] y
);
	assign y = ({4{sel == 2'd1}} & d[3:0]) |
	           ({4{sel == 2'd1}} & d[7:4]) |
	           ({4{sel == 2'd2}} & d[11:8]);
endmodule

module andor_pmux_mixed_select_negative (
	input  [1:0] sel_a,
	input  [1:0] sel_b,
	input        a,
	input        b,
	output       y
);
	assign y = ((sel_a == 2'd1) & a) |
	           ((sel_b == 2'd2) & b);
endmodule

module andor_pmux_wide_decode (
	input  [3:0]  sel,
	input  [23:0] d,
	input         q,
	output [3:0]  y
);
	assign y = ({4{sel == 4'd1}}  & d[3:0]) |
	           ({4{sel == 4'd4}}  & {d[4] & q, d[5], 1'b0, d[6]}) |
	           ({4{sel == 4'd7}}  & d[10:7]) |
	           ({4{sel == 4'd9}}  & {1'b1, d[11], d[12] & q, d[13]}) |
	           ({4{sel == 4'd12}} & d[17:14]) |
	           ({4{sel == 4'd15}} & {d[18], d[19], d[20], 1'b1});
endmodule

module andor_pmux_shared_subtree (
	input  [2:0] sel,
	input  [8:0] d,
	input  [2:0] q,
	output [2:0] y,
	output [2:0] z
);
	wire [2:0] sub = ({3{sel == 3'd1}} & d[2:0]) |
	                 ({3{sel == 3'd3}} & d[5:3]);

	assign y = sub | ({3{sel == 3'd6}} & d[8:6]);
	assign z = sub & q;
endmodule

module andor_pmux_single_arm_negative (
	input  [1:0] sel,
	input  [1:0] d,
	output [1:0] y
);
	assign y = ({2{sel == 2'd1}} & d) | 2'b00;
endmodule

module andor_pmux_all_zero_negative (
	input  [1:0] sel,
	output [1:0] y
);
	assign y = ({2{sel == 2'd1}} & 2'b00) |
	           ({2{sel == 2'd2}} & 2'b00);
endmodule

module andor_pmux_non_eq_leaf_negative (
	input  [1:0] sel,
	input        raw,
	input        a,
	input        b,
	output       y
);
	assign y = ((sel == 2'd1) & a) |
	           (raw & b);
endmodule

module andor_pmux_duplicate_complex (
	input  [2:0] sel,
	input  [11:0] d,
	input        q,
	input        r,
	output [3:0] y
);
	assign y = ({4{sel == 3'd2}} & {d[0] & q, d[1], d[2], d[3]}) |
	           ({4{sel == 3'd2}} & {d[4], d[5] & r, d[6], d[7]}) |
	           ({4{sel == 3'd5}} & {d[8], d[9] & q, d[10] & r, d[11]});
endmodule
