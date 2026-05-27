module andor_pmux_basic (
	input  [2:0] sel,
	input  [5:0] d,
	input        a,
	output [1:0] y
);
	assign y = ({2{sel == 3'd1}} & d[1:0]) |
	           ({2{sel == 3'd3}} & {d[2] & a, d[3]}) |
	           ({2{sel == 3'd6}} & 2'b01);
endmodule

module andor_pmux_outer_enable (
	input  [2:0] sel,
	input  [3:0] d,
	input        en,
	output [1:0] y
);
	wire [1:0] body;

	assign body = ({2{sel == 3'd2}} & {1'b0, d[0]}) |
	              ({2{sel == 3'd5}} & {d[1], d[2]}) |
	              ({2{sel == 3'd7}} & {d[3], 1'b1});
	assign y = {2{en}} & body;
endmodule

module andor_pmux_duplicate (
	input  [1:0] sel,
	input        a,
	input        b,
	input        c,
	input        d,
	input        e,
	input        f,
	output [1:0] y
);
	assign y = ({2{sel == 2'd1}} & {a, b}) |
	           ({2{sel == 2'd1}} & {c, d}) |
	           ({2{sel == 2'd2}} & {e, f});
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
	input  [3:0] d,
	input        q,
	output       y,
	output       z
);
	wire sub = ((sel == 3'd1) & d[0]) |
	           ((sel == 3'd3) & d[1]);

	assign y = sub | ((sel == 3'd6) & d[2]);
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
	input  [8:0] d,
	input        q,
	input        r,
	output [2:0] y
);
	assign y = ({3{sel == 3'd2}} & {d[0] & q, d[1], d[2]}) |
	           ({3{sel == 3'd2}} & {d[3], d[4] & r, d[5]}) |
	           ({3{sel == 3'd5}} & {d[6], d[7] & q, d[8] & r});
endmodule
