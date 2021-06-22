package pkg;
	typedef logic pkg_user_t;
endpackage

module top;
	typedef logic user_t;

	// Continuous assignment to a variable is legal
	user_t var_1;
	assign var_1 = 0;
	assert property (var_1 == 0);

	var user_t var_2;
	assign var_2 = 0;
	assert property (var_2 == 0);

	var pkg::pkg_user_t var_3;
	assign var_3 = 0;
	assert property (var_3 == 0);

	// Procedural assignment to a variable is legal
	user_t var_4 = 0;
	assert property (var_4 == 0);

	user_t var_5;
	initial var_5 = 0;
	assert property (var_5 == 0);

	var user_t var_6 = 0;
	assert property (var_6 == 0);

	var user_t var_7;
	initial var_7 = 0;
	assert property (var_7 == 0);

	pkg::pkg_user_t var_8 = 0;
	assert property (var_8 == 0);

	pkg::pkg_user_t var_9;
	initial var_9 = 0;
	assert property (var_9 == 0);

	var pkg::pkg_user_t var_10 = 0;
	assert property (var_10 == 0);

	var pkg::pkg_user_t var_11;
	initial var_11 = 0;
	assert property (var_11 == 0);

	// Continuous assignment to a net is legal
	wire user_t wire_1 = 0;
	assert property (wire_3 == 0);

	wire user_t wire_2;
	assign wire_2 = 0;
	assert property (wire_2 == 0);

	wire pkg::pkg_user_t wire_3 = 0;
	assert property (wire_3 == 0);

	wire pkg::pkg_user_t wire_4;
	assign wire_4 = 0;
	assert property (wire_4 == 0);

	// Mixing continuous and procedural assignments is illegal
	user_t var_12 = 0;
	assign var_12 = 1; // warning: reg assigned in a continuous assignment

	user_t var_13;
	initial var_13 = 0;
	assign var_13 = 1; // warning: reg assigned in a continuous assignment

	var user_t var_14 = 0;
	assign var_14 = 1; // warning: reg assigned in a continuous assignment

	var user_t var_15;
	initial var_15 = 0;
	assign var_15 = 1; // warning: reg assigned in a continuous assignment

	pkg::pkg_user_t var_16 = 0;
	assign var_16 = 1; // warning: reg assigned in a continuous assignment

	pkg::pkg_user_t var_17;
	initial var_17 = 0;
	assign var_17 = 1; // warning: reg assigned in a continuous assignment

	var pkg::pkg_user_t var_18 = 0;
	assign var_18 = 1; // warning: reg assigned in a continuous assignment

	var pkg::pkg_user_t var_19;
	initial var_19 = 0;
	assign var_19 = 1; // warning: reg assigned in a continuous assignment

endmodule
