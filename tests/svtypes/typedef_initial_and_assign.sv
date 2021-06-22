package pkg;
	typedef logic pkg_user_t;
endpackage

module top;
	typedef logic user_t;

	// Continuous assignment to a variable is legal
	user_t var_1;
	assign var_1 = 0;

	pkg::pkg_user_t var_2;
	assign var_2 = 0;

	// Mixing continuous and procedural assignments is illegal
	user_t var_3 = 0;
	assign var_3 = 1; // warning: reg assigned in a continuous assignment

	user_t var_4;
	initial var_4 = 0;
	assign var_4 = 1; // warning: reg assigned in a continuous assignment

	pkg::pkg_user_t var_5 = 0;
	assign var_5 = 1; // warning: reg assigned in a continuous assignment

	pkg::pkg_user_t var_6;
	initial var_6 = 0;
	assign var_6 = 1; // warning: reg assigned in a continuous assignment
endmodule
