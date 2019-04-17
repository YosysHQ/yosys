(* abc_box_id = 1 *)
module SB_CARRY (output CO, input CI, I0, I1);
	assign CO = (I0 && I1) || ((I0 || I1) && CI);
endmodule

(* abc_box_id = 2 *)
module SB_LUT4 (output O, input I0, I1, I2, I3);
	parameter [15:0] LUT_INIT = 0;
	// Indicate this is a black-box
	assign O = 1'b0;
endmodule

