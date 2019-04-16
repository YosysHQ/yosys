(* abc_box_id = 1 *)
module SB_CARRY (output CO, input CI, I0, I1);
	assign CO = (I0 && I1) || ((I0 || I1) && CI);
endmodule

