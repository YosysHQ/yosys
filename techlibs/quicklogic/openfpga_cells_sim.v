
module carry_follower(
	output CO,
	input A,
	input B,
	input CI
);
	assign CO = ((A ^ B) & CI) | (~(A ^ B) & (A & B)); 
endmodule

(* abc9_lut=1, lib_whitebox *)
module LUT4(
   output O, 
   input I0,
   input I1,
   input I2,
   input I3
);
    parameter [15:0] INIT = 16'h0;
    parameter EQN = "(I0)";
    
    assign O = INIT[{I3, I2, I1, I0}];
endmodule