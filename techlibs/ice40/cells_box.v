(* abc_box_id = 1 *)
module ICE40_CARRY_LUT (output CO, O, input CI, I1, I2);
	assign CO = (I1 && I2) || ((I1 || I2) && CI);

	wire I0, I3;
	assign I0 = 1'b0;
	assign I3 = CI;

	//                            I0: 1010 1010 1010 1010
	//                            I1: 1100 1100 1100 1100
	//                            I2: 1111 0000 1111 0000
	//                            I3: 1111 1111 0000 0000
	localparam [15:0] LUT_INIT = 16'b 0110_1001_1001_0110;
	wire [7:0] s3 = I3 ? LUT_INIT[15:8] : LUT_INIT[7:0];
	wire [3:0] s2 = I2 ?       s3[ 7:4] :       s3[3:0];
	wire [1:0] s1 = I1 ?       s2[ 3:2] :       s2[1:0];
	assign O = I0 ? s1[1] : s1[0];
endmodule
