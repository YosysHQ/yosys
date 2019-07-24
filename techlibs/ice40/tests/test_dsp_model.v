`timescale 1ns / 1ps

module testbench;
	parameter [0:0] NEG_TRIGGER = 0;
	parameter [0:0] C_REG = 0;
	parameter [0:0] A_REG = 0;
	parameter [0:0] B_REG = 0;
	parameter [0:0] D_REG = 0;
	parameter [0:0] TOP_8x8_MULT_REG = 0;
	parameter [0:0] BOT_8x8_MULT_REG = 0;
	parameter [0:0] PIPELINE_16x16_MULT_REG1 = 0;
	parameter [0:0] PIPELINE_16x16_MULT_REG2 = 0;
	parameter [1:0] TOPOUTPUT_SELECT = 0;
	parameter [1:0] TOPADDSUB_LOWERINPUT = 0;
	parameter [0:0] TOPADDSUB_UPPERINPUT = 1;
	parameter [1:0] TOPADDSUB_CARRYSELECT = 0;
	parameter [1:0] BOTOUTPUT_SELECT = 0;
	parameter [1:0] BOTADDSUB_LOWERINPUT = 0;
	parameter [0:0] BOTADDSUB_UPPERINPUT = 1;
	parameter [1:0] BOTADDSUB_CARRYSELECT = 0;
	parameter [0:0] MODE_8x8 = 0;
	parameter [0:0] A_SIGNED = 0;
	parameter [0:0] B_SIGNED = 0;

	reg CLK, CE;
	reg [15:0] C, A, B, D;
	reg AHOLD, BHOLD, CHOLD, DHOLD;
	reg IRSTTOP, IRSTBOT;
	reg ORSTTOP, ORSTBOT;
	reg OLOADTOP, OLOADBOT;
	reg ADDSUBTOP, ADDSUBBOT;
	reg OHOLDTOP, OHOLDBOT;
	reg CI, ACCUMCI, SIGNEXTIN;

	output [31:0] REF_O, UUT_O;
	output REF_CO, REF_ACCUMCO, REF_SIGNEXTOUT;
	output UUT_CO, UUT_ACCUMCO, UUT_SIGNEXTOUT;

	integer errcount = 0;

	task clkcycle;
		begin
			#5;
			CLK = ~CLK;
			#10;
			CLK = ~CLK;
			#2;
			if (REF_O !== UUT_O) begin
				$display("ERROR at %1t: REF_O=%b UUT_O=%b DIFF=%b", $time, REF_O, UUT_O, REF_O ^ UUT_O);
				errcount = errcount + 1;
			end
			if (REF_CO !== UUT_CO) begin
				$display("ERROR at %1t: REF_CO=%b UUT_CO=%b", $time, REF_CO, UUT_CO);
				errcount = errcount + 1;
			end
			if (REF_ACCUMCO !== UUT_ACCUMCO) begin
				$display("ERROR at %1t: REF_ACCUMCO=%b UUT_ACCUMCO=%b", $time, REF_ACCUMCO, UUT_ACCUMCO);
				errcount = errcount + 1;
			end
			if (REF_SIGNEXTOUT !== UUT_SIGNEXTOUT) begin
				$display("ERROR at %1t: REF_SIGNEXTOUT=%b UUT_SIGNEXTOUT=%b", $time, REF_SIGNEXTOUT, UUT_SIGNEXTOUT);
				errcount = errcount + 1;
			end
			#3;
		end
	endtask

	initial begin
		$dumpfile("test_dsp_model.vcd");
		$dumpvars(0, testbench);

		#2;
		CLK = NEG_TRIGGER;
		CE = 1;
		{C, A, B, D} = 0;
		{AHOLD, BHOLD, CHOLD, DHOLD} = 0;
		{OLOADTOP, OLOADBOT} = 0;
		{ADDSUBTOP, ADDSUBBOT} = 0;
		{OHOLDTOP, OHOLDBOT} = 0;
		{CI, ACCUMCI, SIGNEXTIN} = 0;

		{IRSTTOP, IRSTBOT} = ~0;
		{ORSTTOP, ORSTBOT} = ~0;

		#3;
		{IRSTTOP, IRSTBOT} = 0;
		{ORSTTOP, ORSTBOT} = 0;

		repeat (300) begin
			clkcycle;

			A = $urandom;
			B = $urandom;
			C = $urandom;
			D = $urandom;

			{AHOLD, BHOLD, CHOLD, DHOLD} = $urandom & $urandom & $urandom;
			{OLOADTOP, OLOADBOT} = $urandom & $urandom & $urandom;
			{ADDSUBTOP, ADDSUBBOT} = $urandom & $urandom & $urandom;
			{OHOLDTOP, OHOLDBOT} = $urandom & $urandom & $urandom;
			{CI, ACCUMCI, SIGNEXTIN} = $urandom & $urandom & $urandom;

			{IRSTTOP, IRSTBOT} = $urandom & $urandom & $urandom;
			{ORSTTOP, ORSTBOT} = $urandom & $urandom & $urandom;
		end

		if (errcount == 0) begin
			$display("All tests passed.");
			$finish;
		end else begin
			$display("Caught %1d errors.", errcount);
			$stop;
		end
	end

	SB_MAC16 #(
		.NEG_TRIGGER              (NEG_TRIGGER             ),
		.C_REG                    (C_REG                   ),
		.A_REG                    (A_REG                   ),
		.B_REG                    (B_REG                   ),
		.D_REG                    (D_REG                   ),
		.TOP_8x8_MULT_REG         (TOP_8x8_MULT_REG        ),
		.BOT_8x8_MULT_REG         (BOT_8x8_MULT_REG        ),
		.PIPELINE_16x16_MULT_REG1 (PIPELINE_16x16_MULT_REG1),
		.PIPELINE_16x16_MULT_REG2 (PIPELINE_16x16_MULT_REG2),
		.TOPOUTPUT_SELECT         (TOPOUTPUT_SELECT        ),
		.TOPADDSUB_LOWERINPUT     (TOPADDSUB_LOWERINPUT    ),
		.TOPADDSUB_UPPERINPUT     (TOPADDSUB_UPPERINPUT    ),
		.TOPADDSUB_CARRYSELECT    (TOPADDSUB_CARRYSELECT   ),
		.BOTOUTPUT_SELECT         (BOTOUTPUT_SELECT        ),
		.BOTADDSUB_LOWERINPUT     (BOTADDSUB_LOWERINPUT    ),
		.BOTADDSUB_UPPERINPUT     (BOTADDSUB_UPPERINPUT    ),
		.BOTADDSUB_CARRYSELECT    (BOTADDSUB_CARRYSELECT   ),
		.MODE_8x8                 (MODE_8x8                ),
		.A_SIGNED                 (A_SIGNED                ),
		.B_SIGNED                 (B_SIGNED                )
	) ref (
		.CLK        (CLK           ),
		.CE         (CE            ),
		.C          (C             ),
		.A          (A             ),
		.B          (B             ),
		.D          (D             ),
		.AHOLD      (AHOLD         ),
		.BHOLD      (BHOLD         ),
		.CHOLD      (CHOLD         ),
		.DHOLD      (DHOLD         ),
		.IRSTTOP    (IRSTTOP       ),
		.IRSTBOT    (IRSTBOT       ),
		.ORSTTOP    (ORSTTOP       ),
		.ORSTBOT    (ORSTBOT       ),
		.OLOADTOP   (OLOADTOP      ),
		.OLOADBOT   (OLOADBOT      ),
		.ADDSUBTOP  (ADDSUBTOP     ),
		.ADDSUBBOT  (ADDSUBBOT     ),
		.OHOLDTOP   (OHOLDTOP      ),
		.OHOLDBOT   (OHOLDBOT      ),
		.CI         (CI            ),
		.ACCUMCI    (ACCUMCI       ),
		.SIGNEXTIN  (SIGNEXTIN     ),
		.O          (REF_O         ),
		.CO         (REF_CO        ),
		.ACCUMCO    (REF_ACCUMCO   ),
		.SIGNEXTOUT (REF_SIGNEXTOUT)
	);

	SB_MAC16_UUT #(
		.NEG_TRIGGER              (NEG_TRIGGER             ),
		.C_REG                    (C_REG                   ),
		.A_REG                    (A_REG                   ),
		.B_REG                    (B_REG                   ),
		.D_REG                    (D_REG                   ),
		.TOP_8x8_MULT_REG         (TOP_8x8_MULT_REG        ),
		.BOT_8x8_MULT_REG         (BOT_8x8_MULT_REG        ),
		.PIPELINE_16x16_MULT_REG1 (PIPELINE_16x16_MULT_REG1),
		.PIPELINE_16x16_MULT_REG2 (PIPELINE_16x16_MULT_REG2),
		.TOPOUTPUT_SELECT         (TOPOUTPUT_SELECT        ),
		.TOPADDSUB_LOWERINPUT     (TOPADDSUB_LOWERINPUT    ),
		.TOPADDSUB_UPPERINPUT     (TOPADDSUB_UPPERINPUT    ),
		.TOPADDSUB_CARRYSELECT    (TOPADDSUB_CARRYSELECT   ),
		.BOTOUTPUT_SELECT         (BOTOUTPUT_SELECT        ),
		.BOTADDSUB_LOWERINPUT     (BOTADDSUB_LOWERINPUT    ),
		.BOTADDSUB_UPPERINPUT     (BOTADDSUB_UPPERINPUT    ),
		.BOTADDSUB_CARRYSELECT    (BOTADDSUB_CARRYSELECT   ),
		.MODE_8x8                 (MODE_8x8                ),
		.A_SIGNED                 (A_SIGNED                ),
		.B_SIGNED                 (B_SIGNED                )
	) uut (
		.CLK        (CLK           ),
		.CE         (CE            ),
		.C          (C             ),
		.A          (A             ),
		.B          (B             ),
		.D          (D             ),
		.AHOLD      (AHOLD         ),
		.BHOLD      (BHOLD         ),
		.CHOLD      (CHOLD         ),
		.DHOLD      (DHOLD         ),
		.IRSTTOP    (IRSTTOP       ),
		.IRSTBOT    (IRSTBOT       ),
		.ORSTTOP    (ORSTTOP       ),
		.ORSTBOT    (ORSTBOT       ),
		.OLOADTOP   (OLOADTOP      ),
		.OLOADBOT   (OLOADBOT      ),
		.ADDSUBTOP  (ADDSUBTOP     ),
		.ADDSUBBOT  (ADDSUBBOT     ),
		.OHOLDTOP   (OHOLDTOP      ),
		.OHOLDBOT   (OHOLDBOT      ),
		.CI         (CI            ),
		.ACCUMCI    (ACCUMCI       ),
		.SIGNEXTIN  (SIGNEXTIN     ),
		.O          (UUT_O         ),
		.CO         (UUT_CO        ),
		.ACCUMCO    (UUT_ACCUMCO   ),
		.SIGNEXTOUT (UUT_SIGNEXTOUT)
	);
endmodule

module testbench_comb_8x8_A;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (2),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (0),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (0),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (2),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (0),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (0),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (0),
		.B_SIGNED                  (0)
	) testbench ();
endmodule

module testbench_comb_8x8_A_signedA;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (2),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (0),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (0),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (2),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (0),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (0),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (1),
		.B_SIGNED                  (0)
	) testbench ();
endmodule

module testbench_comb_8x8_A_signedB;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (2),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (0),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (0),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (2),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (0),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (0),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (0),
		.B_SIGNED                  (1)
	) testbench ();
endmodule

module testbench_comb_8x8_A_signedAB;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (2),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (0),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (0),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (2),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (0),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (0),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (1),
		.B_SIGNED                  (1)
	) testbench ();
endmodule

module testbench_comb_8x8_B;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (0),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (1),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (1),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (0),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (1),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (1),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (0),
		.B_SIGNED                  (0)
	) testbench ();
endmodule

module testbench_comb_8x8_B_signedA;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (0),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (1),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (1),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (0),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (1),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (1),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (1),
		.B_SIGNED                  (0)
	) testbench ();
endmodule

module testbench_comb_8x8_B_signedB;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (0),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (1),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (1),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (0),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (1),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (1),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (0),
		.B_SIGNED                  (1)
	) testbench ();
endmodule

module testbench_comb_8x8_B_signedAB;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (0),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (1),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (1),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (0),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (1),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (1),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (0),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (1),
		.B_SIGNED                  (1)
	) testbench ();
endmodule

module testbench_comb_16x16;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (0),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (2),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (1),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (0),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (2),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (1),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (0),
		.B_SIGNED                  (0)
	) testbench ();
endmodule

module testbench_comb_16x16_signedA;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (0),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (2),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (1),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (0),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (2),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (1),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (1),
		.B_SIGNED                  (0)
	) testbench ();
endmodule

module testbench_comb_16x16_signedB;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (0),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (2),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (1),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (0),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (2),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (1),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (0),
		.B_SIGNED                  (1)
	) testbench ();
endmodule

module testbench_comb_16x16_signedAB;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (0),
		.A_REG                     (0),
		.B_REG                     (0),
		.D_REG                     (0),
		.TOP_8x8_MULT_REG          (0),
		.BOT_8x8_MULT_REG          (0),
		.PIPELINE_16x16_MULT_REG1  (0),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (0),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (2),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (1),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (0),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (2),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (1),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (1),
		.B_SIGNED                  (1)
	) testbench ();
endmodule

module testbench_seq_16x16_A;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (1),
		.A_REG                     (1),
		.B_REG                     (1),
		.D_REG                     (1),
		.TOP_8x8_MULT_REG          (1),
		.BOT_8x8_MULT_REG          (1),
		.PIPELINE_16x16_MULT_REG1  (1),
		.PIPELINE_16x16_MULT_REG2  (1),
		.TOPOUTPUT_SELECT          (0),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (2),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (1),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (0),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (2),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (1),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (0),
		.B_SIGNED                  (0)
	) testbench ();
endmodule

module testbench_seq_16x16_B;
	testbench #(
		.NEG_TRIGGER               (0),
		.C_REG                     (1),
		.A_REG                     (1),
		.B_REG                     (1),
		.D_REG                     (1),
		.TOP_8x8_MULT_REG          (1),
		.BOT_8x8_MULT_REG          (1),
		.PIPELINE_16x16_MULT_REG1  (1),
		.PIPELINE_16x16_MULT_REG2  (0),
		.TOPOUTPUT_SELECT          (1),   // 0=P, 1=Q, 2=8x8, 3=16x16
		.TOPADDSUB_LOWERINPUT      (2),   // 0=A, 1=8x8, 2=16x16, 3=S-EXT
		.TOPADDSUB_UPPERINPUT      (0),   // 0=Q, 1=C
		.TOPADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.BOTOUTPUT_SELECT          (1),   // 0=R, 1=S, 2=8x8, 3=16x16
		.BOTADDSUB_LOWERINPUT      (2),   // 0=B, 1=8x8, 2=16x16, 3=S-EXT
		.BOTADDSUB_UPPERINPUT      (0),   // 0=S, 1=D
		.BOTADDSUB_CARRYSELECT     (2),   // 0=0, 1=1, 2=ACI, 3=CI
		.MODE_8x8                  (0),
		.A_SIGNED                  (0),
		.B_SIGNED                  (0)
	) testbench ();
endmodule
