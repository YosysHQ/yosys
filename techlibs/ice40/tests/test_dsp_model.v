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
	parameter [1:0] TOPADDSUB_LOWERINPUT = 2;
	parameter [0:0] TOPADDSUB_UPPERINPUT = 1;
	parameter [1:0] TOPADDSUB_CARRYSELECT = 2;
	parameter [1:0] BOTOUTPUT_SELECT = 0;
	parameter [1:0] BOTADDSUB_LOWERINPUT = 2;
	parameter [0:0] BOTADDSUB_UPPERINPUT = 1;
	parameter [1:0] BOTADDSUB_CARRYSELECT = 2;
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
				$display("ERROR at %1t: REF_O=%b UUT_O=%b", $time, REF_O, UUT_O);
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

		#5;
		CLK = NEG_TRIGGER;
		CE = 1;
		{C, A, B, D} = 0;
		{AHOLD, BHOLD, CHOLD, DHOLD} = 0;
		{IRSTTOP, IRSTBOT} = 0;
		{ORSTTOP, ORSTBOT} = 0;
		{OLOADTOP, OLOADBOT} = 0;
		{ADDSUBTOP, ADDSUBBOT} = 0;
		{OHOLDTOP, OHOLDBOT} = 0;
		{CI, ACCUMCI, SIGNEXTIN} = 0;

		// C = 10;
		// A = 15;
		// B = 22;
		// D = 27;

		repeat (10) clkcycle;

		if (errcount == 0) begin
			$display("All tests passed.");
		end else begin
			$display("Caught %1d errors.", errcount);
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
