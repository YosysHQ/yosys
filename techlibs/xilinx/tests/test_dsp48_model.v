`timescale 1ns / 1ps

module testbench;
	parameter integer AREG = 1;
	parameter integer BREG = 1;
	parameter integer CREG = 1;
	parameter integer MREG = 1;
	parameter integer PREG = 1;
	parameter integer CARRYINREG = 1;
	parameter integer CARRYINSELREG = 1;
	parameter integer OPMODEREG = 1;
	parameter integer SUBTRACTREG = 1;
	parameter B_INPUT = "DIRECT";
	parameter LEGACY_MODE = "NONE";

	reg CLK;
	reg CEA, CEB, CEC, CEM, CEP, CECARRYIN, CECINSUB, CECTRL;
	reg RSTA, RSTB, RSTC, RSTM, RSTP, RSTCARRYIN, RSTCTRL;
	reg [17:0] A;
	reg [17:0] B;
	reg [47:0] C;
	reg [17:0] BCIN;
	reg [47:0] PCIN;
	reg CARRYIN;
	reg [6:0] OPMODE;
	reg SUBTRACT;
	reg [1:0] CARRYINSEL;

	output [47:0] P, REF_P;
	output [17:0] BCOUT, REF_BCOUT;
	output [47:0] PCOUT, REF_PCOUT;

	integer errcount = 0;

	reg ERROR_FLAG = 0;

	task clkcycle;
		begin
			#5;
			CLK = ~CLK;
			#10;
			CLK = ~CLK;
			#2;
			ERROR_FLAG = 0;
			if (REF_BCOUT !== BCOUT) begin
				$display("ERROR at %1t: REF_BCOUT=%b UUT_BCOUT=%b DIFF=%b", $time, REF_BCOUT, BCOUT, REF_BCOUT ^ BCOUT);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			if (REF_P !== P) begin
				$display("ERROR at %1t: REF_P=%b UUT_P=%b DIFF=%b", $time, REF_P, P, REF_P ^ P);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			if (REF_PCOUT !== PCOUT) begin
				$display("ERROR at %1t: REF_PCOUT=%b UUT_PCOUT=%b DIFF=%b", $time, REF_PCOUT, PCOUT, REF_PCOUT ^ PCOUT);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			#3;
		end
	endtask

	reg config_valid = 0;
	task drc;
		begin
			config_valid = 1;

			if (OPMODE[1:0] == 2'b10 && PREG != 1) config_valid = 0;
			if (OPMODE[1:0] == 2'b00 && CARRYINSEL == 2'b10) config_valid = 0;
			if (OPMODE[1:0] == 2'b10 && CARRYINSEL == 2'b10) config_valid = 0;
			if (OPMODE[1:0] == 2'b00 && CARRYINSEL == 2'b11) config_valid = 0;
			if (OPMODE[1:0] == 2'b10 && CARRYINSEL == 2'b11) config_valid = 0;
			if (OPMODE[3:2] == 2'b10) config_valid = 0;
			if ((OPMODE[3:2] == 2'b01) ^ (OPMODE[1:0] == 2'b01) == 1'b1) config_valid = 0;
			if ((OPMODE[6:4] == 3'b010 || OPMODE[6:4] == 3'b110) && PREG != 1) config_valid = 0;
			if (OPMODE[6:4] == 3'b100) config_valid = 0;
			if (OPMODE[6:4] == 3'b111) config_valid = 0;
			if (OPMODE[6:4] == 3'b000 && CARRYINSEL == 2'b01) config_valid = 0;
			if (OPMODE[6:4] == 3'b011 && CARRYINSEL == 2'b01) config_valid = 0;

			// Xilinx models consider these combinations invalid for an unknown reason.
			if (CARRYINSEL == 2'b01 && OPMODE[3:2] == 2'b00) config_valid = 0;
			if (CARRYINSEL == 2'b10 && OPMODE == 7'b0000011) config_valid = 0;
			if (CARRYINSEL == 2'b10 && OPMODE == 7'b0000101) config_valid = 0;
			if (CARRYINSEL == 2'b10 && OPMODE == 7'b0100011) config_valid = 0;
			if (CARRYINSEL == 2'b10 && OPMODE == 7'b0111111) config_valid = 0;
			if (CARRYINSEL == 2'b10 && OPMODE == 7'b1100011) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b0000011) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b0000101) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b0011111) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b0010011) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b0100011) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b0100101) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b0101111) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b0110011) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b0111111) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b1010011) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b1011111) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b1100011) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b1100101) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE == 7'b1101111) config_valid = 0;

			if (CARRYINSEL == 2'b10 && OPMODE[3:0] == 4'b0101 && MREG == 1) config_valid = 0;
			if (CARRYINSEL == 2'b11 && OPMODE[3:0] == 4'b0101 && MREG == 0) config_valid = 0;
		end
	endtask

	initial begin
		$dumpfile("test_dsp48_model.vcd");
		$dumpvars(0, testbench);

		#2;
		CLK = 1'b0;
		{CEA, CEB, CEC, CEM, CEP, CECARRYIN, CECINSUB, CECTRL} = 8'b11111111;
		{A, B, C, PCIN, OPMODE, SUBTRACT, CARRYIN, CARRYINSEL} = 0;
		{RSTA, RSTB, RSTC, RSTM, RSTP, RSTCARRYIN, RSTCTRL} = 7'b1111111;
		repeat (10) begin
			#10;
			CLK = 1'b1;
			#10;
			CLK = 1'b0;
			#10;
			CLK = 1'b1;
			#10;
			CLK = 1'b0;
		end
		{RSTA, RSTB, RSTC, RSTM, RSTP, RSTCARRYIN, RSTCTRL} = 0;

		repeat (100000) begin
			clkcycle;
			config_valid = 0;
			while (!config_valid) begin
				A = $urandom;
				B = $urandom;
				C = {$urandom, $urandom};
				BCIN = $urandom;
				PCIN = {$urandom, $urandom};

				{CEA, CEB, CEC, CEM, CEP, CECARRYIN, CECINSUB, CECTRL} = $urandom | $urandom | $urandom;
				{RSTA, RSTB, RSTC, RSTM, RSTP, RSTCARRYIN, RSTCTRL} = $urandom & $urandom & $urandom & $urandom & $urandom & $urandom;
				{CARRYIN, CARRYINSEL, OPMODE, SUBTRACT} = $urandom;

				drc;
			end
		end

		if (errcount == 0) begin
			$display("All tests passed.");
			$finish;
		end else begin
			$display("Caught %1d errors.", errcount);
			$stop;
		end
	end

	DSP48 #(
		.AREG               (AREG),
		.BREG               (BREG),
		.CREG               (CREG),
		.MREG               (MREG),
		.PREG               (PREG),
		.CARRYINREG         (CARRYINREG),
		.CARRYINSELREG      (CARRYINSELREG),
		.OPMODEREG          (OPMODEREG),
		.SUBTRACTREG        (SUBTRACTREG),
		.B_INPUT            (B_INPUT),
		.LEGACY_MODE        (LEGACY_MODE)
	) ref (
		.A             (A),
		.B             (B),
		.C             (C),
		.BCIN          (BCIN),
		.PCIN          (PCIN),
		.CARRYIN       (CARRYIN),
		.OPMODE        (OPMODE),
		.SUBTRACT      (SUBTRACT),
		.CARRYINSEL    (CARRYINSEL),
		.BCOUT         (REF_BCOUT),
		.P             (REF_P),
		.PCOUT         (REF_PCOUT),
		.CEA           (CEA),
		.CEB           (CEB),
		.CEC           (CEC),
		.CEM           (CEM),
		.CEP           (CEP),
		.CECARRYIN     (CECARRYIN),
		.CECINSUB       (CECINSUB),
		.CECTRL        (CECTRL),
		.CLK           (CLK),
		.RSTA          (RSTA),
		.RSTB          (RSTB),
		.RSTC          (RSTC),
		.RSTM          (RSTM),
		.RSTP          (RSTP),
		.RSTCARRYIN    (RSTCARRYIN),
		.RSTCTRL       (RSTCTRL)
	);

	DSP48_UUT #(
		.AREG               (AREG),
		.BREG               (BREG),
		.CREG               (CREG),
		.MREG               (MREG),
		.PREG               (PREG),
		.CARRYINREG         (CARRYINREG),
		.CARRYINSELREG      (CARRYINSELREG),
		.OPMODEREG          (OPMODEREG),
		.SUBTRACTREG        (SUBTRACTREG),
		.B_INPUT            (B_INPUT),
		.LEGACY_MODE        (LEGACY_MODE)
	) uut (
		.A             (A),
		.B             (B),
		.C             (C),
		.BCIN          (BCIN),
		.PCIN          (PCIN),
		.CARRYIN       (CARRYIN),
		.OPMODE        (OPMODE),
		.SUBTRACT      (SUBTRACT),
		.CARRYINSEL    (CARRYINSEL),
		.BCOUT         (BCOUT),
		.P             (P),
		.PCOUT         (PCOUT),
		.CEA           (CEA),
		.CEB           (CEB),
		.CEC           (CEC),
		.CEM           (CEM),
		.CEP           (CEP),
		.CECARRYIN     (CECARRYIN),
		.CECINSUB       (CECINSUB),
		.CECTRL        (CECTRL),
		.CLK           (CLK),
		.RSTA          (RSTA),
		.RSTB          (RSTB),
		.RSTC          (RSTC),
		.RSTM          (RSTM),
		.RSTP          (RSTP),
		.RSTCARRYIN    (RSTCARRYIN),
		.RSTCTRL       (RSTCTRL)
	);
endmodule

module mult_noreg;
	testbench #(
		.AREG               (0),
		.BREG               (0),
		.CREG               (0),
		.MREG               (0),
		.PREG               (0),
		.CARRYINREG         (0),
		.CARRYINSELREG      (0),
		.OPMODEREG          (0),
		.SUBTRACTREG        (0),
		.B_INPUT            ("DIRECT")
	) testbench ();
endmodule

module mult_allreg;
	testbench #(
		.AREG               (1),
		.BREG               (1),
		.CREG               (1),
		.MREG               (1),
		.PREG               (1),
		.CARRYINREG         (1),
		.CARRYINSELREG      (1),
		.OPMODEREG          (1),
		.SUBTRACTREG        (1),
		.B_INPUT            ("CASCADE")
	) testbench ();
endmodule

module mult_inreg;
	testbench #(
		.AREG               (1),
		.BREG               (1),
		.CREG               (1),
		.MREG               (0),
		.PREG               (0),
		.CARRYINREG         (1),
		.CARRYINSELREG      (0),
		.OPMODEREG          (0),
		.SUBTRACTREG        (0),
		.B_INPUT            ("DIRECT")
	) testbench ();
endmodule
