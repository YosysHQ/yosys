`timescale 1ns / 1ps

module testbench;
	parameter integer A0REG = 1;
	parameter integer A1REG = 1;
	parameter integer B0REG = 1;
	parameter integer B1REG = 1;
	parameter integer CREG = 1;
	parameter integer DREG = 1;
	parameter integer MREG = 1;
	parameter integer PREG = 1;
	parameter integer CARRYINREG = 1;
	parameter integer CARRYOUTREG = 1;
	parameter integer OPMODEREG = 1;
	parameter CARRYINSEL = "OPMODE5";
	parameter RSTTYPE = "SYNC";

	reg CLK;
	reg CEA, CEB, CEC, CED, CEM, CEP, CECARRYIN, CEOPMODE;
	reg RSTA, RSTB, RSTC, RSTD, RSTM, RSTP, RSTCARRYIN, RSTOPMODE;
	reg [17:0] A;
	reg [17:0] B;
	reg [47:0] C;
	reg [17:0] D;
	reg [47:0] PCIN;
	reg [7:0] OPMODE;
	reg CARRYIN;

	output CARRYOUTF, REF_CARRYOUTF;
	output CARRYOUT, REF_CARRYOUT, REF_OLD_CARRYOUT;
	output [35:0] M, REF_M;
	output [47:0] P, REF_P, REF_OLD_P;
	output [17:0] BCOUT, REF_BCOUT, REF_OLD_BCOUT;
	output [47:0] PCOUT, REF_PCOUT, REF_OLD_PCOUT;

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
			if (REF_BCOUT !== BCOUT || REF_OLD_BCOUT != BCOUT) begin
				$display("ERROR at %1t: REF_BCOUT=%b REF_OLD_BCOUT=%b UUT_BCOUT=%b DIFF=%b", $time, REF_BCOUT, REF_OLD_BCOUT, BCOUT, REF_BCOUT ^ BCOUT);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			if (REF_M !== M) begin
				$display("ERROR at %1t: REF_M=%b UUT_M=%b DIFF=%b", $time, REF_M, M, REF_M ^ M);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			if (REF_P !== P || REF_OLD_P != P) begin
				$display("ERROR at %1t: REF_P=%b REF_OLD_P=%b UUT_P=%b DIFF=%b", $time, REF_P, REF_OLD_P, P, REF_P ^ P);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			if (REF_PCOUT !== PCOUT || REF_OLD_PCOUT != PCOUT) begin
				$display("ERROR at %1t: REF_PCOUT=%b REF_OLD_PCOUT=%b UUT_PCOUT=%b DIFF=%b", $time, REF_PCOUT, REF_OLD_PCOUT, PCOUT, REF_PCOUT ^ PCOUT);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			if (REF_CARRYOUT !== CARRYOUT || (REF_OLD_CARRYOUT != CARRYOUT && !CARRYOUTREG)) begin
				$display("ERROR at %1t: REF_CARRYOUT=%b REF_OLD_CARRYOUT=%b UUT_CARRYOUT=%b DIFF=%b", $time, REF_CARRYOUT, REF_OLD_CARRYOUT, CARRYOUT, REF_CARRYOUT ^ CARRYOUT);
				errcount = errcount + 1;
				ERROR_FLAG = 1;
			end
			if (REF_CARRYOUTF !== CARRYOUTF) begin
				$display("ERROR at %1t: REF_CARRYOUTF=%b UUT_CARRYOUTF=%b", $time, REF_CARRYOUTF, CARRYOUTF);
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
			if (OPMODE[3:2] == 2'b10 && PREG != 1) config_valid = 0;
		end
	endtask

	initial begin
		$dumpfile("test_dsp48a1_model.vcd");
		$dumpvars(0, testbench);

		#2;
		CLK = 1'b0;
		{CEA, CEB, CEC, CED, CEM, CEP, CECARRYIN, CEOPMODE} = 8'b11111111;
		{A, B, C, D, PCIN, OPMODE, CARRYIN} = 0;
		{RSTA, RSTB, RSTC, RSTD, RSTM, RSTP, RSTCARRYIN, RSTOPMODE} = 8'b11111111;
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
		{RSTA, RSTB, RSTC, RSTD, RSTM, RSTP, RSTCARRYIN, RSTOPMODE} = 0;

		repeat (10000) begin
			clkcycle;
			config_valid = 0;
			while (!config_valid) begin
				A = $urandom;
				B = $urandom;
				C = {$urandom, $urandom};
				D = $urandom;
				PCIN = {$urandom, $urandom};

				{CEA, CEB, CEC, CED, CEM, CEP, CECARRYIN, CEOPMODE} = $urandom | $urandom | $urandom;
				{RSTA, RSTB, RSTC, RSTD, RSTM, RSTP, RSTCARRYIN, RSTOPMODE} = $urandom & $urandom & $urandom & $urandom & $urandom & $urandom;
				{CARRYIN, OPMODE} = $urandom;

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

	DSP48A #(
		.A0REG              (A0REG),
		.A1REG              (A1REG),
		.B0REG              (B0REG),
		.B1REG              (B1REG),
		.CREG               (CREG),
		.DREG               (DREG),
		.MREG               (MREG),
		.PREG               (PREG),
		.CARRYINREG         (CARRYINREG),
		.OPMODEREG          (OPMODEREG),
		.CARRYINSEL         (CARRYINSEL),
		.RSTTYPE            (RSTTYPE)
	) ref_old (
		.A             (A),
		.B             (B),
		.C             (C),
		.D             (D),
		.PCIN          (PCIN),
		.CARRYIN       (CARRYIN),
		.OPMODE        (OPMODE),
		.BCOUT         (REF_OLD_BCOUT),
		.CARRYOUT      (REF_OLD_CARRYOUT),
		.P             (REF_OLD_P),
		.PCOUT         (REF_OLD_PCOUT),
		.CEA           (CEA),
		.CEB           (CEB),
		.CEC           (CEC),
		.CED           (CED),
		.CEM           (CEM),
		.CEP           (CEP),
		.CECARRYIN     (CECARRYIN),
		.CEOPMODE      (CEOPMODE),
		.CLK           (CLK),
		.RSTA          (RSTA),
		.RSTB          (RSTB),
		.RSTC          (RSTC),
		.RSTD          (RSTD),
		.RSTM          (RSTM),
		.RSTP          (RSTP),
		.RSTCARRYIN    (RSTCARRYIN),
		.RSTOPMODE     (RSTOPMODE)
	);

	DSP48A1 #(
		.A0REG              (A0REG),
		.A1REG              (A1REG),
		.B0REG              (B0REG),
		.B1REG              (B1REG),
		.CREG               (CREG),
		.DREG               (DREG),
		.MREG               (MREG),
		.PREG               (PREG),
		.CARRYINREG         (CARRYINREG),
		.CARRYOUTREG        (CARRYOUTREG),
		.OPMODEREG          (OPMODEREG),
		.CARRYINSEL         (CARRYINSEL),
		.RSTTYPE            (RSTTYPE)
	) ref (
		.A             (A),
		.B             (B),
		.C             (C),
		.D             (D),
		.PCIN          (PCIN),
		.CARRYIN       (CARRYIN),
		.OPMODE        (OPMODE),
		.BCOUT         (REF_BCOUT),
		.CARRYOUTF     (REF_CARRYOUTF),
		.CARRYOUT      (REF_CARRYOUT),
		.P             (REF_P),
		.M             (REF_M),
		.PCOUT         (REF_PCOUT),
		.CEA           (CEA),
		.CEB           (CEB),
		.CEC           (CEC),
		.CED           (CED),
		.CEM           (CEM),
		.CEP           (CEP),
		.CECARRYIN     (CECARRYIN),
		.CEOPMODE      (CEOPMODE),
		.CLK           (CLK),
		.RSTA          (RSTA),
		.RSTB          (RSTB),
		.RSTC          (RSTC),
		.RSTD          (RSTD),
		.RSTM          (RSTM),
		.RSTP          (RSTP),
		.RSTCARRYIN    (RSTCARRYIN),
		.RSTOPMODE     (RSTOPMODE)
	);

	DSP48A1_UUT #(
		.A0REG              (A0REG),
		.A1REG              (A1REG),
		.B0REG              (B0REG),
		.B1REG              (B1REG),
		.CREG               (CREG),
		.DREG               (DREG),
		.MREG               (MREG),
		.PREG               (PREG),
		.CARRYINREG         (CARRYINREG),
		.CARRYOUTREG        (CARRYOUTREG),
		.OPMODEREG          (OPMODEREG),
		.CARRYINSEL         (CARRYINSEL),
		.RSTTYPE            (RSTTYPE)
	) uut (
		.A             (A),
		.B             (B),
		.C             (C),
		.D             (D),
		.PCIN          (PCIN),
		.CARRYIN       (CARRYIN),
		.OPMODE        (OPMODE),
		.BCOUT         (BCOUT),
		.CARRYOUTF     (CARRYOUTF),
		.CARRYOUT      (CARRYOUT),
		.P             (P),
		.M             (M),
		.PCOUT         (PCOUT),
		.CEA           (CEA),
		.CEB           (CEB),
		.CEC           (CEC),
		.CED           (CED),
		.CEM           (CEM),
		.CEP           (CEP),
		.CECARRYIN     (CECARRYIN),
		.CEOPMODE      (CEOPMODE),
		.CLK           (CLK),
		.RSTA          (RSTA),
		.RSTB          (RSTB),
		.RSTC          (RSTC),
		.RSTD          (RSTD),
		.RSTM          (RSTM),
		.RSTP          (RSTP),
		.RSTCARRYIN    (RSTCARRYIN),
		.RSTOPMODE     (RSTOPMODE)
	);
endmodule

module mult_noreg;
	testbench #(
		.A0REG              (0),
		.A1REG              (0),
		.B0REG              (0),
		.B1REG              (0),
		.CREG               (0),
		.DREG               (0),
		.MREG               (0),
		.PREG               (0),
		.CARRYINREG         (0),
		.CARRYOUTREG        (0),
		.OPMODEREG          (0),
		.CARRYINSEL         ("CARRYIN"),
		.RSTTYPE            ("SYNC")
	) testbench ();
endmodule

module mult_allreg;
	testbench #(
		.A0REG              (1),
		.A1REG              (1),
		.B0REG              (1),
		.B1REG              (1),
		.CREG               (1),
		.DREG               (1),
		.MREG               (1),
		.PREG               (1),
		.CARRYINREG         (1),
		.CARRYOUTREG        (1),
		.OPMODEREG          (1),
		.CARRYINSEL         ("OPMODE5"),
		.RSTTYPE            ("SYNC")
	) testbench ();
endmodule

module mult_inreg;
	testbench #(
		.A0REG              (1),
		.A1REG              (1),
		.B0REG              (1),
		.B1REG              (1),
		.CREG               (1),
		.DREG               (1),
		.MREG               (0),
		.PREG               (0),
		.CARRYINREG         (1),
		.CARRYOUTREG        (0),
		.OPMODEREG          (0),
		.CARRYINSEL         ("CARRYIN"),
		.RSTTYPE            ("SYNC")
	) testbench ();
endmodule
