`timescale 1ps / 1ps
`define SB_DFF_INIT initial Q = 0;
// `define SB_DFF_INIT

`ifndef NO_ICE40_DEFAULT_ASSIGNMENTS
`define ICE40_DEFAULT_ASSIGNMENT_V(v) = v
`define ICE40_DEFAULT_ASSIGNMENT_0 = 1'b0
`define ICE40_DEFAULT_ASSIGNMENT_1 = 1'b1
`else
`define ICE40_DEFAULT_ASSIGNMENT_V(v)
`define ICE40_DEFAULT_ASSIGNMENT_0
`define ICE40_DEFAULT_ASSIGNMENT_1
`endif

// SiliconBlue IO Cells

module SB_IO (
	inout  PACKAGE_PIN,
	input  LATCH_INPUT_VALUE,
	input  CLOCK_ENABLE `ICE40_DEFAULT_ASSIGNMENT_1,
	input  INPUT_CLK,
	input  OUTPUT_CLK,
	input  OUTPUT_ENABLE,
	input  D_OUT_0,
	input  D_OUT_1,
	output D_IN_0,
	output D_IN_1
);
	parameter [5:0] PIN_TYPE = 6'b000000;
	parameter [0:0] PULLUP = 1'b0;
	parameter [0:0] NEG_TRIGGER = 1'b0;
	parameter IO_STANDARD = "SB_LVCMOS";

`ifndef BLACKBOX
	reg dout, din_0, din_1;
	reg din_q_0, din_q_1;
	reg dout_q_0, dout_q_1;
	reg outena_q;

	// IO tile generates a constant 1'b1 internally if global_cen is not connected
	wire clken_pulled = CLOCK_ENABLE || CLOCK_ENABLE === 1'bz;
	reg  clken_pulled_ri;
	reg  clken_pulled_ro;

	generate if (!NEG_TRIGGER) begin
		always @(posedge INPUT_CLK)                       clken_pulled_ri <= clken_pulled;
		always @(posedge INPUT_CLK)  if (clken_pulled)    din_q_0         <= PACKAGE_PIN;
		always @(negedge INPUT_CLK)  if (clken_pulled_ri) din_q_1         <= PACKAGE_PIN;
		always @(posedge OUTPUT_CLK)                      clken_pulled_ro <= clken_pulled;
		always @(posedge OUTPUT_CLK) if (clken_pulled)    dout_q_0        <= D_OUT_0;
		always @(negedge OUTPUT_CLK) if (clken_pulled_ro) dout_q_1        <= D_OUT_1;
		always @(posedge OUTPUT_CLK) if (clken_pulled)    outena_q        <= OUTPUT_ENABLE;
	end else begin
		always @(negedge INPUT_CLK)                       clken_pulled_ri <= clken_pulled;
		always @(negedge INPUT_CLK)  if (clken_pulled)    din_q_0         <= PACKAGE_PIN;
		always @(posedge INPUT_CLK)  if (clken_pulled_ri) din_q_1         <= PACKAGE_PIN;
		always @(negedge OUTPUT_CLK)                      clken_pulled_ro <= clken_pulled;
		always @(negedge OUTPUT_CLK) if (clken_pulled)    dout_q_0        <= D_OUT_0;
		always @(posedge OUTPUT_CLK) if (clken_pulled_ro) dout_q_1        <= D_OUT_1;
		always @(negedge OUTPUT_CLK) if (clken_pulled)    outena_q        <= OUTPUT_ENABLE;
	end endgenerate

	always @* begin
		if (!PIN_TYPE[1] || !LATCH_INPUT_VALUE)
			din_0 = PIN_TYPE[0] ? PACKAGE_PIN : din_q_0;
		din_1 = din_q_1;
	end

	// work around simulation glitches on dout in DDR mode
	reg outclk_delayed_1;
	reg outclk_delayed_2;
	always @* outclk_delayed_1 <= OUTPUT_CLK;
	always @* outclk_delayed_2 <= outclk_delayed_1;

	always @* begin
		if (PIN_TYPE[3])
			dout = PIN_TYPE[2] ? !dout_q_0 : D_OUT_0;
		else
			dout = (outclk_delayed_2 ^ NEG_TRIGGER) || PIN_TYPE[2] ? dout_q_0 : dout_q_1;
	end

	assign D_IN_0 = din_0, D_IN_1 = din_1;

	generate
		if (PIN_TYPE[5:4] == 2'b01) assign PACKAGE_PIN = dout;
		if (PIN_TYPE[5:4] == 2'b10) assign PACKAGE_PIN = OUTPUT_ENABLE ? dout : 1'bz;
		if (PIN_TYPE[5:4] == 2'b11) assign PACKAGE_PIN = outena_q ? dout : 1'bz;
	endgenerate
`endif
`ifdef TIMING
specify
	(INPUT_CLK => D_IN_0) = (0:0:0, 0:0:0);
	(INPUT_CLK => D_IN_1) = (0:0:0, 0:0:0);
	(PACKAGE_PIN => D_IN_0) = (0:0:0, 0:0:0);
	(OUTPUT_CLK => PACKAGE_PIN) = (0:0:0, 0:0:0);
	(D_OUT_0 => PACKAGE_PIN) = (0:0:0, 0:0:0);
	(OUTPUT_ENABLE => PACKAGE_PIN) = (0:0:0, 0:0:0);

	$setuphold(posedge OUTPUT_CLK, posedge D_OUT_0, 0:0:0, 0:0:0);
	$setuphold(posedge OUTPUT_CLK, negedge D_OUT_0, 0:0:0, 0:0:0);
	$setuphold(negedge OUTPUT_CLK, posedge D_OUT_1, 0:0:0, 0:0:0);
	$setuphold(negedge OUTPUT_CLK, negedge D_OUT_1, 0:0:0, 0:0:0);
	$setuphold(negedge OUTPUT_CLK, posedge D_OUT_0, 0:0:0, 0:0:0);
	$setuphold(negedge OUTPUT_CLK, negedge D_OUT_0, 0:0:0, 0:0:0);
	$setuphold(posedge OUTPUT_CLK, posedge D_OUT_1, 0:0:0, 0:0:0);
	$setuphold(posedge OUTPUT_CLK, negedge D_OUT_1, 0:0:0, 0:0:0);
	$setuphold(posedge INPUT_CLK, posedge CLOCK_ENABLE, 0:0:0, 0:0:0);
	$setuphold(posedge INPUT_CLK, negedge CLOCK_ENABLE, 0:0:0, 0:0:0);
	$setuphold(posedge OUTPUT_CLK, posedge CLOCK_ENABLE, 0:0:0, 0:0:0);
	$setuphold(posedge OUTPUT_CLK, negedge CLOCK_ENABLE, 0:0:0, 0:0:0);
	$setuphold(posedge INPUT_CLK, posedge PACKAGE_PIN, 0:0:0, 0:0:0);
	$setuphold(posedge INPUT_CLK, negedge PACKAGE_PIN, 0:0:0, 0:0:0);
	$setuphold(negedge INPUT_CLK, posedge PACKAGE_PIN, 0:0:0, 0:0:0);
	$setuphold(negedge INPUT_CLK, negedge PACKAGE_PIN, 0:0:0, 0:0:0);
	$setuphold(posedge OUTPUT_CLK, posedge OUTPUT_ENABLE, 0:0:0, 0:0:0);
	$setuphold(posedge OUTPUT_CLK, negedge OUTPUT_ENABLE, 0:0:0, 0:0:0);
	$setuphold(negedge OUTPUT_CLK, posedge OUTPUT_ENABLE, 0:0:0, 0:0:0);
	$setuphold(negedge OUTPUT_CLK, negedge OUTPUT_ENABLE, 0:0:0, 0:0:0);
endspecify
`endif
endmodule

module SB_GB_IO (
	inout  PACKAGE_PIN,
	output GLOBAL_BUFFER_OUTPUT,
	input  LATCH_INPUT_VALUE,
	input  CLOCK_ENABLE `ICE40_DEFAULT_ASSIGNMENT_1,
	input  INPUT_CLK,
	input  OUTPUT_CLK,
	input  OUTPUT_ENABLE,
	input  D_OUT_0,
	input  D_OUT_1,
	output D_IN_0,
	output D_IN_1
);
	parameter [5:0] PIN_TYPE = 6'b000000;
	parameter [0:0] PULLUP = 1'b0;
	parameter [0:0] NEG_TRIGGER = 1'b0;
	parameter IO_STANDARD = "SB_LVCMOS";

	assign GLOBAL_BUFFER_OUTPUT = PACKAGE_PIN;

	SB_IO #(
		.PIN_TYPE(PIN_TYPE),
		.PULLUP(PULLUP),
		.NEG_TRIGGER(NEG_TRIGGER),
		.IO_STANDARD(IO_STANDARD)
	) IO (
		.PACKAGE_PIN(PACKAGE_PIN),
		.LATCH_INPUT_VALUE(LATCH_INPUT_VALUE),
		.CLOCK_ENABLE(CLOCK_ENABLE),
		.INPUT_CLK(INPUT_CLK),
		.OUTPUT_CLK(OUTPUT_CLK),
		.OUTPUT_ENABLE(OUTPUT_ENABLE),
		.D_OUT_0(D_OUT_0),
		.D_OUT_1(D_OUT_1),
		.D_IN_0(D_IN_0),
		.D_IN_1(D_IN_1)
	);
endmodule

module SB_GB (
	input  USER_SIGNAL_TO_GLOBAL_BUFFER,
	output GLOBAL_BUFFER_OUTPUT
);
	assign GLOBAL_BUFFER_OUTPUT = USER_SIGNAL_TO_GLOBAL_BUFFER;
`ifdef TIMING
specify
	(USER_SIGNAL_TO_GLOBAL_BUFFER => GLOBAL_BUFFER_OUTPUT) = (0:0:0, 0:0:0);
endspecify
`endif
endmodule

// SiliconBlue Logic Cells

(* abc9_lut=1, lib_whitebox *)
module SB_LUT4 (
	output O,
	input I0 `ICE40_DEFAULT_ASSIGNMENT_0,
	input I1 `ICE40_DEFAULT_ASSIGNMENT_0,
	input I2 `ICE40_DEFAULT_ASSIGNMENT_0,
	input I3 `ICE40_DEFAULT_ASSIGNMENT_0
);
	parameter [15:0] LUT_INIT = 0;
	wire [7:0] s3 = I3 ? LUT_INIT[15:8] : LUT_INIT[7:0];
	wire [3:0] s2 = I2 ?       s3[ 7:4] :       s3[3:0];
	wire [1:0] s1 = I1 ?       s2[ 3:2] :       s2[1:0];
	assign O = I0 ? s1[1] : s1[0];
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L80
		(I0 => O) = (449, 386);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L83
		(I1 => O) = (400, 379);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L86
		(I2 => O) = (379, 351);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L88
		(I3 => O) = (316, 288);
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L80
		(I0 => O) = (662, 569);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L83
		(I1 => O) = (589, 558);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L86
		(I2 => O) = (558, 517);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L88
		(I3 => O) = (465, 423);
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L92
		(I0 => O) = (1245, 1285);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L95
		(I1 => O) = (1179, 1232);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L98
		(I2 => O) = (1179, 1205);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L100
		(I3 => O) = (861, 874);
	endspecify
`endif
endmodule

(* lib_whitebox *)
module SB_CARRY (output CO, input I0, I1, CI);
	assign CO = (I0 && I1) || ((I0 || I1) && CI);
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L79
		(CI => CO) = (126, 105);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L82
		(I0 => CO) = (259, 245);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L85
		(I1 => CO) = (231, 133);
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L79
		(CI => CO) = (186, 155);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L82
		(I0 => CO) = (382, 362);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L85
		(I1 => CO) = (341, 196);
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L91
		(CI => CO) = (278, 278);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L94
		(I0 => CO) = (675, 662);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L97
		(I1 => CO) = (609, 358);
	endspecify
`endif
endmodule

// Positive Edge SiliconBlue FF Cells

(* abc9_flop, lib_whitebox *)
module SB_DFF (
	output reg Q,
	input C, D
);
	`SB_DFF_INIT

	always @(posedge C)
		Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		(posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		(posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		(posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFE (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input D
);
	`SB_DFF_INIT

	always @(posedge C)
		if (E)
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C &&& E, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E) (posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E) (posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E) (posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFSR (
	output reg Q,
	input C, R, D
);
	`SB_DFF_INIT

	always @(posedge C)
		if (R)
			Q <= 0;
		else
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L78
		$setup(R, posedge C, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if ( R) (posedge C => (Q : 1'b0)) = 540;
		if (!R) (posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L78
		$setup(R, posedge C, 299);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if ( R) (posedge C => (Q : 1'b0)) = 796;
		if (!R) (posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L90
		$setup(R, posedge C, 530);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if ( R) (posedge C => (Q : 1'b0)) = 1391;
		if (!R) (posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module SB_DFFR (
	output reg Q,
	input C, R, D
);
	`SB_DFF_INIT

	always @(posedge C, posedge R)
		if (R)
			Q <= 0;
		else
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L63
		$setup(negedge R, posedge C, 160);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L91
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 599;
`else
		if (R) (R => Q) = 599;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (!R) (posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L63
		$setup(negedge R, posedge C, 235);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L91
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 883;
`else
		if (R) (R => Q) = 883;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (!R) (posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L75
		$setup(negedge R, posedge C, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L103
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 1589;
`else
		if (R) (R => Q) = 1589;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (!R) (posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFSS (
	output reg Q,
	input C, S, D
);
	`SB_DFF_INIT

	always @(posedge C)
		if (S)
			Q <= 1;
		else
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L78
		$setup(S, posedge C, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if ( S) (posedge C => (Q : 1'b1)) = 540;
		if (!S) (posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L78
		$setup(S, posedge C, 299);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if ( S) (posedge C => (Q : 1'b1)) = 796;
		if (!S) (posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L90
		$setup(S, posedge C, 530);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if ( S) (posedge C => (Q : 1'b1)) = 1391;
		if (!S) (posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module SB_DFFS (
	output reg Q,
	input C, S, D
);
	`SB_DFF_INIT

	always @(posedge C, posedge S)
		if (S)
			Q <= 1;
		else
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L63
		$setup(negedge S, posedge C, 160);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L91
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 599;
`else
		if (S) (S => Q) = 599;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (!S) (posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L63
		$setup(negedge S, posedge C, 235);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L91
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 883;
`else
		if (S) (S => Q) = 883;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (!S) (posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L75
		$setup(negedge S, posedge C, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L103
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 1589;
`else
		if (S) (S => Q) = 1589; // Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (!S) (posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFESR (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input R,
	input D
);
	`SB_DFF_INIT

	always @(posedge C)
		if (E) begin
			if (R)
				Q <= 0;
			else
				Q <= D;
		end
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C &&& E && !R, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L78
		$setup(R, posedge C &&& E, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E &&  R) (posedge C => (Q : 1'b0)) = 540;
		if (E && !R) (posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E && !R, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L78
		$setup(R, posedge C &&& E, 299);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E &&  R) (posedge C => (Q : 1'b0)) = 796;
		if (E && !R) (posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L90
		$setup(R, posedge C &&& E, 530);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E &&  R) (posedge C => (Q : 1'b0)) = 1391;
		if (E && !R) (posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module SB_DFFER (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input R,
	input D
);
	`SB_DFF_INIT

	always @(posedge C, posedge R)
		if (R)
			Q <= 0;
		else if (E)
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C &&& E, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L63
		$setup(negedge R, posedge C, 160);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L91
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 599;
`else
		if (R) (R => Q) = 599;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E && !R) (posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L63
		$setup(negedge R, posedge C, 235);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L91
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 883;
`else
		if (R) (R => Q) = 883; 	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E && !R) (posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L75
		$setup(negedge R, posedge C, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L103
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 1589;
`else
		if (R) (R => Q) = 1589;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E && !R) (posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFESS (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input S,
	input D
);
	`SB_DFF_INIT

	always @(posedge C)
		if (E) begin
			if (S)
				Q <= 1;
			else
				Q <= D;
		end
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C &&& E && !S, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L78
		$setup(S, posedge C &&& E, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E &&  S) (posedge C => (Q : 1'b1)) = 540;
		if (E && !S) (posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E && !S, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L78
		$setup(S, posedge C &&& E, 299);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E &&  S) (posedge C => (Q : 1'b1)) = 796;
		if (E && !S) (posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L90
		$setup(S, posedge C &&& E, 530);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E &&  S) (posedge C => (Q : 1'b1)) = 1391;
		if (E && !S) (posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module SB_DFFES (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input S,
	input D
);
	`SB_DFF_INIT

	always @(posedge C, posedge S)
		if (S)
			Q <= 1;
		else if (E)
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, posedge C &&& E, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L63
		$setup(posedge S, posedge C, 160);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L91
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 599;
`else
		if (S) (S => Q) = 599;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E && !S) (posedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L63
		$setup(posedge S, posedge C, 235);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L91
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 883;
`else
		if (S) (S => Q) = 883; // Technically, this should be an edge sensitive path
							   // but for facilitating a bypass box, let's pretend it's
							   // a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E && !S) (posedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, posedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, posedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L75
		$setup(posedge S, posedge C, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L103
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 1589;
`else
		if (S) (S => Q) = 1589; // Technically, this should be an edge sensitive path
							   // but for facilitating a bypass box, let's pretend it's
							   // a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E && !S) (posedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

// Negative Edge SiliconBlue FF Cells

(* abc9_flop, lib_whitebox *)
module SB_DFFN (
	output reg Q,
	input C, D
);
	`SB_DFF_INIT

	always @(negedge C)
		Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		(negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		(negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		(negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFNE (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input D
);
	`SB_DFF_INIT

	always @(negedge C)
		if (E)
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C &&& E, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E) (negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E) (negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E) (negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFNSR (
	output reg Q,
	input C, R, D
);
	`SB_DFF_INIT

	always @(negedge C)
		if (R)
			Q <= 0;
		else
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(R, negedge C, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if ( R) (negedge C => (Q : 1'b0)) = 540;
		if (!R) (negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L78
		$setup(R, negedge C, 299);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if ( R) (negedge C => (Q : 1'b0)) = 796;
		if (!R) (negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L90
		$setup(R, negedge C, 530);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if ( R) (negedge C => (Q : 1'b0)) = 1391;
		if (!R) (negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFNR (
	output reg Q,
	input C, R, D
);
	`SB_DFF_INIT

	always @(negedge C, posedge R)
		if (R)
			Q <= 0;
		else
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L63
		$setup(negedge R, negedge C, 160);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L91
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 599;
`else
		if (R) (R => Q) = 599;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (!R) (negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L63
		$setup(negedge R, negedge C, 235);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L91
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 883;
`else
		if (R) (R => Q) = 883;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (!R) (negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L75
		$setup(negedge R, negedge C, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L103
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 1589;
`else
		if (R) (R => Q) = 1589;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (!R) (negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFNSS (
	output reg Q,
	input C, S, D
);
	`SB_DFF_INIT

	always @(negedge C)
		if (S)
			Q <= 1;
		else
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(S, negedge C, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if ( S) (negedge C => (Q : 1'b1)) = 540;
		if (!S) (negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L78
		$setup(S, negedge C, 299);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if ( S) (negedge C => (Q : 1'b1)) = 796;
		if (!S) (negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L90
		$setup(S, negedge C, 530);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if ( S) (negedge C => (Q : 1'b1)) = 1391;
		if (!S) (negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module SB_DFFNS (
	output reg Q,
	input C, S, D
);
	`SB_DFF_INIT

	always @(negedge C, posedge S)
		if (S)
			Q <= 1;
		else
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L63
		$setup(negedge S, negedge C, 160);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L91
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 599;
`else
		if (S) (S => Q) = 599;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (!S) (negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L63
		$setup(negedge S, negedge C, 235);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L91
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 883;
`else
		if (S) (S => Q) = 883;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (!S) (negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L75
		$setup(negedge S, negedge C, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L103
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 1589;
`else
		if (S) (S => Q) = 1589;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (!S) (negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFNESR (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input R,
	input D
);
	`SB_DFF_INIT

	always @(negedge C)
		if (E) begin
			if (R)
				Q <= 0;
			else
				Q <= D;
		end
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C &&& E && !R, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L78
		$setup(R, negedge C &&& E, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E &&  R) (negedge C => (Q : 1'b0)) = 540;
		if (E && !R) (negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E && !R, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L78
		$setup(R, negedge C &&& E, 299);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E &&  R) (negedge C => (Q : 1'b0)) = 796;
		if (E && !R) (negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L90
		$setup(R, negedge C &&& E, 530);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E &&  R) (negedge C => (Q : 1'b0)) = 1391;
		if (E && !R) (negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module SB_DFFNER (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input R,
	input D
);
	`SB_DFF_INIT

	always @(negedge C, posedge R)
		if (R)
			Q <= 0;
		else if (E)
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C &&& E, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L63
		$setup(R, negedge C, 2160);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L91
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 599;
`else
		if (R) (R => Q) = 599;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E && !R) (negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L63
		$setup(R, negedge C, 235);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L91
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 883;
`else
		if (R) (R => Q) = 883;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E && !R) (negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L75
		$setup(negedge R, negedge C, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L103
`ifndef YOSYS
		(posedge R => (Q : 1'b0)) = 1589;
`else
		if (R) (R => Q) = 1589;	// Technically, this should be an edge sensitive path
					// but for facilitating a bypass box, let's pretend it's
					// a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E && !R) (negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module SB_DFFNESS (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input S,
	input D
);
	`SB_DFF_INIT

	always @(negedge C)
		if (E) begin
			if (S)
				Q <= 1;
			else
				Q <= D;
		end
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C &&& E && !S, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L78
		$setup(S, negedge C &&& E, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E &&  S) (negedge C => (Q : 1'b1)) = 540;
		if (E && !S) (negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E && !S, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L78
		$setup(S, negedge C &&& E, 299);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E &&  S) (negedge C => (Q : 1'b1)) = 796;
		if (E && !S) (negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L90
		$setup(S, negedge C &&& E, 530);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E &&  S) (negedge C => (Q : 1'b1)) = 1391;
		if (E && !S) (negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module SB_DFFNES (
	output reg Q,
	input C,
	input E `ICE40_DEFAULT_ASSIGNMENT_1,
	input S,
	input D
);
	`SB_DFF_INIT

	always @(negedge C, posedge S)
		if (S)
			Q <= 1;
		else if (E)
			Q <= D;
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
		$setup(D, negedge C &&& E, 470 - 449);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L63
		$setup(negedge S, negedge C, 160);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L91
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 599;
`else
        if (S) (S => Q) = 599; // Technically, this should be an edge sensitive path
                               // but for facilitating a bypass box, let's pretend it's
                               // a simple path
`endif

		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
		if (E && !S) (negedge C => (Q : D)) = 540;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E, 693 - 662);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L63
		$setup(negedge S, negedge C, 235);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L91
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 883;
`else
        if (S) (S => Q) = 883; // Technically, this should be an edge sensitive path
                               // but for facilitating a bypass box, let's pretend it's
                               // a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
		if (E && !S) (negedge C => (Q : D)) = 796;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
		//   minus https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
		$setup(D, negedge C &&& E, /*1232 - 1285*/ 0); // Negative times not currently supported
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
		$setup(E, negedge C, 0);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L75
		$setup(negedge S, negedge C, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L103
`ifndef YOSYS
		(posedge S => (Q : 1'b1)) = 1589;
`else
        if (S) (S => Q) = 1589; // Technically, this should be an edge sensitive path
                               // but for facilitating a bypass box, let's pretend it's
                               // a simple path
`endif
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
		if (E && !S) (negedge C => (Q : D)) = 1391;
	endspecify
`endif
endmodule

// SiliconBlue RAM Cells

module SB_RAM40_4K (
	output [15:0] RDATA,
	input         RCLK,
	input         RCLKE `ICE40_DEFAULT_ASSIGNMENT_1,
	input         RE `ICE40_DEFAULT_ASSIGNMENT_0,
	input  [10:0] RADDR,
	input         WCLK,
	input         WCLKE `ICE40_DEFAULT_ASSIGNMENT_1,
	input         WE `ICE40_DEFAULT_ASSIGNMENT_0,
	input  [10:0] WADDR,
	input  [15:0] MASK `ICE40_DEFAULT_ASSIGNMENT_V(16'h 0000),
	input  [15:0] WDATA
);
	// MODE 0:  256 x 16
	// MODE 1:  512 x 8
	// MODE 2: 1024 x 4
	// MODE 3: 2048 x 2
	parameter WRITE_MODE = 0;
	parameter READ_MODE = 0;

	parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

	parameter INIT_FILE = "";

`ifndef BLACKBOX
	wire [15:0] WMASK_I;
	wire [15:0] RMASK_I;

	reg  [15:0] RDATA_I;
	wire [15:0] WDATA_I;

	generate
		case (WRITE_MODE)
			0: assign WMASK_I = MASK;

			1: assign WMASK_I = WADDR[   8] == 0 ? 16'b 1010_1010_1010_1010 :
			                    WADDR[   8] == 1 ? 16'b 0101_0101_0101_0101 : 16'bx;

			2: assign WMASK_I = WADDR[ 9:8] == 0 ? 16'b 1110_1110_1110_1110 :
			                    WADDR[ 9:8] == 1 ? 16'b 1101_1101_1101_1101 :
			                    WADDR[ 9:8] == 2 ? 16'b 1011_1011_1011_1011 :
			                    WADDR[ 9:8] == 3 ? 16'b 0111_0111_0111_0111 : 16'bx;

			3: assign WMASK_I = WADDR[10:8] == 0 ? 16'b 1111_1110_1111_1110 :
			                    WADDR[10:8] == 1 ? 16'b 1111_1101_1111_1101 :
			                    WADDR[10:8] == 2 ? 16'b 1111_1011_1111_1011 :
			                    WADDR[10:8] == 3 ? 16'b 1111_0111_1111_0111 :
			                    WADDR[10:8] == 4 ? 16'b 1110_1111_1110_1111 :
			                    WADDR[10:8] == 5 ? 16'b 1101_1111_1101_1111 :
			                    WADDR[10:8] == 6 ? 16'b 1011_1111_1011_1111 :
			                    WADDR[10:8] == 7 ? 16'b 0111_1111_0111_1111 : 16'bx;
		endcase

		case (READ_MODE)
			0: assign RMASK_I = 16'b 0000_0000_0000_0000;

			1: assign RMASK_I = RADDR[   8] == 0 ? 16'b 1010_1010_1010_1010 :
			                    RADDR[   8] == 1 ? 16'b 0101_0101_0101_0101 : 16'bx;

			2: assign RMASK_I = RADDR[ 9:8] == 0 ? 16'b 1110_1110_1110_1110 :
			                    RADDR[ 9:8] == 1 ? 16'b 1101_1101_1101_1101 :
			                    RADDR[ 9:8] == 2 ? 16'b 1011_1011_1011_1011 :
			                    RADDR[ 9:8] == 3 ? 16'b 0111_0111_0111_0111 : 16'bx;

			3: assign RMASK_I = RADDR[10:8] == 0 ? 16'b 1111_1110_1111_1110 :
			                    RADDR[10:8] == 1 ? 16'b 1111_1101_1111_1101 :
			                    RADDR[10:8] == 2 ? 16'b 1111_1011_1111_1011 :
			                    RADDR[10:8] == 3 ? 16'b 1111_0111_1111_0111 :
			                    RADDR[10:8] == 4 ? 16'b 1110_1111_1110_1111 :
			                    RADDR[10:8] == 5 ? 16'b 1101_1111_1101_1111 :
			                    RADDR[10:8] == 6 ? 16'b 1011_1111_1011_1111 :
			                    RADDR[10:8] == 7 ? 16'b 0111_1111_0111_1111 : 16'bx;
		endcase

		case (WRITE_MODE)
			0: assign WDATA_I = WDATA;

			1: assign WDATA_I = {WDATA[14], WDATA[14], WDATA[12], WDATA[12],
			                     WDATA[10], WDATA[10], WDATA[ 8], WDATA[ 8],
			                     WDATA[ 6], WDATA[ 6], WDATA[ 4], WDATA[ 4],
			                     WDATA[ 2], WDATA[ 2], WDATA[ 0], WDATA[ 0]};

			2: assign WDATA_I = {WDATA[13], WDATA[13], WDATA[13], WDATA[13],
			                     WDATA[ 9], WDATA[ 9], WDATA[ 9], WDATA[ 9],
			                     WDATA[ 5], WDATA[ 5], WDATA[ 5], WDATA[ 5],
			                     WDATA[ 1], WDATA[ 1], WDATA[ 1], WDATA[ 1]};

			3: assign WDATA_I = {WDATA[11], WDATA[11], WDATA[11], WDATA[11],
			                     WDATA[11], WDATA[11], WDATA[11], WDATA[11],
			                     WDATA[ 3], WDATA[ 3], WDATA[ 3], WDATA[ 3],
			                     WDATA[ 3], WDATA[ 3], WDATA[ 3], WDATA[ 3]};
		endcase

		case (READ_MODE)
			0: assign RDATA = RDATA_I;
			1: assign RDATA = {1'b0, |RDATA_I[15:14], 1'b0, |RDATA_I[13:12], 1'b0, |RDATA_I[11:10], 1'b0, |RDATA_I[ 9: 8],
			                   1'b0, |RDATA_I[ 7: 6], 1'b0, |RDATA_I[ 5: 4], 1'b0, |RDATA_I[ 3: 2], 1'b0, |RDATA_I[ 1: 0]};
			2: assign RDATA = {2'b0, |RDATA_I[15:12], 3'b0, |RDATA_I[11: 8], 3'b0, |RDATA_I[ 7: 4], 3'b0, |RDATA_I[ 3: 0], 1'b0};
			3: assign RDATA = {4'b0, |RDATA_I[15: 8], 7'b0, |RDATA_I[ 7: 0], 3'b0};
		endcase
	endgenerate

	integer i;
	reg [15:0] memory [0:255];

	initial begin
		if (INIT_FILE != "")
			$readmemh(INIT_FILE, memory);
		else
			for (i=0; i<16; i=i+1) begin
				memory[ 0*16 + i] = INIT_0[16*i +: 16];
				memory[ 1*16 + i] = INIT_1[16*i +: 16];
				memory[ 2*16 + i] = INIT_2[16*i +: 16];
				memory[ 3*16 + i] = INIT_3[16*i +: 16];
				memory[ 4*16 + i] = INIT_4[16*i +: 16];
				memory[ 5*16 + i] = INIT_5[16*i +: 16];
				memory[ 6*16 + i] = INIT_6[16*i +: 16];
				memory[ 7*16 + i] = INIT_7[16*i +: 16];
				memory[ 8*16 + i] = INIT_8[16*i +: 16];
				memory[ 9*16 + i] = INIT_9[16*i +: 16];
				memory[10*16 + i] = INIT_A[16*i +: 16];
				memory[11*16 + i] = INIT_B[16*i +: 16];
				memory[12*16 + i] = INIT_C[16*i +: 16];
				memory[13*16 + i] = INIT_D[16*i +: 16];
				memory[14*16 + i] = INIT_E[16*i +: 16];
				memory[15*16 + i] = INIT_F[16*i +: 16];
			end
	end

	always @(posedge WCLK) begin
		if (WE && WCLKE) begin
			if (!WMASK_I[ 0]) memory[WADDR[7:0]][ 0] <= WDATA_I[ 0];
			if (!WMASK_I[ 1]) memory[WADDR[7:0]][ 1] <= WDATA_I[ 1];
			if (!WMASK_I[ 2]) memory[WADDR[7:0]][ 2] <= WDATA_I[ 2];
			if (!WMASK_I[ 3]) memory[WADDR[7:0]][ 3] <= WDATA_I[ 3];
			if (!WMASK_I[ 4]) memory[WADDR[7:0]][ 4] <= WDATA_I[ 4];
			if (!WMASK_I[ 5]) memory[WADDR[7:0]][ 5] <= WDATA_I[ 5];
			if (!WMASK_I[ 6]) memory[WADDR[7:0]][ 6] <= WDATA_I[ 6];
			if (!WMASK_I[ 7]) memory[WADDR[7:0]][ 7] <= WDATA_I[ 7];
			if (!WMASK_I[ 8]) memory[WADDR[7:0]][ 8] <= WDATA_I[ 8];
			if (!WMASK_I[ 9]) memory[WADDR[7:0]][ 9] <= WDATA_I[ 9];
			if (!WMASK_I[10]) memory[WADDR[7:0]][10] <= WDATA_I[10];
			if (!WMASK_I[11]) memory[WADDR[7:0]][11] <= WDATA_I[11];
			if (!WMASK_I[12]) memory[WADDR[7:0]][12] <= WDATA_I[12];
			if (!WMASK_I[13]) memory[WADDR[7:0]][13] <= WDATA_I[13];
			if (!WMASK_I[14]) memory[WADDR[7:0]][14] <= WDATA_I[14];
			if (!WMASK_I[15]) memory[WADDR[7:0]][15] <= WDATA_I[15];
		end
	end

	always @(posedge RCLK) begin
		if (RE && RCLKE) begin
			RDATA_I <= memory[RADDR[7:0]] & ~RMASK_I;
		end
	end
`endif
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L343-L358
		$setup(MASK, posedge WCLK &&& WE && WCLKE, 274);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L359-L369
		$setup(RADDR, posedge RCLK &&& RE && RCLKE, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L370
		$setup(RCLKE, posedge RCLK, 267);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L371
		$setup(RE, posedge RCLK, 98);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L372-L382
		$setup(WADDR, posedge WCLK &&& WE && WCLKE, 224);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L383
		$setup(WCLKE, posedge WCLK, 267);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L384-L399
		$setup(WDATA, posedge WCLK &&& WE && WCLKE, 161);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L400
		$setup(WE, posedge WCLK, 133);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L401
		(posedge RCLK => (RDATA : 16'bx)) = 2146;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L343-L358
		$setup(MASK, posedge WCLK &&& WE && WCLKE, 403);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L359-L369
		$setup(RADDR, posedge RCLK &&& RE && RCLKE, 300);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L370
		$setup(RCLKE, posedge RCLK, 393);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L371
		$setup(RE, posedge RCLK, 145);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L372-L382
		$setup(WADDR, posedge WCLK &&& WE && WCLKE, 331);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L383
		$setup(WCLKE, posedge WCLK, 393);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L384-L399
		$setup(WDATA, posedge WCLK &&& WE && WCLKE, 238);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L400
		$setup(WE, posedge WCLK, 196);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L401
		(posedge RCLK => (RDATA : 16'bx)) = 3163;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12968-12983
		$setup(MASK, posedge WCLK &&& WE && WCLKE, 517);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12984-12994
		$setup(RADDR, posedge RCLK &&& RE && RCLKE, 384);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12995
		$setup(RCLKE, posedge RCLK, 503);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12996
		$setup(RE, posedge RCLK, 185);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12997-13007
		$setup(WADDR, posedge WCLK &&& WE && WCLKE, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13008
		$setup(WCLKE, posedge WCLK, 503);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13009-13024
		$setup(WDATA, posedge WCLK &&& WE && WCLKE, 305);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13025
		$setup(WE, posedge WCLK, 252);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13026
		(posedge RCLK => (RDATA : 16'bx)) = 1179;
	endspecify
`endif
endmodule

module SB_RAM40_4KNR (
	output [15:0] RDATA,
	input         RCLKN,
	input         RCLKE `ICE40_DEFAULT_ASSIGNMENT_1,
	input         RE `ICE40_DEFAULT_ASSIGNMENT_0,
	input  [10:0] RADDR,
	input         WCLK,
	input         WCLKE `ICE40_DEFAULT_ASSIGNMENT_1,
	input         WE `ICE40_DEFAULT_ASSIGNMENT_0,
	input  [10:0] WADDR,
	input  [15:0] MASK `ICE40_DEFAULT_ASSIGNMENT_V(16'h 0000),
	input  [15:0] WDATA
);
	parameter WRITE_MODE = 0;
	parameter READ_MODE = 0;

	parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

	parameter INIT_FILE = "";

	SB_RAM40_4K #(
		.WRITE_MODE(WRITE_MODE),
		.READ_MODE (READ_MODE ),
		.INIT_0    (INIT_0    ),
		.INIT_1    (INIT_1    ),
		.INIT_2    (INIT_2    ),
		.INIT_3    (INIT_3    ),
		.INIT_4    (INIT_4    ),
		.INIT_5    (INIT_5    ),
		.INIT_6    (INIT_6    ),
		.INIT_7    (INIT_7    ),
		.INIT_8    (INIT_8    ),
		.INIT_9    (INIT_9    ),
		.INIT_A    (INIT_A    ),
		.INIT_B    (INIT_B    ),
		.INIT_C    (INIT_C    ),
		.INIT_D    (INIT_D    ),
		.INIT_E    (INIT_E    ),
		.INIT_F    (INIT_F    ),
		.INIT_FILE (INIT_FILE )
	) RAM (
		.RDATA(RDATA),
		.RCLK (~RCLKN),
		.RCLKE(RCLKE),
		.RE   (RE   ),
		.RADDR(RADDR),
		.WCLK (WCLK ),
		.WCLKE(WCLKE),
		.WE   (WE   ),
		.WADDR(WADDR),
		.MASK (MASK ),
		.WDATA(WDATA)
	);
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L343-L358
		$setup(MASK, posedge WCLK &&& WE && WCLKE, 274);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L359-L369
		$setup(RADDR, posedge RCLKN &&& RE && RCLKE, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L370
		$setup(RCLKE, posedge RCLKN, 267);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L371
		$setup(RE, posedge RCLKN, 98);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L372-L382
		$setup(WADDR, posedge WCLK &&& WE && WCLKE, 224);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L383
		$setup(WCLKE, posedge WCLK, 267);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L384-L399
		$setup(WDATA, posedge WCLK &&& WE && WCLKE, 161);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L400
		$setup(WE, posedge WCLK, 133);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L401
		(posedge RCLKN => (RDATA : 16'bx)) = 2146;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L343-L358
		$setup(MASK, posedge WCLK &&& WE && WCLKE, 403);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L359-L369
		$setup(RADDR, posedge RCLKN &&& RE && RCLKE, 300);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L370
		$setup(RCLKE, posedge RCLKN, 393);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L371
		$setup(RE, posedge RCLKN, 145);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L372-L382
		$setup(WADDR, posedge WCLK &&& WE && WCLKE, 331);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L383
		$setup(WCLKE, posedge WCLK, 393);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L384-L399
		$setup(WDATA, posedge WCLK &&& WE && WCLKE, 238);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L400
		$setup(WE, posedge WCLK, 196);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L401
		(posedge RCLKN => (RDATA : 16'bx)) = 3163;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12968-12983
		$setup(MASK, posedge WCLK &&& WE && WCLKE, 517);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12984-12994
		$setup(RADDR, posedge RCLKN &&& RE && RCLKE, 384);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12995
		$setup(RCLKE, posedge RCLKN, 503);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12996
		$setup(RE, posedge RCLKN, 185);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12997-13007
		$setup(WADDR, posedge WCLK &&& WE && WCLKE, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13008
		$setup(WCLKE, posedge WCLK, 503);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13009-13024
		$setup(WDATA, posedge WCLK &&& WE && WCLKE, 305);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13025
		$setup(WE, posedge WCLK, 252);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13026
		(posedge RCLKN => (RDATA : 16'bx)) = 1179;
	endspecify
`endif
endmodule

module SB_RAM40_4KNW (
	output [15:0] RDATA,
	input         RCLK,
	input         RCLKE `ICE40_DEFAULT_ASSIGNMENT_1,
	input         RE `ICE40_DEFAULT_ASSIGNMENT_0,
	input  [10:0] RADDR,
	input         WCLKN,
	input         WCLKE `ICE40_DEFAULT_ASSIGNMENT_1,
	input         WE `ICE40_DEFAULT_ASSIGNMENT_0,
	input  [10:0] WADDR,
	input  [15:0] MASK `ICE40_DEFAULT_ASSIGNMENT_V(16'h 0000),
	input  [15:0] WDATA
);
	parameter WRITE_MODE = 0;
	parameter READ_MODE = 0;

	parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

	parameter INIT_FILE = "";

	SB_RAM40_4K #(
		.WRITE_MODE(WRITE_MODE),
		.READ_MODE (READ_MODE ),
		.INIT_0    (INIT_0    ),
		.INIT_1    (INIT_1    ),
		.INIT_2    (INIT_2    ),
		.INIT_3    (INIT_3    ),
		.INIT_4    (INIT_4    ),
		.INIT_5    (INIT_5    ),
		.INIT_6    (INIT_6    ),
		.INIT_7    (INIT_7    ),
		.INIT_8    (INIT_8    ),
		.INIT_9    (INIT_9    ),
		.INIT_A    (INIT_A    ),
		.INIT_B    (INIT_B    ),
		.INIT_C    (INIT_C    ),
		.INIT_D    (INIT_D    ),
		.INIT_E    (INIT_E    ),
		.INIT_F    (INIT_F    ),
		.INIT_FILE (INIT_FILE )
	) RAM (
		.RDATA(RDATA),
		.RCLK (RCLK ),
		.RCLKE(RCLKE),
		.RE   (RE   ),
		.RADDR(RADDR),
		.WCLK (~WCLKN),
		.WCLKE(WCLKE),
		.WE   (WE   ),
		.WADDR(WADDR),
		.MASK (MASK ),
		.WDATA(WDATA)
	);
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L343-L358
		$setup(MASK, posedge WCLKN &&& WE && WCLKE, 274);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L359-L369
		$setup(RADDR, posedge RCLK &&& RE && RCLKE, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L370
		$setup(RCLKE, posedge RCLK, 267);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L371
		$setup(RE, posedge RCLK, 98);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L372-L382
		$setup(WADDR, posedge WCLKN &&& WE && WCLKE, 224);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L383
		$setup(WCLKE, posedge WCLKN, 267);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L384-L399
		$setup(WDATA, posedge WCLKN &&& WE && WCLKE, 161);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L400
		$setup(WE, posedge WCLKN, 133);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L401
		(posedge RCLK => (RDATA : 16'bx)) = 2146;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L343-L358
		$setup(MASK, posedge WCLKN &&& WE && WCLKE, 403);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L359-L369
		$setup(RADDR, posedge RCLK &&& RE && RCLKE, 300);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L370
		$setup(RCLKE, posedge RCLK, 393);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L371
		$setup(RE, posedge RCLK, 145);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L372-L382
		$setup(WADDR, posedge WCLKN &&& WE && WCLKE, 331);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L383
		$setup(WCLKE, posedge WCLKN, 393);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L384-L399
		$setup(WDATA, posedge WCLKN &&& WE && WCLKE, 238);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L400
		$setup(WE, posedge WCLKN, 196);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L401
		(posedge RCLK => (RDATA : 16'bx)) = 3163;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12968-12983
		$setup(MASK, posedge WCLKN &&& WE && WCLKE, 517);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12984-12994
		$setup(RADDR, posedge RCLK &&& RE && RCLKE, 384);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12995
		$setup(RCLKE, posedge RCLK, 503);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12996
		$setup(RE, posedge RCLK, 185);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12997-13007
		$setup(WADDR, posedge WCLKN &&& WE && WCLKE, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13008
		$setup(WCLKE, posedge WCLKN, 503);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13009-13024
		$setup(WDATA, posedge WCLKN &&& WE && WCLKE, 305);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13025
		$setup(WE, posedge WCLKN, 252);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13026
		(posedge RCLK => (RDATA : 16'bx)) = 1179;
	endspecify
`endif
endmodule

module SB_RAM40_4KNRNW (
	output [15:0] RDATA,
	input         RCLKN,
	input         RCLKE `ICE40_DEFAULT_ASSIGNMENT_1,
	input         RE `ICE40_DEFAULT_ASSIGNMENT_0,
	input  [10:0] RADDR,
	input         WCLKN,
	input         WCLKE `ICE40_DEFAULT_ASSIGNMENT_1,
	input         WE `ICE40_DEFAULT_ASSIGNMENT_0,
	input  [10:0] WADDR,
	input  [15:0] MASK `ICE40_DEFAULT_ASSIGNMENT_V(16'h 0000),
	input  [15:0] WDATA
);
	parameter WRITE_MODE = 0;
	parameter READ_MODE = 0;

	parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

	parameter INIT_FILE = "";

	SB_RAM40_4K #(
		.WRITE_MODE(WRITE_MODE),
		.READ_MODE (READ_MODE ),
		.INIT_0    (INIT_0    ),
		.INIT_1    (INIT_1    ),
		.INIT_2    (INIT_2    ),
		.INIT_3    (INIT_3    ),
		.INIT_4    (INIT_4    ),
		.INIT_5    (INIT_5    ),
		.INIT_6    (INIT_6    ),
		.INIT_7    (INIT_7    ),
		.INIT_8    (INIT_8    ),
		.INIT_9    (INIT_9    ),
		.INIT_A    (INIT_A    ),
		.INIT_B    (INIT_B    ),
		.INIT_C    (INIT_C    ),
		.INIT_D    (INIT_D    ),
		.INIT_E    (INIT_E    ),
		.INIT_F    (INIT_F    ),
		.INIT_FILE (INIT_FILE )
	) RAM (
		.RDATA(RDATA),
		.RCLK (~RCLKN),
		.RCLKE(RCLKE),
		.RE   (RE   ),
		.RADDR(RADDR),
		.WCLK (~WCLKN),
		.WCLKE(WCLKE),
		.WE   (WE   ),
		.WADDR(WADDR),
		.MASK (MASK ),
		.WDATA(WDATA)
	);
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L343-L358
		$setup(MASK, posedge WCLKN &&& WE && WCLKE, 274);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L359-L369
		$setup(RADDR, posedge RCLKN &&& RE && RCLKE, 203);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L370
		$setup(RCLKE, posedge RCLKN, 267);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L371
		$setup(RE, posedge RCLKN, 98);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L372-L382
		$setup(WADDR, posedge WCLKN &&& WE && WCLKE, 224);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L383
		$setup(WCLKE, posedge WCLKN, 267);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L384-L399
		$setup(WDATA, posedge WCLKN &&& WE && WCLKE, 161);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L400
		$setup(WE, posedge WCLKN, 133);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L401
		(posedge RCLKN => (RDATA : 16'bx)) = 2146;
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L343-L358
		$setup(MASK, posedge WCLKN &&& WE && WCLKE, 403);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L359-L369
		$setup(RADDR, posedge RCLKN &&& RE && RCLKE, 300);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L370
		$setup(RCLKE, posedge RCLKN, 393);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L371
		$setup(RE, posedge RCLKN, 145);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L372-L382
		$setup(WADDR, posedge WCLKN &&& WE && WCLKE, 331);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L383
		$setup(WCLKE, posedge WCLKN, 393);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L384-L399
		$setup(WDATA, posedge WCLKN &&& WE && WCLKE, 238);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L400
		$setup(WE, posedge WCLKN, 196);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L401
		(posedge RCLKN => (RDATA : 16'bx)) = 3163;
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12968-12983
		$setup(MASK, posedge WCLKN &&& WE && WCLKE, 517);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12984-12994
		$setup(RADDR, posedge RCLKN &&& RE && RCLKE, 384);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12995
		$setup(RCLKE, posedge RCLKN, 503);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12996
		$setup(RE, posedge RCLKN, 185);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L12997-13007
		$setup(WADDR, posedge WCLKN &&& WE && WCLKE, 424);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13008
		$setup(WCLKE, posedge WCLKN, 503);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13009-13024
		$setup(WDATA, posedge WCLKN &&& WE && WCLKE, 305);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13025
		$setup(WE, posedge WCLKN, 252);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13026
		(posedge RCLKN => (RDATA : 16'bx)) = 1179;
	endspecify
`endif
endmodule

// Packed IceStorm Logic Cells

module ICESTORM_LC (
	input I0, I1, I2, I3, CIN, CLK, CEN, SR,
	output LO,
	output O,
	output COUT
);
	parameter [15:0] LUT_INIT = 0;

	parameter [0:0] NEG_CLK      = 0;
	parameter [0:0] CARRY_ENABLE = 0;
	parameter [0:0] DFF_ENABLE   = 0;
	parameter [0:0] SET_NORESET  = 0;
	parameter [0:0] ASYNC_SR     = 0;

	parameter [0:0] CIN_CONST    = 0;
	parameter [0:0] CIN_SET      = 0;

	wire I0_pd = (I0 === 1'bz) ? 1'b0 : I0;
	wire I1_pd = (I1 === 1'bz) ? 1'b0 : I1;
	wire I2_pd = (I2 === 1'bz) ? 1'b0 : I2;
	wire I3_pd = (I3 === 1'bz) ? 1'b0 : I3;
	wire SR_pd = (SR === 1'bz) ? 1'b0 : SR;
	wire CEN_pu = (CEN === 1'bz) ? 1'b1 : CEN;

	wire mux_cin = CIN_CONST ? CIN_SET : CIN;

	assign COUT = CARRY_ENABLE ? (I1_pd && I2_pd) || ((I1_pd || I2_pd) && mux_cin) : 1'bx;

	wire [7:0] lut_s3 = I3_pd ? LUT_INIT[15:8] : LUT_INIT[7:0];
	wire [3:0] lut_s2 = I2_pd ?   lut_s3[ 7:4] :   lut_s3[3:0];
	wire [1:0] lut_s1 = I1_pd ?   lut_s2[ 3:2] :   lut_s2[1:0];
	wire       lut_o  = I0_pd ?   lut_s1[   1] :   lut_s1[  0];

	assign LO = lut_o;

	wire polarized_clk;
	assign polarized_clk = CLK ^ NEG_CLK;

	reg o_reg = 1'b0;
	always @(posedge polarized_clk)
		if (CEN_pu)
			o_reg <= SR_pd ? SET_NORESET : lut_o;

	reg o_reg_async = 1'b0;
	always @(posedge polarized_clk, posedge SR_pd)
		if (SR_pd)
			o_reg_async <= SET_NORESET;
		else if (CEN_pu)
			o_reg_async <= lut_o;

	assign O = DFF_ENABLE ? ASYNC_SR ? o_reg_async : o_reg : lut_o;
`ifdef TIMING
specify
	(I0 => O) = (0:0:0, 0:0:0);
	(I1 => O) = (0:0:0, 0:0:0);
	(I2 => O) = (0:0:0, 0:0:0);
	(I3 => O) = (0:0:0, 0:0:0);
	(I0 => LO) = (0:0:0, 0:0:0);
	(I1 => LO) = (0:0:0, 0:0:0);
	(I2 => LO) = (0:0:0, 0:0:0);
	(I3 => LO) = (0:0:0, 0:0:0);
	(I1 => COUT) = (0:0:0, 0:0:0);
	(I2 => COUT) = (0:0:0, 0:0:0);
	(CIN => COUT) = (0:0:0, 0:0:0);
	(CLK => O) = (0:0:0, 0:0:0);
	(SR => O) = (0:0:0, 0:0:0);
	$setuphold(posedge CLK, posedge I0, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, negedge I0, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, posedge I0, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, negedge I0, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, posedge I1, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, negedge I1, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, posedge I1, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, negedge I1, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, posedge I2, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, negedge I2, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, posedge I2, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, negedge I2, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, posedge I3, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, negedge I3, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, posedge I3, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, negedge I3, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, posedge CEN, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, negedge CEN, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, posedge CEN, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, negedge CEN, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, posedge SR, 0:0:0, 0:0:0);
	$setuphold(posedge CLK, negedge SR, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, posedge SR, 0:0:0, 0:0:0);
	$setuphold(negedge CLK, negedge SR, 0:0:0, 0:0:0);
endspecify
`endif
`ifdef ICE40_HX
specify
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L79
	(CIN => COUT) = (101:112:126, 85:94:105);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L80
	(I0 => O) = (361:399:449, 310:343:386);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L81
	(I0 => LO) = (293:324:365, 310:343:386);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L82
	(I1 => COUT) = (209:231:259, 197:218:245);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L83
	(I1 => O) = (321:355:400, 304:337:379);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L84
	(I1 => LO) = (259:287:323, 304:337:379);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L85
	(I2 => COUT) = (186:206:231, 107:118:133);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L86
	(I2 => O) = (304:337:379, 282:312:351);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L87
	(I2 => LO) = (254:281:316, 231:256:288);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L88
	(I3 => O) = (254:281:316, 231:256:288);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L89
	(I3 => LO) = (214:237:267, 220:243:274);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L90
	(posedge CLK => (O : 1'bx)) = (434:480:540, 434:480:540);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L91-L92
	(SR => O) = (482:535:599, 482:533:599);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L74
	$setuphold(posedge CLK, posedge I0, 378:418:470, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L68
	$setuphold(posedge CLK, negedge I0, 321:355:400, 0:0:0);
	$setuphold(negedge CLK, posedge I0, 378:418:470, 0:0:0);
	$setuphold(negedge CLK, negedge I0, 321:355:400, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L75
	$setuphold(posedge CLK, posedge I1, 321:355:400, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L69
	$setuphold(posedge CLK, negedge I1, 304:337:379, 0:0:0);
	$setuphold(negedge CLK, posedge I1, 321:355:400, 0:0:0);
	$setuphold(negedge CLK, negedge I1, 304:337:379, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L76
	$setuphold(posedge CLK, posedge I2, 299:330:372, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L70
	$setuphold(posedge CLK, negedge I2, 259:287:323, 0:0:0);
	$setuphold(negedge CLK, posedge I2, 299:330:372, 0:0:0);
	$setuphold(negedge CLK, negedge I2, 259:287:323, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L77
	$setuphold(posedge CLK, posedge I3, 220:243:274, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L71
	$setuphold(posedge CLK, negedge I3, 175:183:217, 0:0:0);
	$setuphold(negedge CLK, posedge I3, 220:243:274, 0:0:0);
	$setuphold(negedge CLK, negedge I3, 175:183:217, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L73
	$setuphold(posedge CLK, negedge CEN, 0:0:0, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L67
	$setuphold(posedge CLK, posedge CEN, 0:0:0, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L78
	$setuphold(posedge CLK, posedge SR, 163:181:203, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_hx1k.txt#L72
	$setuphold(posedge CLK, negedge SR, 113:125:140, 0:0:0);
	$setuphold(negedge CLK, posedge SR, 163:181:203, 0:0:0);
	$setuphold(negedge CLK, negedge SR, 113:125:140, 0:0:0);
endspecify
`endif
`ifdef ICE40_LP
specify
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L79
	(CIN => COUT) = (118:153:186, 98:128:155);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L80
	(I0 => O) = (419:545:662, 360:468:569);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L81
	(I0 => LO) = (340:442:538, 360:468:569);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L82
	(I1 => COUT) = (242:315:382, 229:298:362);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L83
	(I1 => O) = (372:485:589, 353:459:558);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L84
	(I1 => LO) = (301:391:475, 353:459:558);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L85
	(I2 => COUT) = (216:281:341, 124:162:196);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L86
	(I2 => O) = (353:459:558, 327:425:517);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L87
	(I2 => LO) = (288:374:455, 321:417:507);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L88
	(I3 => O) = (294:383:465, 268:349:424);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L89
	(I3 => LO) = (249:323:393, 255:332:403);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L90
	(posedge CLK => (O : 1'bx)) = (504:655:796, 504:655:796);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L91-L92
	(SR => O) = (559:726:883, 559:726:883);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L74
	$setuphold(posedge CLK, posedge I0, 438:570:693, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L68
	$setuphold(posedge CLK, negedge I0, 373:485:589, 0:0:0);
	$setuphold(negedge CLK, posedge I0, 438:570:693, 0:0:0);
	$setuphold(negedge CLK, negedge I0, 373:485:589, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L75
	$setuphold(posedge CLK, posedge I1, 373:485:589, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L69
	$setuphold(posedge CLK, negedge I1, 353:459:558, 0:0:0);
	$setuphold(negedge CLK, posedge I1, 373:485:589, 0:0:0);
	$setuphold(negedge CLK, negedge I1, 353:459:558, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L76
	$setuphold(posedge CLK, posedge I2, 347:451:548, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L70
	$setuphold(posedge CLK, negedge I2, 301:391:475, 0:0:0);
	$setuphold(negedge CLK, posedge I2, 347:451:548, 0:0:0);
	$setuphold(negedge CLK, negedge I2, 301:391:475, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L77
	$setuphold(posedge CLK, posedge I3, 255:332:403, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L71
	$setuphold(posedge CLK, negedge I3, 203:264:320, 0:0:0);
	$setuphold(negedge CLK, posedge I3, 255:332:403, 0:0:0);
	$setuphold(negedge CLK, negedge I3, 203:264:320, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L73
	$setuphold(posedge CLK, negedge CEN, 0:0:0, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L67
	$setuphold(posedge CLK, posedge CEN, 0:0:0, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L78
	$setuphold(posedge CLK, posedge SR, 190:247:300, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_lp1k.txt#L72
	$setuphold(posedge CLK, negedge SR, 131:170:207, 0:0:0);
	$setuphold(negedge CLK, posedge SR, 190:247:300, 0:0:0);
	$setuphold(negedge CLK, negedge SR, 131:170:207, 0:0:0);
endspecify
`endif
`ifdef ICE40_U
specify
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L91
	(CIN => COUT) = (103:181:278, 103:181:278);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L92
	(I0 => O) = (462:808:1255, 477:834:1285);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L93
	(I0 => LO) = (315:550:848, 334:585:901);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L94
	(I1 => COUT) = (251:438:675, 246:430:662);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L95
	(I1 => O) = (438:765:1179, 457:799:1232);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L96
	(I1 => LO) = (275:481:742, 329:576:887);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L97
	(I2 => COUT) = (226:395:609, 133:232:358);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L98
	(I2 => O) = (438:765:1179, 447:782:1205);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L99
	(I2 => LO) = (261:456:702, 290:507:781);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L100
	(I3 => O) = (320:559:861, 226:370:874);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L101
	(I3 => LO) = (216:378:583, 226:395:609);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L102
	(posedge CLK => (O : 1'bx)) = (516:903:1391, 516:903:1391);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L103-104
	(SR => O) = (420:734:1131, 590:1032:1589);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L86
	$setuphold(posedge CLK, posedge I0, 457:799:1232, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L80
	$setuphold(posedge CLK, negedge I0, 393:688:1060, 0:0:0);
	$setuphold(negedge CLK, posedge I0, 457:799:1232, 0:0:0);
	$setuphold(negedge CLK, negedge I0, 393:688:1060, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L87
	$setuphold(posedge CLK, posedge I1, 393:688:1060, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L81
	$setuphold(posedge CLK, negedge I1, 373:653:1007, 0:0:0);
	$setuphold(negedge CLK, posedge I1, 393:688:1060, 0:0:0);
	$setuphold(negedge CLK, negedge I1, 373:653:1007, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L88
	$setuphold(posedge CLK, posedge I2, 364:636:980, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L82
	$setuphold(posedge CLK, negedge I2, 320:559:861, 0:0:0);
	$setuphold(negedge CLK, posedge I2, 364:636:980, 0:0:0);
	$setuphold(negedge CLK, negedge I2, 320:559:861, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L89
	$setuphold(posedge CLK, posedge I3, 279:473:728, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L83
	$setuphold(posedge CLK, negedge I3, 216:378:583, 0:0:0);
	$setuphold(negedge CLK, posedge I3, 279:473:728, 0:0:0);
	$setuphold(negedge CLK, negedge I3, 216:378:583, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L85
	$setuphold(posedge CLK, negedge CEN, 0:0:0, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L79
	$setuphold(posedge CLK, posedge CEN, 0:0:0, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L90
	$setuphold(posedge CLK, posedge SR, 197:344:530, 0:0:0);
	// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L84
	$setuphold(posedge CLK, negedge SR, 143:249:384, 0:0:0);
	$setuphold(negedge CLK, posedge SR, 197:344:530, 0:0:0);
	$setuphold(negedge CLK, negedge SR, 131:170:207, 0:0:0);
endspecify
`endif
endmodule

// SiliconBlue PLL Cells

(* blackbox *)
module SB_PLL40_CORE (
	input   REFERENCECLK,
	output  PLLOUTCORE,
	output  PLLOUTGLOBAL,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 1'b0;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

(* blackbox *)
module SB_PLL40_PAD (
	input   PACKAGEPIN,
	output  PLLOUTCORE,
	output  PLLOUTGLOBAL,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 1'b0;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

(* blackbox *)
module SB_PLL40_2_PAD (
	input   PACKAGEPIN,
	output  PLLOUTCOREA,
	output  PLLOUTGLOBALA,
	output  PLLOUTCOREB,
	output  PLLOUTGLOBALB,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 1'b0;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT_PORTB = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE_PORTA = 1'b0;
	parameter ENABLE_ICEGATE_PORTB = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

(* blackbox *)
module SB_PLL40_2F_CORE (
	input   REFERENCECLK,
	output  PLLOUTCOREA,
	output  PLLOUTGLOBALA,
	output  PLLOUTCOREB,
	output  PLLOUTGLOBALB,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 1'b0;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT_PORTA = "GENCLK";
	parameter PLLOUT_SELECT_PORTB = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE_PORTA = 1'b0;
	parameter ENABLE_ICEGATE_PORTB = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

(* blackbox *)
module SB_PLL40_2F_PAD (
	input   PACKAGEPIN,
	output  PLLOUTCOREA,
	output  PLLOUTGLOBALA,
	output  PLLOUTCOREB,
	output  PLLOUTGLOBALB,
	input   EXTFEEDBACK,
	input   [7:0] DYNAMICDELAY,
	output  LOCK,
	input   BYPASS,
	input   RESETB,
	input   LATCHINPUTVALUE,
	output  SDO,
	input   SDI,
	input   SCLK
);
	parameter FEEDBACK_PATH = "SIMPLE";
	parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = "FIXED";
	parameter DELAY_ADJUSTMENT_MODE_RELATIVE = "FIXED";
	parameter SHIFTREG_DIV_MODE = 2'b00;
	parameter FDA_FEEDBACK = 4'b0000;
	parameter FDA_RELATIVE = 4'b0000;
	parameter PLLOUT_SELECT_PORTA = "GENCLK";
	parameter PLLOUT_SELECT_PORTB = "GENCLK";
	parameter DIVR = 4'b0000;
	parameter DIVF = 7'b0000000;
	parameter DIVQ = 3'b000;
	parameter FILTER_RANGE = 3'b000;
	parameter ENABLE_ICEGATE_PORTA = 1'b0;
	parameter ENABLE_ICEGATE_PORTB = 1'b0;
	parameter TEST_MODE = 1'b0;
	parameter EXTERNAL_DIVIDE_FACTOR = 1;
endmodule

// SiliconBlue Device Configuration Cells

(* blackbox, keep *)
module SB_WARMBOOT (
	input BOOT,
	input S1,
	input S0
);
endmodule

module SB_SPRAM256KA (
	input [13:0] ADDRESS,
	input [15:0] DATAIN,
	input [3:0] MASKWREN,
	input WREN, CHIPSELECT, CLOCK, STANDBY, SLEEP, POWEROFF,
	output reg [15:0] DATAOUT
);
`ifndef BLACKBOX
`ifndef EQUIV
	reg [15:0] mem [0:16383];
	wire off = SLEEP || !POWEROFF;
	integer i;

	always @(negedge POWEROFF) begin
		for (i = 0; i <= 16383; i = i+1)
			mem[i] = 16'bx;
	end

	always @(posedge CLOCK, posedge off) begin
		if (off) begin
			DATAOUT <= 0;
		end else
		if (STANDBY) begin
			DATAOUT <= 16'bx;
		end else
		if (CHIPSELECT) begin
			if (!WREN) begin
				DATAOUT <= mem[ADDRESS];
			end else begin
				if (MASKWREN[0]) mem[ADDRESS][ 3: 0] <= DATAIN[ 3: 0];
				if (MASKWREN[1]) mem[ADDRESS][ 7: 4] <= DATAIN[ 7: 4];
				if (MASKWREN[2]) mem[ADDRESS][11: 8] <= DATAIN[11: 8];
				if (MASKWREN[3]) mem[ADDRESS][15:12] <= DATAIN[15:12];
				DATAOUT <= 16'bx;
			end
		end
	end
`endif
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13169-L13182
		$setup(posedge ADDRESS, posedge CLOCK, 268);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13183
		$setup(CHIPSELECT, posedge CLOCK, 404);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13184-L13199
		$setup(DATAIN, posedge CLOCK, 143);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13200-L13203
		$setup(MASKWREN, posedge CLOCK, 143);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13167
		//$setup(negedge SLEEP, posedge CLOCK, 41505);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13167
		//$setup(negedge STANDBY, posedge CLOCK, 1715);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13206
		$setup(WREN, posedge CLOCK, 289);
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13207-L13222
		(posedge CLOCK => (DATAOUT : 16'bx)) = 1821;
		// https://github.com/YosysHQ/icestorm/blob/95949315364f8d9b0c693386aefadf44b28e2cf6/icefuzz/timings_up5k.txt#L13223-L13238
		(posedge SLEEP => (DATAOUT : 16'b0)) = 1099;
	endspecify
`endif
endmodule

(* blackbox *)
module SB_HFOSC(
	input TRIM0,
	input TRIM1,
	input TRIM2,
	input TRIM3,
	input TRIM4,
	input TRIM5,
	input TRIM6,
	input TRIM7,
	input TRIM8,
	input TRIM9,
	input CLKHFPU,
	input CLKHFEN,
	output CLKHF
);
parameter TRIM_EN = "0b0";
parameter CLKHF_DIV = "0b00";
endmodule

(* blackbox *)
module SB_LFOSC(
	input CLKLFPU,
	input CLKLFEN,
	output CLKLF
);
endmodule

(* blackbox *)
module SB_RGBA_DRV(
	input CURREN,
	input RGBLEDEN,
	input RGB0PWM,
	input RGB1PWM,
	input RGB2PWM,
	output RGB0,
	output RGB1,
	output RGB2
);
parameter CURRENT_MODE = "0b0";
parameter RGB0_CURRENT = "0b000000";
parameter RGB1_CURRENT = "0b000000";
parameter RGB2_CURRENT = "0b000000";
endmodule

(* blackbox *)
module SB_LED_DRV_CUR(
	input EN,
	output LEDPU
);
endmodule

(* blackbox *)
module SB_RGB_DRV(
	input RGBLEDEN,
	input RGB0PWM,
	input RGB1PWM,
	input RGB2PWM,
	input RGBPU,
	output RGB0,
	output RGB1,
	output RGB2
);
parameter CURRENT_MODE = "0b0";
parameter RGB0_CURRENT = "0b000000";
parameter RGB1_CURRENT = "0b000000";
parameter RGB2_CURRENT = "0b000000";
endmodule

(* blackbox *)
module SB_I2C(
	input  SBCLKI,
	input  SBRWI,
	input  SBSTBI,
	input  SBADRI7,
	input  SBADRI6,
	input  SBADRI5,
	input  SBADRI4,
	input  SBADRI3,
	input  SBADRI2,
	input  SBADRI1,
	input  SBADRI0,
	input  SBDATI7,
	input  SBDATI6,
	input  SBDATI5,
	input  SBDATI4,
	input  SBDATI3,
	input  SBDATI2,
	input  SBDATI1,
	input  SBDATI0,
	input  SCLI,
	input  SDAI,
	output SBDATO7,
	output SBDATO6,
	output SBDATO5,
	output SBDATO4,
	output SBDATO3,
	output SBDATO2,
	output SBDATO1,
	output SBDATO0,
	output SBACKO,
	output I2CIRQ,
	output I2CWKUP,
	output SCLO, //inout in the SB verilog library, but output in the VHDL and PDF libs and seemingly in the HW itself
	output SCLOE,
	output SDAO,
	output SDAOE
);
parameter I2C_SLAVE_INIT_ADDR = "0b1111100001";
parameter BUS_ADDR74 = "0b0001";
endmodule

(* blackbox *)
module SB_SPI (
	input  SBCLKI,
	input  SBRWI,
	input  SBSTBI,
	input  SBADRI7,
	input  SBADRI6,
	input  SBADRI5,
	input  SBADRI4,
	input  SBADRI3,
	input  SBADRI2,
	input  SBADRI1,
	input  SBADRI0,
	input  SBDATI7,
	input  SBDATI6,
	input  SBDATI5,
	input  SBDATI4,
	input  SBDATI3,
	input  SBDATI2,
	input  SBDATI1,
	input  SBDATI0,
	input  MI,
	input  SI,
	input  SCKI,
	input  SCSNI,
	output SBDATO7,
	output SBDATO6,
	output SBDATO5,
	output SBDATO4,
	output SBDATO3,
	output SBDATO2,
	output SBDATO1,
	output SBDATO0,
	output SBACKO,
	output SPIIRQ,
	output SPIWKUP,
	output SO,
	output SOE,
	output MO,
	output MOE,
	output SCKO, //inout in the SB verilog library, but output in the VHDL and PDF libs and seemingly in the HW itself
	output SCKOE,
	output MCSNO3,
	output MCSNO2,
	output MCSNO1,
	output MCSNO0,
	output MCSNOE3,
	output MCSNOE2,
	output MCSNOE1,
	output MCSNOE0
);
parameter BUS_ADDR74 = "0b0000";
endmodule

(* blackbox *)
module SB_LEDDA_IP(
	input LEDDCS,
	input LEDDCLK,
	input LEDDDAT7,
	input LEDDDAT6,
	input LEDDDAT5,
	input LEDDDAT4,
	input LEDDDAT3,
	input LEDDDAT2,
	input LEDDDAT1,
	input LEDDDAT0,
	input LEDDADDR3,
	input LEDDADDR2,
	input LEDDADDR1,
	input LEDDADDR0,
	input LEDDDEN,
	input LEDDEXE,
	input LEDDRST,
	output PWMOUT0,
	output PWMOUT1,
	output PWMOUT2,
	output LEDDON
);
endmodule

(* blackbox *)
module SB_FILTER_50NS(
	input FILTERIN,
	output FILTEROUT
);
endmodule

module SB_IO_I3C (
	inout  PACKAGE_PIN,
	input  LATCH_INPUT_VALUE,
	input  CLOCK_ENABLE,
	input  INPUT_CLK,
	input  OUTPUT_CLK,
	input  OUTPUT_ENABLE,
	input  D_OUT_0,
	input  D_OUT_1,
	output D_IN_0,
	output D_IN_1,
	input  PU_ENB,
	input  WEAK_PU_ENB
);
	parameter [5:0] PIN_TYPE = 6'b000000;
	parameter [0:0] PULLUP = 1'b0;
	parameter [0:0] WEAK_PULLUP = 1'b0;
	parameter [0:0] NEG_TRIGGER = 1'b0;
	parameter IO_STANDARD = "SB_LVCMOS";

`ifndef BLACKBOX
	reg dout, din_0, din_1;
	reg din_q_0, din_q_1;
	reg dout_q_0, dout_q_1;
	reg outena_q;

	generate if (!NEG_TRIGGER) begin
		always @(posedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_0  <= PACKAGE_PIN;
		always @(negedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_1  <= PACKAGE_PIN;
		always @(posedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_0 <= D_OUT_0;
		always @(negedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_1 <= D_OUT_1;
		always @(posedge OUTPUT_CLK) if (CLOCK_ENABLE) outena_q <= OUTPUT_ENABLE;
	end else begin
		always @(negedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_0  <= PACKAGE_PIN;
		always @(posedge INPUT_CLK)  if (CLOCK_ENABLE) din_q_1  <= PACKAGE_PIN;
		always @(negedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_0 <= D_OUT_0;
		always @(posedge OUTPUT_CLK) if (CLOCK_ENABLE) dout_q_1 <= D_OUT_1;
		always @(negedge OUTPUT_CLK) if (CLOCK_ENABLE) outena_q <= OUTPUT_ENABLE;
	end endgenerate

	always @* begin
		if (!PIN_TYPE[1] || !LATCH_INPUT_VALUE)
			din_0 = PIN_TYPE[0] ? PACKAGE_PIN : din_q_0;
		din_1 = din_q_1;
	end

	// work around simulation glitches on dout in DDR mode
	reg outclk_delayed_1;
	reg outclk_delayed_2;
	always @* outclk_delayed_1 <= OUTPUT_CLK;
	always @* outclk_delayed_2 <= outclk_delayed_1;

	always @* begin
		if (PIN_TYPE[3])
			dout = PIN_TYPE[2] ? !dout_q_0 : D_OUT_0;
		else
			dout = (outclk_delayed_2 ^ NEG_TRIGGER) || PIN_TYPE[2] ? dout_q_0 : dout_q_1;
	end

	assign D_IN_0 = din_0, D_IN_1 = din_1;

	generate
		if (PIN_TYPE[5:4] == 2'b01) assign PACKAGE_PIN = dout;
		if (PIN_TYPE[5:4] == 2'b10) assign PACKAGE_PIN = OUTPUT_ENABLE ? dout : 1'bz;
		if (PIN_TYPE[5:4] == 2'b11) assign PACKAGE_PIN = outena_q ? dout : 1'bz;
	endgenerate
`endif
endmodule

module SB_IO_OD (
	inout  PACKAGEPIN,
	input  LATCHINPUTVALUE,
	input  CLOCKENABLE,
	input  INPUTCLK,
	input  OUTPUTCLK,
	input  OUTPUTENABLE,
	input  DOUT1,
	input  DOUT0,
	output DIN1,
	output DIN0
);
	parameter [5:0] PIN_TYPE = 6'b000000;
	parameter [0:0] NEG_TRIGGER = 1'b0;

`ifndef BLACKBOX
	reg dout, din_0, din_1;
	reg din_q_0, din_q_1;
	reg dout_q_0, dout_q_1;
	reg outena_q;

	generate if (!NEG_TRIGGER) begin
		always @(posedge INPUTCLK)  if (CLOCKENABLE) din_q_0  <= PACKAGEPIN;
		always @(negedge INPUTCLK)  if (CLOCKENABLE) din_q_1  <= PACKAGEPIN;
		always @(posedge OUTPUTCLK) if (CLOCKENABLE) dout_q_0 <= DOUT0;
		always @(negedge OUTPUTCLK) if (CLOCKENABLE) dout_q_1 <= DOUT1;
		always @(posedge OUTPUTCLK) if (CLOCKENABLE) outena_q <= OUTPUTENABLE;
	end else begin
		always @(negedge INPUTCLK)  if (CLOCKENABLE) din_q_0  <= PACKAGEPIN;
		always @(posedge INPUTCLK)  if (CLOCKENABLE) din_q_1  <= PACKAGEPIN;
		always @(negedge OUTPUTCLK) if (CLOCKENABLE) dout_q_0 <= DOUT0;
		always @(posedge OUTPUTCLK) if (CLOCKENABLE) dout_q_1 <= DOUT1;
		always @(negedge OUTPUTCLK) if (CLOCKENABLE) outena_q <= OUTPUTENABLE;
	end endgenerate

	always @* begin
		if (!PIN_TYPE[1] || !LATCHINPUTVALUE)
			din_0 = PIN_TYPE[0] ? PACKAGEPIN : din_q_0;
		din_1 = din_q_1;
	end

	// work around simulation glitches on dout in DDR mode
	reg outclk_delayed_1;
	reg outclk_delayed_2;
	always @* outclk_delayed_1 <= OUTPUTCLK;
	always @* outclk_delayed_2 <= outclk_delayed_1;

	always @* begin
		if (PIN_TYPE[3])
			dout = PIN_TYPE[2] ? !dout_q_0 : DOUT0;
		else
			dout = (outclk_delayed_2 ^ NEG_TRIGGER) || PIN_TYPE[2] ? dout_q_0 : dout_q_1;
	end

	assign DIN0 = din_0, DIN1 = din_1;

	generate
		if (PIN_TYPE[5:4] == 2'b01) assign PACKAGEPIN = dout ? 1'bz : 1'b0;
		if (PIN_TYPE[5:4] == 2'b10) assign PACKAGEPIN = OUTPUTENABLE ? (dout ? 1'bz : 1'b0) : 1'bz;
		if (PIN_TYPE[5:4] == 2'b11) assign PACKAGEPIN = outena_q ? (dout ? 1'bz : 1'b0) : 1'bz;
	endgenerate
`endif
endmodule

//(* abc9_box, lib_whitebox *) // TODO
module SB_MAC16 (
	input CLK, CE,
	input [15:0] C, A, B, D,
	input AHOLD, BHOLD, CHOLD, DHOLD,
	input IRSTTOP, IRSTBOT,
	input ORSTTOP, ORSTBOT,
	input OLOADTOP, OLOADBOT,
	input ADDSUBTOP, ADDSUBBOT,
	input OHOLDTOP, OHOLDBOT,
	input CI, ACCUMCI, SIGNEXTIN,
	output [31:0] O,
	output CO, ACCUMCO, SIGNEXTOUT
);
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
	parameter [0:0] TOPADDSUB_UPPERINPUT = 0;
	parameter [1:0] TOPADDSUB_CARRYSELECT = 0;
	parameter [1:0] BOTOUTPUT_SELECT = 0;
	parameter [1:0] BOTADDSUB_LOWERINPUT = 0;
	parameter [0:0] BOTADDSUB_UPPERINPUT = 0;
	parameter [1:0] BOTADDSUB_CARRYSELECT = 0;
	parameter [0:0] MODE_8x8 = 0;
	parameter [0:0] A_SIGNED = 0;
	parameter [0:0] B_SIGNED = 0;

	wire clock = CLK ^ NEG_TRIGGER;

	// internal wires, compare Figure on page 133 of ICE Technology Library 3.0 and Fig 2 on page 2 of Lattice TN1295-DSP
	// http://www.latticesemi.com/~/media/LatticeSemi/Documents/TechnicalBriefs/SBTICETechnologyLibrary201608.pdf
	// https://www.latticesemi.com/-/media/LatticeSemi/Documents/ApplicationNotes/AD/DSPFunctionUsageGuideforICE40Devices.ashx
	wire [15:0] iA, iB, iC, iD;
	wire [15:0] iF, iJ, iK, iG;
	wire [31:0] iL, iH;
	wire [15:0] iW, iX, iP, iQ;
	wire [15:0] iY, iZ, iR, iS;
	wire HCI, LCI, LCO;

	// Regs C and A
	reg [15:0] rC, rA;
	always @(posedge clock, posedge IRSTTOP) begin
		if (IRSTTOP) begin
			rC <= 0;
			rA <= 0;
		end else if (CE) begin
			if (!CHOLD) rC <= C;
			if (!AHOLD) rA <= A;
		end
	end
	assign iC = C_REG ? rC : C;
	assign iA = A_REG ? rA : A;

	// Regs B and D
	reg [15:0] rB, rD;
	always @(posedge clock, posedge IRSTBOT) begin
		if (IRSTBOT) begin
			rB <= 0;
			rD <= 0;
		end else if (CE) begin
			if (!BHOLD) rB <= B;
			if (!DHOLD) rD <= D;
		end
	end
	assign iB = B_REG ? rB : B;
	assign iD = D_REG ? rD : D;

	// Multiplier Stage
	wire [15:0] p_Ah_Bh, p_Al_Bh, p_Ah_Bl, p_Al_Bl;
	wire [15:0] Ah, Al, Bh, Bl;
	assign Ah = {A_SIGNED ? {8{iA[15]}} : 8'b0, iA[15: 8]};
	assign Al = {A_SIGNED && MODE_8x8 ? {8{iA[ 7]}} : 8'b0, iA[ 7: 0]};
	assign Bh = {B_SIGNED ? {8{iB[15]}} : 8'b0, iB[15: 8]};
	assign Bl = {B_SIGNED && MODE_8x8 ? {8{iB[ 7]}} : 8'b0, iB[ 7: 0]};
	assign p_Ah_Bh = Ah * Bh; // F
	assign p_Al_Bh = {8'b0, Al[7:0]} * Bh; // J
	assign p_Ah_Bl = Ah * {8'b0, Bl[7:0]}; // K
	assign p_Al_Bl = Al * Bl; // G

	// Regs F and J
	reg [15:0] rF, rJ;
	always @(posedge clock, posedge IRSTTOP) begin
		if (IRSTTOP) begin
			rF <= 0;
			rJ <= 0;
		end else if (CE) begin
			rF <= p_Ah_Bh;
			if (!MODE_8x8) rJ <= p_Al_Bh;
		end
	end
	assign iF = TOP_8x8_MULT_REG ? rF : p_Ah_Bh;
	assign iJ = PIPELINE_16x16_MULT_REG1 ? rJ : p_Al_Bh;

	// Regs K and G
	reg [15:0] rK, rG;
	always @(posedge clock, posedge IRSTBOT) begin
		if (IRSTBOT) begin
			rK <= 0;
			rG <= 0;
		end else if (CE) begin
			if (!MODE_8x8) rK <= p_Ah_Bl;
			rG <= p_Al_Bl;
		end
	end
	assign iK = PIPELINE_16x16_MULT_REG1 ? rK : p_Ah_Bl;
	assign iG = BOT_8x8_MULT_REG ? rG : p_Al_Bl;

	// Adder Stage
	wire [23:0] iK_e = {A_SIGNED ? {8{iK[15]}} : 8'b0, iK};
	wire [23:0] iJ_e = {B_SIGNED ? {8{iJ[15]}} : 8'b0, iJ};
	assign iL = iG + (iK_e << 8) + (iJ_e << 8) + (iF << 16);

	// Reg H
	reg [31:0] rH;
	always @(posedge clock, posedge IRSTBOT) begin
		if (IRSTBOT) begin
			rH <= 0;
		end else if (CE) begin
			if (!MODE_8x8) rH <= iL;
		end
	end
	assign iH = PIPELINE_16x16_MULT_REG2 ? rH : iL;

	// Hi Output Stage
	wire [15:0] XW, Oh;
	reg [15:0] rQ;
	assign iW = TOPADDSUB_UPPERINPUT ? iC : iQ;
	assign iX = (TOPADDSUB_LOWERINPUT == 0) ? iA : (TOPADDSUB_LOWERINPUT == 1) ? iF : (TOPADDSUB_LOWERINPUT == 2) ? iH[31:16] : {16{iZ[15]}};
	assign {ACCUMCO, XW} = iX + (iW ^ {16{ADDSUBTOP}}) + HCI;
	assign CO = ACCUMCO ^ ADDSUBTOP;
	assign iP = OLOADTOP ? iC : XW ^ {16{ADDSUBTOP}};
	always @(posedge clock, posedge ORSTTOP) begin
		if (ORSTTOP) begin
			rQ <= 0;
		end else if (CE) begin
			if (!OHOLDTOP) rQ <= iP;
		end
	end
	assign iQ = rQ;
	assign Oh = (TOPOUTPUT_SELECT == 0) ? iP : (TOPOUTPUT_SELECT == 1) ? iQ : (TOPOUTPUT_SELECT == 2) ? iF : iH[31:16];
	assign HCI = (TOPADDSUB_CARRYSELECT == 0) ? 1'b0 : (TOPADDSUB_CARRYSELECT == 1) ? 1'b1 : (TOPADDSUB_CARRYSELECT == 2) ? LCO : LCO ^ ADDSUBBOT;
	assign SIGNEXTOUT = iX[15];

	// Lo Output Stage
	wire [15:0] YZ, Ol;
	reg [15:0] rS;
	assign iY = BOTADDSUB_UPPERINPUT ? iD : iS;
	assign iZ = (BOTADDSUB_LOWERINPUT == 0) ? iB : (BOTADDSUB_LOWERINPUT == 1) ? iG : (BOTADDSUB_LOWERINPUT == 2) ? iH[15:0] : {16{SIGNEXTIN}};
	assign {LCO, YZ} = iZ + (iY ^ {16{ADDSUBBOT}}) + LCI;
	assign iR = OLOADBOT ? iD : YZ ^ {16{ADDSUBBOT}};
	always @(posedge clock, posedge ORSTBOT) begin
		if (ORSTBOT) begin
			rS <= 0;
		end else if (CE) begin
			if (!OHOLDBOT) rS <= iR;
		end
	end
	assign iS = rS;
	assign Ol = (BOTOUTPUT_SELECT == 0) ? iR : (BOTOUTPUT_SELECT == 1) ? iS : (BOTOUTPUT_SELECT == 2) ? iG : iH[15:0];
	assign LCI = (BOTADDSUB_CARRYSELECT == 0) ? 1'b0 : (BOTADDSUB_CARRYSELECT == 1) ? 1'b1 : (BOTADDSUB_CARRYSELECT == 2) ? ACCUMCI : CI;
	assign O = {Oh, Ol};
endmodule

// Post-place-and-route RAM model
module ICESTORM_RAM(
	output RDATA_15, RDATA_14, RDATA_13, RDATA_12, RDATA_11, RDATA_10, RDATA_9, RDATA_8, RDATA_7, RDATA_6, RDATA_5, RDATA_4, RDATA_3, RDATA_2, RDATA_1, RDATA_0,
	input  RCLK, RCLKE, RE,
	input  RADDR_10, RADDR_9, RADDR_8, RADDR_7, RADDR_6, RADDR_5, RADDR_4, RADDR_3, RADDR_2, RADDR_1, RADDR_0,
	input  WCLK, WCLKE, WE,
	input  WADDR_10, WADDR_9, WADDR_8, WADDR_7, WADDR_6, WADDR_5, WADDR_4, WADDR_3, WADDR_2, WADDR_1, WADDR_0,
	input  MASK_15, MASK_14, MASK_13, MASK_12, MASK_11, MASK_10, MASK_9, MASK_8, MASK_7, MASK_6, MASK_5, MASK_4, MASK_3, MASK_2, MASK_1, MASK_0,
	input  WDATA_15, WDATA_14, WDATA_13, WDATA_12, WDATA_11, WDATA_10, WDATA_9, WDATA_8, WDATA_7, WDATA_6, WDATA_5, WDATA_4, WDATA_3, WDATA_2, WDATA_1, WDATA_0
);
	parameter WRITE_MODE = 0;
	parameter READ_MODE = 0;

	parameter NEG_CLK_R = 1'b0;
	parameter NEG_CLK_W = 1'b0;

	parameter INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

	// Pull-down and pull-up functions
	function pd;
		input x;
		begin
			pd = (x === 1'bz) ? 1'b0 : x;
		end
	endfunction

	function pu;
		input x;
		begin
			pu = (x === 1'bz) ? 1'b1 : x;
		end
	endfunction

	SB_RAM40_4K #(
		.WRITE_MODE(WRITE_MODE),
		.READ_MODE (READ_MODE ),
		.INIT_0    (INIT_0    ),
		.INIT_1    (INIT_1    ),
		.INIT_2    (INIT_2    ),
		.INIT_3    (INIT_3    ),
		.INIT_4    (INIT_4    ),
		.INIT_5    (INIT_5    ),
		.INIT_6    (INIT_6    ),
		.INIT_7    (INIT_7    ),
		.INIT_8    (INIT_8    ),
		.INIT_9    (INIT_9    ),
		.INIT_A    (INIT_A    ),
		.INIT_B    (INIT_B    ),
		.INIT_C    (INIT_C    ),
		.INIT_D    (INIT_D    ),
		.INIT_E    (INIT_E    ),
		.INIT_F    (INIT_F    )
	) RAM (
		.RDATA({RDATA_15, RDATA_14, RDATA_13, RDATA_12, RDATA_11, RDATA_10, RDATA_9, RDATA_8, RDATA_7, RDATA_6, RDATA_5, RDATA_4, RDATA_3, RDATA_2, RDATA_1, RDATA_0}),
		.RCLK (pd(RCLK) ^ NEG_CLK_R),
		.RCLKE(pu(RCLKE)),
		.RE   (pd(RE)),
		.RADDR({pd(RADDR_10), pd(RADDR_9), pd(RADDR_8), pd(RADDR_7), pd(RADDR_6), pd(RADDR_5), pd(RADDR_4), pd(RADDR_3), pd(RADDR_2), pd(RADDR_1), pd(RADDR_0)}),
		.WCLK (pd(WCLK) ^ NEG_CLK_W),
		.WCLKE(pu(WCLKE)),
		.WE   (pd(WE)),
		.WADDR({pd(WADDR_10), pd(WADDR_9), pd(WADDR_8), pd(WADDR_7), pd(WADDR_6), pd(WADDR_5), pd(WADDR_4), pd(WADDR_3), pd(WADDR_2), pd(WADDR_1), pd(WADDR_0)}),
		.MASK ({pd(MASK_15), pd(MASK_14), pd(MASK_13), pd(MASK_12), pd(MASK_11), pd(MASK_10), pd(MASK_9), pd(MASK_8),
			pd(MASK_7), pd(MASK_6), pd(MASK_5), pd(MASK_4), pd(MASK_3), pd(MASK_2), pd(MASK_1), pd(MASK_0)}),
		.WDATA({pd(WDATA_15), pd(WDATA_14), pd(WDATA_13), pd(WDATA_12), pd(WDATA_11), pd(WDATA_10), pd(WDATA_9), pd(WDATA_8),
			pd(WDATA_7), pd(WDATA_6), pd(WDATA_5), pd(WDATA_4), pd(WDATA_3), pd(WDATA_2), pd(WDATA_1), pd(WDATA_0)})
	);

`ifdef TIMING
specify
	(RCLK => RDATA_15) = (0:0:0, 0:0:0);
	(RCLK => RDATA_14) = (0:0:0, 0:0:0);
	(RCLK => RDATA_13) = (0:0:0, 0:0:0);
	(RCLK => RDATA_12) = (0:0:0, 0:0:0);
	(RCLK => RDATA_11) = (0:0:0, 0:0:0);
	(RCLK => RDATA_10) = (0:0:0, 0:0:0);
	(RCLK => RDATA_9) = (0:0:0, 0:0:0);
	(RCLK => RDATA_8) = (0:0:0, 0:0:0);
	(RCLK => RDATA_7) = (0:0:0, 0:0:0);
	(RCLK => RDATA_6) = (0:0:0, 0:0:0);
	(RCLK => RDATA_5) = (0:0:0, 0:0:0);
	(RCLK => RDATA_4) = (0:0:0, 0:0:0);
	(RCLK => RDATA_3) = (0:0:0, 0:0:0);
	(RCLK => RDATA_2) = (0:0:0, 0:0:0);
	(RCLK => RDATA_1) = (0:0:0, 0:0:0);
	(RCLK => RDATA_0) = (0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RCLKE, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RCLKE, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RCLKE, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RCLKE, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RE, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RE, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RE, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RE, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_10, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_10, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_10, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_10, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_9, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_9, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_9, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_9, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_8, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_8, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_8, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_8, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_7, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_7, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_7, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_7, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_6, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_6, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_6, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_6, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_5, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_5, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_5, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_5, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_4, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_4, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_4, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_4, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_3, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_3, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_3, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_3, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_2, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_2, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_2, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_2, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_1, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_1, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_1, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_1, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, posedge RADDR_0, 0:0:0, 0:0:0);
	$setuphold(posedge RCLK, negedge RADDR_0, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, posedge RADDR_0, 0:0:0, 0:0:0);
	$setuphold(negedge RCLK, negedge RADDR_0, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WCLKE, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WCLKE, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WCLKE, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WCLKE, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WE, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WE, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WE, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WE, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_10, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_10, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_10, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_10, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_9, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_9, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_9, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_9, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_8, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_8, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_8, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_8, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_7, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_7, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_7, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_7, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_6, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_6, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_6, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_6, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_5, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_5, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_5, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_5, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_4, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_4, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_4, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_4, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_3, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_3, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_3, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_3, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_2, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_2, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_2, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_2, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_1, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_1, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_1, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_1, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WADDR_0, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WADDR_0, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WADDR_0, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WADDR_0, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_15, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_15, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_15, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_15, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_14, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_14, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_14, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_14, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_13, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_13, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_13, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_13, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_12, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_12, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_12, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_12, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_11, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_11, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_11, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_11, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_10, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_10, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_10, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_10, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_9, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_9, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_9, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_9, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_8, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_8, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_8, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_8, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_7, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_7, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_7, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_7, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_6, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_6, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_6, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_6, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_5, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_5, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_5, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_5, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_4, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_4, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_4, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_4, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_3, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_3, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_3, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_3, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_2, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_2, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_2, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_2, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_1, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_1, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_1, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_1, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge MASK_0, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge MASK_0, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge MASK_0, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge MASK_0, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_15, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_15, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_15, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_15, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_14, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_14, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_14, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_14, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_13, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_13, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_13, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_13, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_12, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_12, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_12, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_12, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_11, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_11, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_11, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_11, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_10, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_10, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_10, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_10, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_9, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_9, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_9, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_9, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_8, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_8, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_8, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_8, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_7, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_7, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_7, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_7, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_6, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_6, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_6, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_6, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_5, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_5, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_5, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_5, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_4, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_4, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_4, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_4, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_3, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_3, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_3, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_3, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_2, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_2, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_2, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_2, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_1, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_1, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_1, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_1, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, posedge WDATA_0, 0:0:0, 0:0:0);
	$setuphold(posedge WCLK, negedge WDATA_0, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, posedge WDATA_0, 0:0:0, 0:0:0);
	$setuphold(negedge WCLK, negedge WDATA_0, 0:0:0, 0:0:0);

endspecify
`endif
endmodule
