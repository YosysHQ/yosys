// The core logic primitive of the Cyclone V/10GX is the Adaptive Logic Module
// (ALM). Each ALM is made up of an 8-input, 2-output look-up table, covered 
// in this file, connected to combinational outputs, a carry chain, and four
// D flip-flops (which are covered as MISTRAL_FF in dff_sim.v).
//
// The ALM is vertically symmetric, so I find it helps to think in terms of
// half-ALMs, as that's predominantly the unit that synth_intel_alm uses.
//
// ALMs are quite flexible, having multiple modes.
//
// Normal (combinational) mode
// ---------------------------
// The ALM can implement:
// - a single 6-input function (with the other inputs usable for flip-flop access)
// - two 5-input functions that share two inputs
// - a 5-input and a 4-input function that share one input
// - a 5-input and a 3-or-less-input function that share no inputs
// - two 4-or-less-input functions that share no inputs
//
// Normal-mode functions are represented as MISTRAL_ALUTN cells with N inputs.
// It would be possible to represent a normal mode function as a single cell -
// the vendor cyclone{v,10gx}_lcell_comb cell does exactly that - but I felt
// it was more user-friendly to print out the specific function sizes
// separately.
//
// With the exception of MISTRAL_ALUT6, you can think of two normal-mode cells
// fitting inside a single ALM.
//
// Extended (7-input) mode
// -----------------------
// The ALM can also fit a 7-input function made of two 5-input functions that
// share four inputs, multiplexed by another input.
//
// Because this can't accept arbitrary 7-input functions, Yosys can't handle
// it, so it doesn't have a cell, but I would likely call it MISTRAL_ALUT7(E?)
// if it did, and it would take up a full ALM.
//
// It might be possible to add an extraction pass to examine all ALUT5 cells
// that feed into ALUT3 cells to see if they can be combined into an extended
// ALM, but I don't think it will be worth it.
//
// Arithmetic mode
// ---------------
// In arithmetic mode, each half-ALM uses its carry chain to perform fast addition
// of two four-input functions that share three inputs. Oddly, the result of
// one of the functions is inverted before being added (you can see this as
// the dot on a full-adder input of Figure 1-8 in the Handbook).
//
// The cell for an arithmetic-mode half-ALM is MISTRAL_ALM_ARITH. One idea
// I've had (or rather was suggested by mwk) is that functions that feed into
// arithmetic-mode cells could be packed directly into the arithmetic-mode
// cell as a function, which reduces the number of ALMs needed.
//
// Shared arithmetic mode
// ----------------------
// Shared arithmetic mode looks a lot like arithmetic mode, but here the
// output of every other four-input function goes to the input of the adder
// the next bit along. What this means is that adding three bits together can
// be done in an ALM, because functions can be used to implement addition that
// then feeds into the carry chain. This means that three bits can be added per
// ALM, as opposed to two in the arithmetic mode.
//
// Shared arithmetic mode doesn't currently have a cell, but I intend to add
// it as MISTRAL_ALM_SHARED, and have it occupy a full ALM. Because it adds
// three bits per cell, it makes addition shorter and use less ALMs, but
// I don't know enough to tell whether it's more efficient to use shared
// arithmetic mode to shorten the carry chain, or plain arithmetic mode with
// the functions packed in.

`default_nettype none

// Cyclone V LUT output timings (picoseconds):
//
//          CARRY   A    B    C   D   E    F   G
//  COMBOUT    -  605  583  510 512   -   97 400 (LUT6)
//  COMBOUT    -  602  583  457 510 302   93 483 (LUT7)
//   SUMOUT  368 1342 1323  887 927   -  785   -
// CARRYOUT   71 1082 1062  866 813   - 1198   -

(* abc9_lut=2, lib_whitebox *)
module MISTRAL_ALUT6(input A, B, C, D, E, F, output Q);

parameter [63:0] LUT = 64'h0000_0000_0000_0000;

`ifdef cyclonev
specify
    (A => Q) = 605;
    (B => Q) = 583;
    (C => Q) = 510;
    (D => Q) = 512;
    (E => Q) = 400;
    (F => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 275;
    (B => Q) = 272;
    (C => Q) = 175;
    (D => Q) = 165;
    (E => Q) = 162;
    (F => Q) = 53;
endspecify
`endif

assign Q = LUT >> {F, E, D, C, B, A};

endmodule


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_ALUT5(input A, B, C, D, E, output Q);

parameter [31:0] LUT = 32'h0000_0000;

`ifdef cyclonev
specify
    (A => Q) = 583;
    (B => Q) = 510;
    (C => Q) = 512;
    (D => Q) = 400;
    (E => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 272;
    (B => Q) = 175;
    (C => Q) = 165;
    (D => Q) = 162;
    (E => Q) = 53;
endspecify
`endif

assign Q = LUT >> {E, D, C, B, A};

endmodule


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_ALUT4(input A, B, C, D, output Q);

parameter [15:0] LUT = 16'h0000;

`ifdef cyclonev
specify
    (A => Q) = 510;
    (B => Q) = 512;
    (C => Q) = 400;
    (D => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 175;
    (B => Q) = 165;
    (C => Q) = 162;
    (D => Q) = 53;
endspecify
`endif

assign Q = LUT >> {D, C, B, A};

endmodule


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_ALUT3(input A, B, C, output Q);

parameter [7:0] LUT = 8'h00;

`ifdef cyclonev
specify
    (A => Q) = 510;
    (B => Q) = 400;
    (C => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 165;
    (B => Q) = 162;
    (C => Q) = 53;
endspecify
`endif

assign Q = LUT >> {C, B, A};

endmodule


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_ALUT2(input A, B, output Q);

parameter [3:0] LUT = 4'h0;

`ifdef cyclonev
specify
    (A => Q) = 400;
    (B => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 162;
    (B => Q) = 53;
endspecify
`endif

assign Q = LUT >> {B, A};

endmodule


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_NOT(input A, output Q);

`ifdef cyclonev
specify
    (A => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 53;
endspecify
`endif

assign Q = ~A;

endmodule

// Despite the abc9_carry attributes, this doesn't seem to stop ABC9 adding illegal fanout to the carry chain that nextpnr cannot handle.
// So we treat it as a total blackbox from ABC9's perspective for now.
// (* abc9_box, lib_whitebox *)
module MISTRAL_ALUT_ARITH(input A, B, C, D0, D1, /* (* abc9_carry *) */ input CI, output SO, /* (* abc9_carry *) */ output CO);

parameter LUT0 = 16'h0000;
parameter LUT1 = 16'h0000;

`ifdef cyclonev
specify
    (A  => SO) = 1342;
    (B  => SO) = 1323;
    (C  => SO) = 927;
    (D0 => SO) = 887;
    (D1 => SO) = 785;
    (CI => SO) = 368;

    (A  => CO) = 1082;
    (B  => CO) = 1062;
    (C  => CO) = 813;
    (D0 => CO) = 866;
    (D1 => CO) = 1198;
    (CI => CO) = 36; // Divided by 2 to account for there being two ALUT_ARITHs in an ALM)
endspecify
`endif
`ifdef cyclone10gx
specify
    (A  => SO) = 644;
    (B  => SO) = 477;
    (C  => SO) = 416;
    (D0 => SO) = 380;
    (D1 => SO) = 431;
    (CI => SO) = 276;

    (A  => CO) = 525;
    (B  => CO) = 433;
    (C  => CO) = 712;
    (D0 => CO) = 653;
    (D1 => CO) = 593;
    (CI => CO) = 16;
endspecify
`endif

wire q0, q1;

assign q0 = LUT0 >> {D0, C, B, A};
assign q1 = LUT1 >> {D1, C, B, A};

assign {CO, SO} = q0 + !q1 + CI;

endmodule


/*
// A, B, C0, C1, E0, E1, F0, F1: data inputs
// CARRYIN: carry input
// SHAREIN: shared-arithmetic input
// CLK0, CLK1, CLK2: clock inputs
//
// COMB0, COMB1: combinational outputs
// FF0, FF1, FF2, FF3: DFF outputs
// SUM0, SUM1: adder outputs
// CARRYOUT: carry output
// SHAREOUT: shared-arithmetic output
module MISTRAL_ALM(
    input A, B, C0, C1, E0, E1, F0, F1, CARRYIN, SHAREIN, // LUT path
    input CLK0, CLK1, CLK2, AC0, AC1,                     // FF path
    output COMB0, COMB1, SUM0, SUM1, CARRYOUT, SHAREOUT,
    output FF0, FF1, FF2, FF3
);

parameter LUT0 = 16'b0000;
parameter LUT1 = 16'b0000;
parameter LUT2 = 16'b0000;
parameter LUT3 = 16'b0000;

parameter INIT0 = 1'b0;
parameter INIT1 = 1'b0;
parameter INIT2 = 1'b0;
parameter INIT3 = 1'b0;

parameter C0_MUX = "C0";
parameter C1_MUX = "C1";

parameter F0_MUX = "VCC";
parameter F1_MUX = "GND";

parameter FEEDBACK0 = "FF0";
parameter FEEDBACK1 = "FF2";

parameter ADD_MUX = "LUT";

parameter DFF01_DATA_MUX = "COMB";
parameter DFF23_DATA_MUX = "COMB";

parameter DFF0_CLK = "CLK0";
parameter DFF1_CLK = "CLK0";
parameter DFF2_CLK = "CLK0";
parameter DFF3_CLK = "CLK0";

parameter DFF0_AC  = "AC0";
parameter DFF1_AC  = "AC0";
parameter DFF2_AC  = "AC0";
parameter DFF3_AC  = "AC0";

// Feedback muxes from the flip-flop outputs.
wire ff_feedback_mux0, ff_feedback_mux1;

// C-input muxes which can be set to also use the F-input.
wire c0_input_mux, c1_input_mux;

// F-input muxes which can be set to a constant to allow LUT5 use.
wire f0_input_mux, f1_input_mux;

// Adder input muxes to select between shared-arithmetic mode and arithmetic mode.
wire add0_input_mux, add1_input_mux;

// Combinational-output muxes for LUT #1 and LUT #3
wire lut1_comb_mux, lut3_comb_mux;

// Sum-output muxes for LUT #1 and LUT #3
wire lut1_sum_mux, lut3_sum_mux;

// DFF data-input muxes
wire dff01_data_mux, dff23_data_mux;

// DFF clock selectors
wire dff0_clk, dff1_clk, dff2_clk, dff3_clk;

// DFF asynchronous-clear selectors
wire dff0_ac, dff1_ac, dff2_ac, dff3_ac;

// LUT, DFF and adder output wires for routing.
wire lut0_out, lut1a_out, lut1b_out, lut2_out, lut3a_out, lut3b_out;
wire dff0_out, dff1_out, dff2_out, dff3_out;
wire add0_sum, add1_sum, add0_carry, add1_carry;

generate
    if (FEEDBACK0 === "FF0")
        assign ff_feedback_mux0 = dff0_out;
    else if (FEEDBACK0 === "FF1")
        assign ff_feedback_mux0 = dff1_out;
    else
        $error("Invalid FEEDBACK0 setting!");

    if (FEEDBACK1 == "FF2")
        assign ff_feedback_mux1 = dff2_out;
    else if (FEEDBACK1 == "FF3")
        assign ff_feedback_mux1 = dff3_out;
    else
        $error("Invalid FEEDBACK1 setting!");

    if (C0_MUX === "C0")
        assign c0_input_mux = C0;
    else if (C0_MUX === "F1")
        assign c0_input_mux = F1;
    else if (C0_MUX === "FEEDBACK1")
        assign c0_input_mux = ff_feedback_mux1;
    else
        $error("Invalid C0_MUX setting!");

    if (C1_MUX === "C1")
        assign c1_input_mux = C1;
    else if (C1_MUX === "F0")
        assign c1_input_mux = F0;
    else if (C1_MUX === "FEEDBACK0")
        assign c1_input_mux = ff_feedback_mux0;
    else
        $error("Invalid C1_MUX setting!");

    // F0 == VCC is LUT5
    // F0 == F0 is LUT6
    // F0 == FEEDBACK is unknown
    if (F0_MUX === "VCC")
        assign f0_input_mux = 1'b1;
    else if (F0_MUX === "F0")
        assign f0_input_mux = F0;
    else if (F0_MUX === "FEEDBACK0")
        assign f0_input_mux = ff_feedback_mux0;
    else
        $error("Invalid F0_MUX setting!");

    // F1 == GND is LUT5
    // F1 == F1 is LUT6
    // F1 == FEEDBACK is unknown
    if (F1_MUX === "GND")
        assign f1_input_mux = 1'b0;
    else if (F1_MUX === "F1")
        assign f1_input_mux = F1;
    else if (F1_MUX === "FEEDBACK1")
        assign f1_input_mux = ff_feedback_mux1;
    else
        $error("Invalid F1_MUX setting!");

    if (ADD_MUX === "LUT") begin
        assign add0_input_mux = ~lut1_sum_mux;
        assign add1_input_mux = ~lut3_sum_mux;
    end else if (ADD_MUX === "SHARE") begin
        assign add0_input_mux = SHAREIN;
        assign add1_input_mux = lut1_comb_mux;
    end else
        $error("Invalid ADD_MUX setting!");

    if (DFF01_DATA_MUX === "COMB")
        assign dff01_data_mux = COMB0;
    else if (DFF01_DATA_MUX === "SUM")
        assign dff01_data_mux = SUM0;
    else
        $error("Invalid DFF01_DATA_MUX setting!");

    if (DFF23_DATA_MUX === "COMB")
        assign dff23_data_mux = COMB0;
    else if (DFF23_DATA_MUX === "SUM")
        assign dff23_data_mux = SUM0;
    else
        $error("Invalid DFF23_DATA_MUX setting!");

    if (DFF0_CLK === "CLK0")
        assign dff0_clk = CLK0;
    else if (DFF0_CLK === "CLK1")
        assign dff0_clk = CLK1;
    else if (DFF0_CLK === "CLK2")
        assign dff0_clk = CLK2;
    else
        $error("Invalid DFF0_CLK setting!");

    if (DFF1_CLK === "CLK0")
        assign dff1_clk = CLK0;
    else if (DFF1_CLK === "CLK1")
        assign dff1_clk = CLK1;
    else if (DFF1_CLK === "CLK2")
        assign dff1_clk = CLK2;
    else
        $error("Invalid DFF1_CLK setting!");

    if (DFF2_CLK === "CLK0")
        assign dff2_clk = CLK0;
    else if (DFF2_CLK === "CLK1")
        assign dff2_clk = CLK1;
    else if (DFF2_CLK === "CLK2")
        assign dff2_clk = CLK2;
    else
        $error("Invalid DFF2_CLK setting!");

    if (DFF3_CLK === "CLK0")
        assign dff3_clk = CLK0;
    else if (DFF3_CLK === "CLK1")
        assign dff3_clk = CLK1;
    else if (DFF3_CLK === "CLK2")
        assign dff3_clk = CLK2;
    else
        $error("Invalid DFF3_CLK setting!");

    if (DFF0_AC === "AC0")
        assign dff0_ac = AC0;
    else if (DFF0_AC === "AC1")
        assign dff0_ac = AC1;
    else
        $error("Invalid DFF0_AC setting!");

    if (DFF1_AC === "AC0")
        assign dff1_ac = AC0;
    else if (DFF1_AC === "AC1")
        assign dff1_ac = AC1;
    else
        $error("Invalid DFF1_AC setting!");

    if (DFF2_AC === "AC0")
        assign dff2_ac = AC0;
    else if (DFF2_AC === "AC1")
        assign dff2_ac = AC1;
    else
        $error("Invalid DFF2_AC setting!");

    if (DFF3_AC === "AC0")
        assign dff3_ac = AC0;
    else if (DFF3_AC === "AC1")
        assign dff3_ac = AC1;
    else
        $error("Invalid DFF3_AC setting!");

endgenerate

// F0 on the Quartus diagram
MISTRAL_ALUT4 #(.LUT(LUT0)) lut0 (.A(A), .B(B), .C(C0), .D(c1_input_mux), .Q(lut0_out));

// F2 on the Quartus diagram
MISTRAL_ALUT4 #(.LUT(LUT1)) lut1_comb (.A(A), .B(B), .C(C0), .D(c1_input_mux), .Q(lut1_comb_mux));
MISTRAL_ALUT4 #(.LUT(LUT1)) lut1_sum  (.A(A), .B(B), .C(C0), .D(E0), .Q(lut1_sum_mux));

// F1 on the Quartus diagram
MISTRAL_ALUT4 #(.LUT(LUT2)) lut2 (.A(A), .B(B), .C(C1), .D(c0_input_mux), .Q(lut2_out));

// F3 on the Quartus diagram
MISTRAL_ALUT4 #(.LUT(LUT3)) lut3_comb (.A(A), .B(B), .C(C1), .D(c0_input_mux), .Q(lut3_comb_mux));
MISTRAL_ALUT4 #(.LUT(LUT3)) lut3_sum  (.A(A), .B(B), .C(C1), .D(E1), .Q(lut3_sum_mux));

MISTRAL_FF #(.INIT(INIT0)) dff0 (.D(dff01_data_mux), .CLK(dff0_clk), .ACn(dff0_ac), .Q(dff0_out));
MISTRAL_FF #(.INIT(INIT1)) dff1 (.D(dff01_data_mux), .CLK(dff1_clk), .ACn(dff1_ac), .Q(dff1_out));
MISTRAL_FF #(.INIT(INIT2)) dff2 (.D(dff23_data_mux), .CLK(dff2_clk), .ACn(dff2_ac), .Q(dff2_out));
MISTRAL_FF #(.INIT(INIT3)) dff3 (.D(dff23_data_mux), .CLK(dff3_clk), .ACn(dff3_ac), .Q(dff3_out));

// Adders
assign {add0_carry, add0_sum} = CARRYIN + lut0_out + lut1_sum_mux;
assign {add1_carry, add1_sum} = add0_carry + lut2_out + lut3_sum_mux;

// COMBOUT outputs on the Quartus diagram
assign COMB0 = E0 ? (f0_input_mux ? lut3_comb_mux : lut1_comb_mux)
                    : (f0_input_mux ? lut2_out : lut0_out);

assign COMB1 = E1 ? (f1_input_mux ? lut3_comb_mux : lut1_comb_mux)
                    : (f1_input_mux ? lut2_out : lut0_out);

// SUMOUT output on the Quartus diagram
assign SUM0 = add0_sum;
assign SUM1 = add1_sum;

// COUT output on the Quartus diagram
assign CARRYOUT = add1_carry;

// SHAREOUT output on the Quartus diagram
assign SHAREOUT = lut3_comb_mux;

// REGOUT outputs on the Quartus diagram
assign FF0 = dff0_out;
assign FF1 = dff1_out;
assign FF2 = dff2_out;
assign FF3 = dff3_out;

endmodule
*/
