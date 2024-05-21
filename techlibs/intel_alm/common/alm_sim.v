// The core logic primitive of the Cyclone V is the Adaptive Logic Module
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

assign Q = LUT >> {B, A};

endmodule


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_NOT(input A, output Q);

`ifdef cyclonev
specify
    (A => Q) = 97;
endspecify
`endif

assign Q = ~A;

endmodule

(* abc9_box, lib_whitebox *)
module MISTRAL_ALUT_ARITH(input A, B, C, D0, D1, (* abc9_carry *) input CI, output SO, (* abc9_carry *) output CO);

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

wire q0, q1;

assign q0 = LUT0 >> {D0, C, B, A};
assign q1 = LUT1 >> {D1, C, B, A};

assign {CO, SO} = q0 + !q1 + CI;

endmodule
