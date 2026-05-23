// The core logic primitive of the Cyclone IVE/IVGX is the Logic Element
// (LE). Each LE is made up of an 4-input, 1-output look-up table, covered 
// in this file, connected to combinational outputs, a carry chain, and one
// D flip-flop (which are covered as MISTRAL_FF in dff_sim.v).
//
// LEs are have two modes of operation
//
// Normal (combinational) mode
// ---------------------------
// The LE can implement:
// - a single 4-input(or less) function 
//
// Normal-mode functions are represented as MISTRAL_ALUTN cells with N inputs.
//
// Arithmetic mode
// ---------------
// In arithmetic mode, LE implements two bit adder and carry chain
// It can drive either registered or unregistered output. 
//
// The cell for an arithmetic-mode is MISTRAL_ALM_ARITH.
//

`default_nettype none

// Cyclone V LUT output timings (picoseconds):
//
//          CARRY   A    B    C   D  
//  COMBOUT  ?408? 332  337  220 119  
// CARRYOUT   200  376  385    ?   -


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_ALUT4(input A, B, C, D, output Q);

parameter [15:0] LUT = 16'h0000;

`ifdef cycloneiv
specify
    (A => Q) = 337; 
    (B => Q) = 332;
    (C => Q) = 220;
    (D => Q) = 119;
endspecify
`endif

assign Q = LUT >> {D, C, B, A};

endmodule


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_ALUT3(input A, B, C, output Q);

parameter [7:0] LUT = 8'h00;

`ifdef cycloneiv 
specify 
    (A => Q) = 332;
    (B => Q) = 220;
    (C => Q) = 119;
endspecify
`endif
assign Q = LUT >> {C, B, A};

endmodule


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_ALUT2(input A, B, output Q);

parameter [3:0] LUT = 4'h0;

`ifdef cycloneiv 
specify
    (A => Q) = 220;
    (B => Q) = 119;
endspecify
`endif
assign Q = LUT >> {B, A};

endmodule


(* abc9_lut=1, lib_whitebox *)
module MISTRAL_NOT(input A, output Q);

`ifdef cycloneiv  
specify
    (A => Q) = 119;
endspecify
`endif
assign Q = ~A;

endmodule

(* abc9_box, lib_whitebox *)
module MISTRAL_ALUT_ARITH(input A, B, C, D, (* abc9_carry *) input CI, output SO, (* abc9_carry *) output CO);

parameter LUT = 16'h0000;


`ifdef cycloneiv   
specify
    (A  => SO) = 337;
    (B  => SO) = 332;
    (C  => SO) = 220;
    (D => SO) = 119;
    (CI => SO) = 08;

    (A  => CO) = 385;
    (B  => CO) = 376;
    (CI => CO) = 200;
endspecify
`endif
wire q0, q1;


assign q0 = LUT >> {'b0, CI, B, A};
assign q1 = LUT >> {D, CI, B, A};

assign SO = q1;

assign CO = q0;

endmodule


