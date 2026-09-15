// Pad cells inserted by synth_fabulous via iopadmap.
// Mapped to fabric primitives by a user supplied -extra-map.

(* blackbox *)
module \$__FABULOUS_IBUF (input PAD, output OUT);
endmodule

(* blackbox *)
module \$__FABULOUS_OBUF (output PAD, input IN);
endmodule

(* blackbox *)
module \$__FABULOUS_TBUF (output PAD, input IN, input EN);
endmodule

(* blackbox *)
module \$__FABULOUS_IOBUF (inout PAD, output OUT, input IN, input EN);
endmodule
