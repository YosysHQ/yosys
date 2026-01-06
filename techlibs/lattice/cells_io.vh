// Diamond I/O buffers
module IB   ((* iopad_external_pin *) input I,     output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("INPUT"))  _TECHMAP_REPLACE_ (.B(I), .O(O)); endmodule
module IBPU ((* iopad_external_pin *) input I,     output O); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("INPUT"))  _TECHMAP_REPLACE_ (.B(I), .O(O)); endmodule
module IBPD ((* iopad_external_pin *) input I,     output O); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("INPUT"))  _TECHMAP_REPLACE_ (.B(I), .O(O)); endmodule
module OB   (input I,     (* iopad_external_pin *) output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I)); endmodule
module OBZ  (input I, T,  (* iopad_external_pin *) output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I), .T(T)); endmodule
module OBZPU(input I, T,  (* iopad_external_pin *) output O); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I), .T(T)); endmodule
module OBZPD(input I, T,  (* iopad_external_pin *) output O); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I), .T(T)); endmodule
module OBCO (input I,     output OT, OC); OLVDS olvds (.A(I), .Z(OT), .ZN(OC)); endmodule
module BB   (input I, T,  output O, (* iopad_external_pin *) inout B); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("BIDIR")) _TECHMAP_REPLACE_ (.B(B), .I(I), .O(O), .T(T)); endmodule
module BBPU (input I, T,  output O, (* iopad_external_pin *) inout B); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("BIDIR")) _TECHMAP_REPLACE_ (.B(B), .I(I), .O(O), .T(T)); endmodule
module BBPD (input I, T,  output O, (* iopad_external_pin *) inout B); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("BIDIR")) _TECHMAP_REPLACE_ (.B(B), .I(I), .O(O), .T(T)); endmodule
module ILVDS(input A, AN, (* iopad_external_pin *) output Z    ); TRELLIS_IO #(.DIR("INPUT"))  _TECHMAP_REPLACE_ (.B(A), .O(Z)); endmodule
module OLVDS(input A,     (* iopad_external_pin *) output Z, output ZN); TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(Z), .I(A)); endmodule
