// Diamond I/O buffers
module IB   (input I,     output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("INPUT"))  _TECHMAP_REPLACE_ (.B(I), .O(O)); endmodule
module IBPU (input I,     output O); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("INPUT"))  _TECHMAP_REPLACE_ (.B(I), .O(O)); endmodule
module IBPD (input I,     output O); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("INPUT"))  _TECHMAP_REPLACE_ (.B(I), .O(O)); endmodule
module OB   (input I,     output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I)); endmodule
module OBZ  (input I, T,  output O); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I), .T(T)); endmodule
module OBZPU(input I, T,  output O); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I), .T(T)); endmodule
module OBZPD(input I, T,  output O); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(O), .I(I), .T(T)); endmodule
module OBCO (input I,     output OT, OC); OLVDS olvds (.A(I), .Z(OT), .ZN(OC)); endmodule
module BB   (input I, T,  output O, inout B); (* PULLMODE="NONE" *) TRELLIS_IO #(.DIR("BIDIR")) _TECHMAP_REPLACE_ (.B(B), .I(I), .O(O), .T(T)); endmodule
module BBPU (input I, T,  output O, inout B); (* PULLMODE="UP"   *) TRELLIS_IO #(.DIR("BIDIR")) _TECHMAP_REPLACE_ (.B(B), .I(I), .O(O), .T(T)); endmodule
module BBPD (input I, T,  output O, inout B); (* PULLMODE="DOWN" *) TRELLIS_IO #(.DIR("BIDIR")) _TECHMAP_REPLACE_ (.B(B), .I(I), .O(O), .T(T)); endmodule
module ILVDS(input A, AN, output Z    ); TRELLIS_IO #(.DIR("INPUT"))  _TECHMAP_REPLACE_ (.B(A), .O(Z)); endmodule
module OLVDS(input A,     output Z, ZN); TRELLIS_IO #(.DIR("OUTPUT")) _TECHMAP_REPLACE_ (.B(Z), .I(A)); endmodule
