`default_nettype none

(* abc9_box *)
module MISTRAL_MUL27X27(input [26:0] A, input [26:0] B, output [53:0] Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;

`ifdef cyclonev
specify
    (A *> Y) = 3732;
    (B *> Y) = 3928;
endspecify
`endif
`ifdef arriav
// NOTE: Arria V appears to have only one set of timings for all DSP modes...
specify
    (A *> Y) = 1895;
    (B *> Y) = 2053;
endspecify
`endif
`ifdef cyclone10gx
// TODO: Cyclone 10 GX timings; the below are for Cyclone V
specify
    (A *> Y) = 3732;
    (B *> Y) = 3928;
endspecify
`endif

wire [53:0] A_, B_;

if (A_SIGNED)
    assign A_ = $signed(A);
else
    assign A_ = $unsigned(A);

if (B_SIGNED)
    assign B_ = $signed(B);
else
    assign B_ = $unsigned(B);

assign Y = A_ * B_;

endmodule

(* abc9_box *)
module MISTRAL_MUL18X18(input [17:0] A, input [17:0] B, output [35:0] Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;

`ifdef cyclonev
specify
    (A *> Y) = 3180;
    (B *> Y) = 3982;
endspecify
`endif
`ifdef arriav
// NOTE: Arria V appears to have only one set of timings for all DSP modes...
specify
    (A *> Y) = 1895;
    (B *> Y) = 2053;
endspecify
`endif
`ifdef cyclone10gx
// TODO: Cyclone 10 GX timings; the below are for Cyclone V
specify
    (A *> Y) = 3180;
    (B *> Y) = 3982;
endspecify
`endif

wire [35:0] A_, B_;

if (A_SIGNED)
    assign A_ = $signed(A);
else
    assign A_ = $unsigned(A);

if (B_SIGNED)
    assign B_ = $signed(B);
else
    assign B_ = $unsigned(B);

assign Y = A_ * B_;

endmodule

(* abc9_box *)
module MISTRAL_MUL9X9(input [8:0] A, input [8:0] B, output [17:0] Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;

`ifdef cyclonev
specify
    (A *> Y) = 2818;
    (B *> Y) = 3051;
endspecify
`endif
`ifdef arriav
// NOTE: Arria V appears to have only one set of timings for all DSP modes...
specify
    (A *> Y) = 1895;
    (B *> Y) = 2053;
endspecify
`endif
`ifdef cyclone10gx
// TODO: Cyclone 10 GX timings; the below are for Cyclone V
specify
    (A *> Y) = 2818;
    (B *> Y) = 3051;
endspecify
`endif

wire [17:0] A_, B_;

if (A_SIGNED)
    assign A_ = $signed(A);
else
    assign A_ = $unsigned(A);

if (B_SIGNED)
    assign B_ = $signed(B);
else
    assign B_ = $unsigned(B);

assign Y = A_ * B_;

endmodule
