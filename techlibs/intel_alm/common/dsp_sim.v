(* abc9_box *)
module MISTRAL_MUL27X27(input [26:0] A, input [26:0] B, output [53:0] Y);

// TODO: Cyclone 10 GX timings; the below are for Cyclone V
specify
    (A *> Y) = 3732;
    (B *> Y) = 3928;
endspecify

assign Y = $signed(A) * $signed(B);

endmodule

(* abc9_box *)
module MISTRAL_MUL18X18(input [17:0] A, input [17:0] B, output [35:0] Y);

// TODO: Cyclone 10 GX timings; the below are for Cyclone V
specify
    (A *> Y) = 3180;
    (B *> Y) = 3982;
endspecify

assign Y = $signed(A) * $signed(B);

endmodule

(* abc9_box *)
module MISTRAL_MUL9X9(input [8:0] A, input [8:0] B, output [17:0] Y);

// TODO: Cyclone 10 GX timings; the below are for Cyclone V
specify
    (A *> Y) = 2818;
    (B *> Y) = 3051;
endspecify

assign Y = $signed(A) * $signed(B);

endmodule
