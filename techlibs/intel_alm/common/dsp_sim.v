(* abc9_box *)
module MISTRAL_MUL27x27(input [26:0] A, input [26:0] B, output [53:0] Y);

specify
    (A *> Y) = 4057;
    (B *> Y) = 4057;
endspecify

assign Y = $signed(A) * $signed(B);

endmodule

(* abc9_box *)
module MISTRAL_MUL18X18(input [17:0] A, input [17:0] B, output [35:0] Y);

specify
    (A *> Y) = 4057;
    (B *> Y) = 4057;
endspecify

assign Y = $signed(A) * $signed(B);

endmodule

(* abc9_box *)
module MISTRAL_MUL9X9(input [8:0] A, input [8:0] B, output [17:0] Y);

specify
    (A *> Y) = 4057;
    (B *> Y) = 4057;
endspecify

assign Y = $signed(A) * $signed(B);

endmodule
