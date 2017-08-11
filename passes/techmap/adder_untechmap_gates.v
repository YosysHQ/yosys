module __XOR3_ (input A, input B, input C, output Y);
    assign Y = A ^ B ^ C;
endmodule

module __MAJ_ (input A, input B, input C, output Y);
    assign Y = (A & B) | (A & C) | (B & C);
endmodule
