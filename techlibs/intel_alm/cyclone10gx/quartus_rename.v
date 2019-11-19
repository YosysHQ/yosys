module MISTRAL_ALUT6(input A, B, C, D, E, F, output Q);
parameter LUT = 64'h0000_0000_0000_0000;

cyclone10gx_lcell_comb #(.lut_mask(LUT)) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D), .datae(E), .dataf(F), .combout(Q));

endmodule


module MISTRAL_ALUT5(input A, B, C, D, E, output Q);
parameter LUT = 32'h0000_0000;

cyclone10gx_lcell_comb #(.lut_mask({2{LUT}})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D), .datae(E), .combout(Q));

endmodule


module MISTRAL_ALUT4(input A, B, C, D, output Q);
parameter LUT = 16'h0000;

cyclone10gx_lcell_comb #(.lut_mask({4{LUT}})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D), .combout(Q));

endmodule


module MISTRAL_ALUT3(input A, B, C, output Q);
parameter LUT = 8'h00;

cyclone10gx_lcell_comb #(.lut_mask({8{LUT}})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .combout(Q));

endmodule


module MISTRAL_ALUT2(input A, B, output Q);
parameter LUT = 4'h0;

cyclone10gx_lcell_comb #(.lut_mask({16{LUT}})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .combout(Q));

endmodule


module MISTRAL_NOT(input A, output Q);

NOT _TECHMAP_REPLACE_ (.IN(A), .OUT(Q));

endmodule


module MISTRAL_ALUT_ARITH(input A, B, C, D0, D1, CI, output SO, CO);
parameter LUT0 = 16'h0000;
parameter LUT1 = 16'h0000;

cyclone10gx_lcell_comb #(.lut_mask({16'h0, LUT1, 16'h0, LUT0})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D0), .dataf(D1), .cin(CI), .sumout(SO), .cout(CO));

endmodule
