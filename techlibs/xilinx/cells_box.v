(* abc_box_id = 1 *)
module MUXF7(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

(* abc_box_id = 2 *)
module MUXF8(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

(* abc_box_id = 3 *)
module MUXCY(output O, input CI, DI, S);
  assign O = S ? CI : DI;
endmodule

(* abc_box_id = 4 *)
module XORCY(output O, input CI, LI);
  assign O = CI ^ LI;
endmodule
