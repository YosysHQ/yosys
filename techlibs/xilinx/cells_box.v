(* abc_box_id = 1 *)
module MUXF7(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

(* abc_box_id = 2 *)
module MUXF8(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

