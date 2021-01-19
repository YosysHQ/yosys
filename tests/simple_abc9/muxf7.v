(* abc9_box, abc9_box_id=2, whitebox *)
module MUXF7(input I0, I1, S, output O);
assign O = S ? I1 : I0;
specify
    (I0 => O) = 0;
    (I1 => O) = 0;
    (S => O) = 0;
endspecify
endmodule


