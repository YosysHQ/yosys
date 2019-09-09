// Black Box
// black_box_1.v
// 
(* black_box *) module black_box1 (in1, in2, dout);
input in1, in2;
output dout;
endmodule

module black_box_1 (DI_1, DI_2, DOUT);
input DI_1, DI_2;
output DOUT;

black_box1 U1 (
                .in1(DI_1),
                .in2(DI_2),
                .dout(DOUT)
              );

endmodule
