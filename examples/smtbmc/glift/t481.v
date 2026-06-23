module t481_lev2(pi00, pi01, pi02, pi03, pi04, pi05, pi06, pi07, pi08, pi09, 
	pi10, pi11, pi12, pi13, pi14, pi15, po0);

input pi00, pi01, pi02, pi03, pi04, pi05, pi06, pi07, pi08, pi09, 
	pi10, pi11, pi12, pi13, pi14, pi15;

output po0;

wire n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, 
	n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, 
	n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, 
	n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, 
	n86, n87, n88, n89, n90;

  OR2 U47 ( .A(n46), .B(n47), .Z(po0));
  OR2 U48 ( .A(n48), .B(n49), .Z(n47));
  AN2 U49 ( .A(n50), .B(n51), .Z(n49));
  OR2 U50 ( .A(n52), .B(n53), .Z(n51));
  AN2 U51 ( .A(n54), .B(n55), .Z(n53));
  AN2 U52 ( .A(n56), .B(n57), .Z(n54));
  AN2 U53 ( .A(n58), .B(n59), .Z(n52));
  AN2 U54 ( .A(n60), .B(n61), .Z(n48));
  IV2 U55 ( .A(n50), .Z(n61));
  AN2 U56 ( .A(n62), .B(pi15), .Z(n50));
  IV2 U57 ( .A(pi14), .Z(n62));
  OR2 U58 ( .A(n63), .B(n64), .Z(n60));
  AN2 U59 ( .A(n65), .B(n55), .Z(n64));
  IV2 U60 ( .A(n59), .Z(n55));
  AN2 U61 ( .A(n57), .B(n58), .Z(n65));
  IV2 U62 ( .A(n56), .Z(n58));
  AN2 U63 ( .A(n56), .B(n59), .Z(n63));
  AN2 U64 ( .A(n66), .B(pi00), .Z(n56));
  IV2 U65 ( .A(pi01), .Z(n66));
  AN2 U66 ( .A(n67), .B(n59), .Z(n46));
  OR2 U67 ( .A(n68), .B(n69), .Z(n59));
  OR2 U68 ( .A(n70), .B(n71), .Z(n69));
  AN2 U69 ( .A(n72), .B(n73), .Z(n71));
  IV2 U70 ( .A(n74), .Z(n70));
  OR2 U71 ( .A(n73), .B(n72), .Z(n74));
  AN2 U72 ( .A(n75), .B(pi12), .Z(n72));
  IV2 U73 ( .A(pi13), .Z(n75));
  OR2 U74 ( .A(pi10), .B(n76), .Z(n73));
  IV2 U75 ( .A(pi11), .Z(n76));
  AN2 U76 ( .A(n77), .B(n78), .Z(n68));
  OR2 U77 ( .A(n79), .B(n80), .Z(n78));
  IV2 U78 ( .A(n81), .Z(n77));
  AN2 U79 ( .A(n80), .B(n79), .Z(n81));
  AN2 U80 ( .A(n82), .B(pi08), .Z(n79));
  IV2 U81 ( .A(pi09), .Z(n82));
  OR2 U82 ( .A(pi06), .B(n83), .Z(n80));
  IV2 U83 ( .A(pi07), .Z(n83));
  IV2 U84 ( .A(n57), .Z(n67));
  OR2 U85 ( .A(n84), .B(n85), .Z(n57));
  AN2 U86 ( .A(n86), .B(n87), .Z(n85));
  IV2 U87 ( .A(n88), .Z(n84));
  OR2 U88 ( .A(n87), .B(n86), .Z(n88));
  AN2 U89 ( .A(n89), .B(pi04), .Z(n86));
  IV2 U90 ( .A(pi05), .Z(n89));
  OR2 U91 ( .A(pi02), .B(n90), .Z(n87));
  IV2 U92 ( .A(pi03), .Z(n90));

endmodule

module IV2(A,  Z);
  input A;
  output Z;

  assign Z = ~A;
endmodule

module AN2(A,  B,  Z);
  input A,  B;
  output Z;

  assign Z = A & B;
endmodule

module OR2(A,  B,  Z);
  input A,  B;
  output Z;

  assign Z = A | B;
endmodule
