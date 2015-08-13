module t_gate_switch (L,R,nC,C);
 inout L;
 inout R;
 input nC;
 input C;

 //Syntax: keyword unique_name (drain. source, gate);
 pmos p1 (L,R,nC);
 nmos p2 (L,R,C);

endmodule
