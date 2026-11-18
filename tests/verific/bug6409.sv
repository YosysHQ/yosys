interface ifc;
  logic x, y;
  modport mp (output x, output y);
endinterface

module user(ifc.mp p);
  assign p.y = 1'b0;
endmodule

module top(output logic x, output logic y);
  ifc p();
  user u(p);
  assign p.x = 1'b1;
  assign x = p.x;
  assign y = p.y;
endmodule
