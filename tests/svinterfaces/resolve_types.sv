// This test checks that types, including package types, are resolved from within an interface.

typedef logic [7:0] x_t;

package pkg;
    typedef logic [7:0] y_t;
endpackage

interface iface;
    x_t x;
    pkg::y_t y;
endinterface

module dut (input logic [7:0] x, output logic [7:0] y);
  iface intf();
  assign intf.x = x;
  assign y = intf.y;

  ondemand u(.intf);
endmodule

module ref (input logic [7:0] x, output logic [7:0] y);
  assign y = ~x;
endmodule
