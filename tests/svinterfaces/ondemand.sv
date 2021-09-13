// This is used by the load_and_derive test.

module ondemand (iface intf);
  assign intf.y = ~intf.x;
endmodule
