
module $__NX_XRFB_64x18_ (input PORT_W_CLK, input [5:0] PORT_W_ADDR, PORT_R_ADDR, input [17:0] PORT_W_WR_DATA, input PORT_W_WR_EN, output [17:0] PORT_R_RD_DATA);
  parameter INIT = 1152'bx;
  parameter PORT_W_CLK_POL = 1'b1;
  NX_XRFB_64x18 #(.mem_ctxt(INIT), .wck_edge(~PORT_W_CLK_POL)) _TECHMAP_REPLACE_ (.WCK(PORT_W_CLK), .I(PORT_W_WR_DATA), .RA(PORT_R_ADDR), .WA(PORT_W_ADDR), .WE(PORT_W_WR_EN), .WEA(1'b1), .O(PORT_R_RD_DATA));
endmodule

module $__NX_XRFB_32x36_ (input PORT_W_CLK, input [4:0] PORT_W_ADDR, PORT_R_ADDR, input [35:0] PORT_W_WR_DATA, input PORT_W_WR_EN, output [35:0] PORT_R_RD_DATA);
  parameter INIT = 1152'bx;
  parameter PORT_W_CLK_POL = 1'b1;
  NX_XRFB_32x36 #(.mem_ctxt(INIT), .wck_edge(~PORT_W_CLK_POL)) _TECHMAP_REPLACE_ (.WCK(PORT_W_CLK), .I(PORT_W_WR_DATA), .RA(PORT_R_ADDR), .WA(PORT_W_ADDR), .WE(PORT_W_WR_EN), .WEA(1'b1), .O(PORT_R_RD_DATA));
endmodule
