module $__NX_RFB_M_ (
  input PORT_W_CLK,
  input PORT_W_WR_EN,
  input [5:0] PORT_W_ADDR,
  input [15:0] PORT_W_WR_DATA, 
  input PORT_R_CLK,
  input PORT_R_RD_EN,
  input [5:0] PORT_R_ADDR,
  output [15:0] PORT_R_RD_DATA,
);
  parameter INIT = 1152'bx;
  parameter PORT_W_CLK_POL = 1'b1;
  parameter PORT_R_CLK_POL = 1'b1;

  NX_RFB_M_WRAP #(
    .mode(0),
    .mem_ctxt(INIT),
    .rck_edge(~PORT_R_CLK_POL),
    .wck_edge(~PORT_W_CLK_POL)
  ) _TECHMAP_REPLACE_ (
    .RCK(PORT_R_CLK),
    .WCK(PORT_W_CLK),
    .I(PORT_W_WR_DATA),
    .RA(PORT_R_ADDR),
    .WA(PORT_W_ADDR),
    .RE(PORT_R_RD_EN),
    .WE(PORT_W_WR_EN),
    .O(PORT_R_RD_DATA)
  );
endmodule
