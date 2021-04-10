module inpad (
  output Q,
  (* iopad_external_pin *)
  input P
);
  specify
    (P => Q) = 0;
  endspecify
  assign Q = P;
endmodule

module outpad (
  (* iopad_external_pin *)
  output P,
  input A
);
  specify
    (A => P) = 0;
  endspecify
  assign P = A;
endmodule

module ckpad (
  output Q,
  (* iopad_external_pin *)
  input P
);
  specify
    (P => Q) = 0;
  endspecify
  assign Q = P;
endmodule

module bipad (
  input A,
  input EN,
  output Q,
  (* iopad_external_pin *)
  inout P
);
  assign Q = P;
  assign P = EN ? A : 1'bz;
endmodule

module dff (
  output reg Q,
  input D,
  (* clkbuf_sink *)
  input CLK
);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK) Q <= D;
endmodule

module dffc (
  output reg Q,
  input D,
  (* clkbuf_sink *)
  input CLK,
  (* clkbuf_sink *)
  input CLR
);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

  always @(posedge CLK or posedge CLR)
    if (CLR) Q <= 1'b0;
    else Q <= D;
endmodule

module dffp (
  output reg Q,
  input D,
  (* clkbuf_sink *)
  input CLK,
  (* clkbuf_sink *)
  input PRE
);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

  always @(posedge CLK or posedge PRE)
    if (PRE) Q <= 1'b1;
    else Q <= D;
endmodule

module dffpc (
  output reg Q,
  input D,
  (* clkbuf_sink *)
  input CLK,
  (* clkbuf_sink *)
  input CLR,
  (* clkbuf_sink *)
  input PRE
);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

  always @(posedge CLK or posedge CLR or posedge PRE)
    if (CLR) Q <= 1'b0;
    else if (PRE) Q <= 1'b1;
    else Q <= D;
endmodule

module dffe (
  output reg Q,
  input D,
  (* clkbuf_sink *)
  input CLK,
  input EN
);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge CLK) if (EN) Q <= D;
endmodule

module dffec (
  output reg Q,
  input D,
  (* clkbuf_sink *)
  input CLK,
  input EN,
  (* clkbuf_sink *)
  input CLR
);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;

  always @(posedge CLK or posedge CLR)
    if (CLR) Q <= 1'b0;
    else if (EN) Q <= D;
endmodule

(* lib_whitebox *)
module dffepc (
  output reg Q,
  input D,
  (* clkbuf_sink *)
  input CLK,
  input EN,
  (* clkbuf_sink *)
  input CLR,
  (* clkbuf_sink *)
  input PRE
);
  parameter [0:0] INIT = 1'b0;

  // The CLR => Q and PRE => Q paths are commented out due to YosysHQ/yosys#2530.
  specify
    if (EN) (posedge CLK => (Q : D)) = 1701; // QCK -> QZ
    // if (CLR) (CLR => Q) = 967; // QRT -> QZ
    // if (PRE) (PRE => Q) = 1252; // QST -> QZ
    $setup(D, posedge CLK, 216); // QCK -> QDS
    $setup(EN, posedge CLK, 590); // QCK -> QEN
  endspecify

  initial Q = INIT;
  always @(posedge CLK or posedge CLR or posedge PRE)
    if (CLR) Q <= 1'b0;
    else if (PRE) Q <= 1'b1;
    else if (EN) Q <= D;
endmodule

//                  FZ       FS F2 (F1 TO 0)
(* abc9_box, lib_whitebox *)
module AND2I0 (
  output Q,
  input A, B
);
  specify
    (A => Q) = 698; // FS -> FZ
    (B => Q) = 639; // F2 -> FZ
  endspecify

  assign Q = A ? B : 0;
endmodule

(* abc9_box, lib_whitebox *)
module mux2x0 (
  output Q,
  input S, A, B
);
  specify
    (S => Q) = 698; // FS -> FZ
    (A => Q) = 639; // F1 -> FZ
    (B => Q) = 639; // F2 -> FZ
  endspecify

  assign Q = S ? B : A;
endmodule

(* abc9_box, lib_whitebox *)
module mux2x1 (
  output Q,
  input S, A, B
);
  specify
    (S => Q) = 698; // FS -> FZ
    (A => Q) = 639; // F1 -> FZ
    (B => Q) = 639; // F2 -> FZ
  endspecify

  assign Q = S ? B : A;
endmodule

(* abc9_box, lib_whitebox *)
module mux4x0 (
  output Q,
  input S0, S1, A, B, C, D
);
  specify
    (S0 => Q) = 1251; // TAB -> TZ
    (S1 => Q) = 1406; // TSL -> TZ
    (A => Q) = 1699;  // TA1 -> TZ
    (B => Q) = 1687;  // TA2 -> TZ
    (C => Q) = 1669;  // TB1 -> TZ
    (D => Q) = 1679;  // TB2 -> TZ
  endspecify

  assign Q = S1 ? (S0 ? D : C) : (S0 ? B : A);
endmodule

// S0 BSL TSL
// S1 BAB TAB
// S2 TBS
// A TA1
// B TA2
// C TB1
// D TB2
// E BA1
// F BA2
// G BB1
// H BB2
// Q CZ
(* abc9_box, lib_whitebox *)
module mux8x0 (
  output Q,
  input S0, S1, S2, A, B, C, D, E, F, G, H
);
  specify
    (S0 => Q) = 1593; // ('TSL', 'BSL') -> CZ
    (S1 => Q) = 1437; // ('TAB', 'BAB') -> CZ
    (S2 => Q) = 995; // TBS -> CZ
    (A => Q) = 1887; // TA1 -> CZ
    (B => Q) = 1873; // TA2 -> CZ
    (C => Q) = 1856; // TB1 -> CZ
    (D => Q) = 1860; // TB2 -> CZ
    (E => Q) = 1714; // BA1 -> CZ
    (F => Q) = 1773; // BA2 -> CZ
    (G => Q) = 1749; // BB1 -> CZ
    (H => Q) = 1723; // BB2 -> CZ
  endspecify

  assign Q = S2 ? (S1 ? (S0 ? H : G) : (S0 ? F : E)) : (S1 ? (S0 ? D : C) : (S0 ? B : A));
endmodule

(* blackbox *)
(* keep *)
module qlal4s3b_cell_macro (
  input WB_CLK,
  input WBs_ACK,
  input [31:0] WBs_RD_DAT,
  output [3:0] WBs_BYTE_STB,
  output WBs_CYC,
  output WBs_WE,
  output WBs_RD,
  output WBs_STB,
  output [16:0] WBs_ADR,
  input [3:0] SDMA_Req,
  input [3:0] SDMA_Sreq,
  output [3:0] SDMA_Done,
  output [3:0] SDMA_Active,
  input [3:0] FB_msg_out,
  input [7:0] FB_Int_Clr,
  output FB_Start,
  input FB_Busy,
  output WB_RST,
  output Sys_PKfb_Rst,
  output Clk16,
  output Clk16_Rst,
  output Clk21,
  output Clk21_Rst,
  output Sys_Pclk,
  output Sys_Pclk_Rst,
  input Sys_PKfb_Clk,
  input [31:0] FB_PKfbData,
  output [31:0] WBs_WR_DAT,
  input [3:0] FB_PKfbPush,
  input FB_PKfbSOF,
  input FB_PKfbEOF,
  output [7:0] Sensor_Int,
  output FB_PKfbOverflow,
  output [23:0] TimeStamp,
  input Sys_PSel,
  input [15:0] SPIm_Paddr,
  input SPIm_PEnable,
  input SPIm_PWrite,
  input [31:0] SPIm_PWdata,
  output SPIm_PReady,
  output SPIm_PSlvErr,
  output [31:0] SPIm_Prdata,
  input [15:0] Device_ID,
  input [13:0] FBIO_In_En,
  input [13:0] FBIO_Out,
  input [13:0] FBIO_Out_En,
  output [13:0] FBIO_In,
  inout [13:0] SFBIO,
  input Device_ID_6S,
  input Device_ID_4S,
  input SPIm_PWdata_26S,
  input SPIm_PWdata_24S,
  input SPIm_PWdata_14S,
  input SPIm_PWdata_11S,
  input SPIm_PWdata_0S,
  input SPIm_Paddr_8S,
  input SPIm_Paddr_6S,
  input FB_PKfbPush_1S,
  input FB_PKfbData_31S,
  input FB_PKfbData_21S,
  input FB_PKfbData_19S,
  input FB_PKfbData_9S,
  input FB_PKfbData_6S,
  input Sys_PKfb_ClkS,
  input FB_BusyS,
  input WB_CLKS
);

endmodule


(* blackbox *)
module ram8k_2x1_cell_macro #(
  parameter [18431:0] INIT = 18432'bx,
  parameter INIT_FILE = "init.mem",
  parameter data_width_int = 16,
  parameter data_depth_int = 1024
) (
  input [10:0] A1_0,
  input [10:0] A1_1,
  input [10:0] A2_0,
  input [10:0] A2_1,
  (* clkbuf_sink *)
  input CLK1_0,
  (* clkbuf_sink *)
  input CLK1_1,
  (* clkbuf_sink *)
  input CLK2_0,
  (* clkbuf_sink *)
  input CLK2_1,
  output Almost_Empty_0,
  Almost_Empty_1,
  Almost_Full_0,
  Almost_Full_1,
  input ASYNC_FLUSH_0,
  ASYNC_FLUSH_1,
  ASYNC_FLUSH_S0,
  ASYNC_FLUSH_S1,
  CLK1EN_0,
  CLK1EN_1,
  CLK1S_0,
  CLK1S_1,
  CLK2EN_0,
  CLK2EN_1,
  CLK2S_0,
  CLK2S_1,
  CONCAT_EN_0,
  CONCAT_EN_1,
  CS1_0,
  CS1_1,
  CS2_0,
  CS2_1,
  DIR_0,
  DIR_1,
  FIFO_EN_0,
  FIFO_EN_1,
  P1_0,
  P1_1,
  P2_0,
  P2_1,
  PIPELINE_RD_0,
  PIPELINE_RD_1,
  output [3:0] POP_FLAG_0,
  output [3:0] POP_FLAG_1,
  output [3:0] PUSH_FLAG_0,
  output [3:0] PUSH_FLAG_1,
  output [17:0] RD_0,
  output [17:0] RD_1,
  input SYNC_FIFO_0,
  SYNC_FIFO_1,
  input [17:0] WD_0,
  input [17:0] WD_1,
  input [1:0] WEN1_0,
  input [1:0] WEN1_1,
  input [1:0] WIDTH_SELECT1_0,
  input [1:0] WIDTH_SELECT1_1,
  input [1:0] WIDTH_SELECT2_0,
  input [1:0] WIDTH_SELECT2_1,
  input SD,
  DS,
  LS,
  SD_RB1,
  LS_RB1,
  DS_RB1,
  RMEA,
  RMEB,
  TEST1A,
  TEST1B,
  input [3:0] RMA,
  input [3:0] RMB
);

  specify
    $setup(A1_0, posedge CLK1_0, 0);
    $setup(A1_1, posedge CLK1_1, 0);
    $setup(A2_0, posedge CLK2_0, 0);
    $setup(A2_1, posedge CLK2_1, 0);

    (posedge CLK1_0 => (RD_0 : WD_0)) = 0;
    (posedge CLK2_0 => (RD_1 : WD_1)) = 0;
  endspecify

  // This is a black box of the block RAM.
  // The actual simulation model is [TODO: somewhere else].

endmodule  /* ram8k_2x1_cell_macro */
