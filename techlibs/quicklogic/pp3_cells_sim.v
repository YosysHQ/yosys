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


module logic_cell_macro (
  input BA1,
  input BA2,
  input BAB,
  input BAS1,
  input BAS2,
  input BB1,
  input BB2,
  input BBS1,
  input BBS2,
  input BSL,
  input F1,
  input F2,
  input FS,
  input QCK,
  input QCKS,
  input QDI,
  input QDS,
  input QEN,
  input QRT,
  input QST,
  input TA1,
  input TA2,
  input TAB,
  input TAS1,
  input TAS2,
  input TB1,
  input TB2,
  input TBS,
  input TBS1,
  input TBS2,
  input TSL,
  output CZ,
  output FZ,
  output QZ,
  output TZ
);

  wire TAP1, TAP2, TBP1, TBP2, BAP1, BAP2, BBP1, BBP2, QCKP, TAI, TBI, BAI, BBI, TZI, BZI, CZI, QZI;
  reg QZ_r;

  initial begin
    QZ_r = 1'b0;
  end
  assign QZ = QZ_r;
  assign TAP1 = TAS1 ? ~TA1 : TA1;
  assign TAP2 = TAS2 ? ~TA2 : TA2;
  assign TBP1 = TBS1 ? ~TB1 : TB1;
  assign TBP2 = TBS2 ? ~TB2 : TB2;
  assign BAP1 = BAS1 ? ~BA1 : BA1;
  assign BAP2 = BAS2 ? ~BA2 : BA2;
  assign BBP1 = BBS1 ? ~BB1 : BB1;
  assign BBP2 = BBS2 ? ~BB2 : BB2;

  assign TAI = TSL ? TAP2 : TAP1;
  assign TBI = TSL ? TBP2 : TBP1;
  assign BAI = BSL ? BAP2 : BAP1;
  assign BBI = BSL ? BBP2 : BBP1;
  assign TZI = TAB ? TBI : TAI;
  assign BZI = BAB ? BBI : BAI;
  assign CZI = TBS ? BZI : TZI;
  assign QZI = QDS ? QDI : CZI;
  assign FZ = FS ? F2 : F1;
  assign TZ = TZI;
  assign CZ = CZI;
  assign QCKP = QCKS ? QCK : ~QCK;


  always @(posedge QCKP) if (~QRT && ~QST) if (QEN) QZ_r = QZI;
  always @(QRT or QST)
    if (QRT) QZ_r = 1'b0;
    else if (QST) QZ_r = 1'b1;

endmodule

// BLACK BOXES

`timescale 1ns / 10ps
module ahb_gen_bfm (

  // AHB Slave Interface to AHB Bus Matrix
  //
  A2F_HCLK,
  A2F_HRESET,

  A2F_HADDRS,
  A2F_HSEL,
  A2F_HTRANSS,
  A2F_HSIZES,
  A2F_HWRITES,
  A2F_HREADYS,
  A2F_HWDATAS,

  A2F_HREADYOUTS,
  A2F_HRESPS,
  A2F_HRDATAS

);

  //------Port Parameters----------------
  //

  parameter ADDRWIDTH = 32;
  parameter DATAWIDTH = 32;

  //
  // Define the default address between transfers
  //
  parameter DEFAULT_AHB_ADDRESS = {(ADDRWIDTH) {1'b1}};

  //
  // Define the standard delay from clock
  //
  parameter STD_CLK_DLY = 2;

  //
  // Define Debug Message Controls
  //
  parameter ENABLE_AHB_REG_WR_DEBUG_MSG = 1'b1;
  parameter ENABLE_AHB_REG_RD_DEBUG_MSG = 1'b1;

  //
  // Define the size of the message arrays
  //
  parameter TEST_MSG_ARRAY_SIZE = (64 * 8);


  //------Port Signals-------------------
  //

  // AHB connection to master
  //
  input A2F_HCLK;
  input A2F_HRESET;

  output [ADDRWIDTH-1:0] A2F_HADDRS;
  output A2F_HSEL;
  output [1:0] A2F_HTRANSS;
  output [2:0] A2F_HSIZES;
  output A2F_HWRITES;
  output A2F_HREADYS;
  output [DATAWIDTH-1:0] A2F_HWDATAS;

  input A2F_HREADYOUTS;
  input A2F_HRESPS;
  input [DATAWIDTH-1:0] A2F_HRDATAS;


  wire A2F_HCLK;
  wire A2F_HRESET;

  reg [ADDRWIDTH-1:0] A2F_HADDRS;
  reg A2F_HSEL;
  reg [1:0] A2F_HTRANSS;
  reg [2:0] A2F_HSIZES;
  reg A2F_HWRITES;
  reg A2F_HREADYS;
  reg [DATAWIDTH-1:0] A2F_HWDATAS;

  wire A2F_HREADYOUTS;
  wire A2F_HRESPS;
  wire [DATAWIDTH-1:0] A2F_HRDATAS;


  //------Define Parameters--------------
  //

  //
  // None at this time
  //

  //------Internal Signals---------------
  //

  //	Define internal signals
  //
  reg [TEST_MSG_ARRAY_SIZE-1:0] ahb_bfm_msg1;  // Bus used for depositing test messages in ASCI
  reg [TEST_MSG_ARRAY_SIZE-1:0] ahb_bfm_msg2;  // Bus used for depositing test messages in ASCI
  reg [TEST_MSG_ARRAY_SIZE-1:0] ahb_bfm_msg3;  // Bus used for depositing test messages in ASCI
  reg [TEST_MSG_ARRAY_SIZE-1:0] ahb_bfm_msg4;  // Bus used for depositing test messages in ASCI
  reg [TEST_MSG_ARRAY_SIZE-1:0] ahb_bfm_msg5;  // Bus used for depositing test messages in ASCI
  reg [TEST_MSG_ARRAY_SIZE-1:0] ahb_bfm_msg6;  // Bus used for depositing test messages in ASCI


  //------Logic Operations---------------
  //

  // Define the intial state of key signals
  //
  initial begin

    A2F_HADDRS  <= DEFAULT_AHB_ADDRESS;  // Default Address
    A2F_HSEL    <= 1'b0;  // Bridge not selected
    A2F_HTRANSS <= 2'h0;  // "IDLE" State
    A2F_HSIZES  <= 3'h0;  // "Byte" Transfer Size
    A2F_HWRITES <= 1'b0;  // "Read" operation
    A2F_HREADYS <= 1'b0;  // Slave is not ready
    A2F_HWDATAS <= {(DATAWIDTH) {1'b0}};  // Write Data Value of "0"

    ahb_bfm_msg1 <= "NO ACTIVITY";  // Bus used for depositing test messages in ASCI
    ahb_bfm_msg2 <= "NO ACTIVITY";  // Bus used for depositing test messages in ASCI
    ahb_bfm_msg3 <= "NO ACTIVITY";  // Bus used for depositing test messages in ASCI
    ahb_bfm_msg4 <= "NO ACTIVITY";  // Bus used for depositing test messages in ASCI
    ahb_bfm_msg5 <= "NO ACTIVITY";  // Bus used for depositiog test messages in ASCI
    ahb_bfm_msg6 <= "NO ACTIVITY";  // Bus used for depositiog test messages in ASCI
  end


  //------Instantiate Modules------------
  //

  //
  // None at this time
  //


  //------BFM Routines-------------------
  //
`ifndef YOSYS
  task ahb_read_al4s3b_fabric;
    input  [ADDRWIDTH-1:0] TARGET_ADDRESS;   //        Address to be written on the SPI bus
    input            [2:0] TARGET_XFR_SIZE;  //        Transfer Size for AHB bus
    output [DATAWIDTH-1:0] TARGET_DATA;      //        Data    to be written on the SPI bus

    reg [DATAWIDTH-1:0] read_data;

    integer i, j, k;

    begin
      // Read Command Bit
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      // Issue Diagnostic Messages
      //
      ahb_bfm_msg1 = "AHB Single Read";
      ahb_bfm_msg2 = "Address Phase";
      ahb_bfm_msg3 = "SEQ";

      A2F_HADDRS = TARGET_ADDRESS;  // Transfer Address

      // Define the Transfer Request
      //
      // Transfer decode of: A2F_HTRANS[1]  A2F_HTRANS[0]  Description
      //                     -------------  -------------  ------------------------------------
      //                          0             0            IDLE               (No Transfer)
      //                          0             1            BUSY               (No Transfer)
      //                          1             0            NONSEQ             (Do Transfer)
      //                          1             1            SEQ                (Do Transfer)
      //
      // Transfer decode of: A2F_HREADYS                   Description
      //                     -----------                   ------------------------------------
      //                          0                          Slave is not ready (No Transfer)
      //                          1                          Slave is     ready (Do Transfer)
      //
      A2F_HSEL = 1'b1;     // Bridge   selected
      A2F_HREADYS = 1'b1;  // Slave is ready
      A2F_HTRANSS = 2'h2;  // "NONSEQ" State

      //
      // Define "Transfer Size Encoding" is based on the following:
      //
      //       HSIZE[2]  HSIZE[1]  HSIZE[0]  Bits  Description
      //       --------  --------  --------  ----  -----------
      //          0         0         0         8  Byte
      //          0         0         1        16  Halfword
      //          0         1         0        32  Word
      //          0         1         1        64  Doublword
      //          1         0         0       128  4-word line
      //          1         0         1       256  8-word line
      //          1         1         0       512  -
      //          1         1         1      1024  -
      //
      //       The fabric design only supports up to 32 bits at a time.
      //
      A2F_HSIZES = TARGET_XFR_SIZE;  // Transfer Size

      A2F_HWRITES = 1'b0;  // "Read"  operation
      A2F_HWDATAS = {(DATAWIDTH) {1'b0}};  // Write Data Value of "0"

      //
      // Wait for next clock to sampe the slave's response
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      ahb_bfm_msg2 = "Data Phase";
      ahb_bfm_msg3 = "IDLE";
      ahb_bfm_msg4 = "Waiting for Slave";

      // Set the next transfer cycle to "IDLE"
      A2F_HADDRS = DEFAULT_AHB_ADDRESS;  // Default Address
      A2F_HSEL = 1'b0;     // Bridge not selected
      A2F_HTRANSS = 2'h0;  // "IDLE" State
      A2F_HSIZES = 3'h0;   // "Byte" Transfer Size

      //
      // Check if the slave has returend data
      //
      while (A2F_HREADYOUTS == 1'b0) begin
        @(posedge A2F_HCLK) #STD_CLK_DLY;
      end

      A2F_HREADYS = 1'b0;  // Slave is not ready
      TARGET_DATA = A2F_HRDATAS;  // Read slave data value

      // Clear Diagnostic Messages
      //
      ahb_bfm_msg1 <= "NO ACTIVITY";
      ahb_bfm_msg2 <= "NO ACTIVITY";
      ahb_bfm_msg3 <= "NO ACTIVITY";
      ahb_bfm_msg4 <= "NO ACTIVITY";
      ahb_bfm_msg5 <= "NO ACTIVITY";
      ahb_bfm_msg6 <= "NO ACTIVITY";

    end
  endtask


  task ahb_write_al4s3b_fabric;
    input [ADDRWIDTH-1:0] TARGET_ADDRESS;   //        Address to be written on the SPI bus
    input           [2:0] TARGET_XFR_SIZE;  //        Transfer Size for AHB bus
    input [DATAWIDTH-1:0] TARGET_DATA;      //        Data    to be written on the SPI bus

    reg [DATAWIDTH-1:0] read_data;

    integer i, j, k;

    begin
      // Read Command Bit
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      // Issue Diagnostic Messages
      //
      ahb_bfm_msg1 = "AHB Single Write";
      ahb_bfm_msg2 = "Address Phase";
      ahb_bfm_msg3 = "SEQ";

      A2F_HADDRS = TARGET_ADDRESS;  // Transfer Address

      // Define the Transfer Request
      //
      // Transfer decode of: A2F_HTRANS[1]  A2F_HTRANS[0]  Description
      //                     -------------  -------------  ------------------------------------
      //                          0             0            IDLE               (No Transfer)
      //                          0             1            BUSY               (No Transfer)
      //                          1             0            NONSEQ             (Do Transfer)
      //                          1             1            SEQ                (Do Transfer)
      //
      // Transfer decode of: A2F_HREADYS                   Description
      //                     -----------                   ------------------------------------
      //                          0                          Slave is not ready (No Transfer)
      //                          1                          Slave is     ready (Do Transfer)
      //
      A2F_HSEL = 1'b1;     // Bridge   selected
      A2F_HREADYS = 1'b1;  // Slave is ready
      A2F_HTRANSS = 2'h2;  // "NONSEQ" State

      //
      // Define "Transfer Size Encoding" is based on the following:
      //
      //       HSIZE[2]  HSIZE[1]  HSIZE[0]  Bits  Description
      //       --------  --------  --------  ----  -----------
      //          0         0         0         8  Byte
      //          0         0         1        16  Halfword
      //          0         1         0        32  Word
      //          0         1         1        64  Doublword
      //          1         0         0       128  4-word line
      //          1         0         1       256  8-word line
      //          1         1         0       512  -
      //          1         1         1      1024  -
      //
      //       The fabric design only supports up to 32 bits at a time.
      //
      A2F_HSIZES = TARGET_XFR_SIZE;  // Transfer Size

      A2F_HWRITES = 1'b1;  // "Write"  operation
      A2F_HWDATAS = {(DATAWIDTH) {1'b0}};  // Write Data Value of "0"

      //
      // Wait for next clock to sampe the slave's response
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      ahb_bfm_msg2 = "Data Phase";
      ahb_bfm_msg3 = "IDLE";
      ahb_bfm_msg4 = "Waiting for Slave";

      // Set the next transfer cycle to "IDLE"
      A2F_HADDRS = DEFAULT_AHB_ADDRESS;  // Default Address
      A2F_HSEL = 1'b0;     // Bridge not selected
      A2F_HTRANSS = 2'h0;  // "IDLE" State
      A2F_HSIZES = 3'h0;   // "Byte" Transfer Size
      A2F_HWDATAS = TARGET_DATA;  // Write From test routine
      A2F_HWRITES = 1'b0;  // "Read" operation

      //
      // Check if the slave has returend data
      //
      while (A2F_HREADYOUTS == 1'b0) begin
        @(posedge A2F_HCLK) #STD_CLK_DLY;
      end

      A2F_HREADYS = 1'b0;  // Slave is not ready
      TARGET_DATA = A2F_HRDATAS;  // Read slave data value

      // Clear Diagnostic Messages
      //
      ahb_bfm_msg1 <= "NO ACTIVITY";
      ahb_bfm_msg2 <= "NO ACTIVITY";
      ahb_bfm_msg3 <= "NO ACTIVITY";
      ahb_bfm_msg4 <= "NO ACTIVITY";
      ahb_bfm_msg5 <= "NO ACTIVITY";
      ahb_bfm_msg6 <= "NO ACTIVITY";

    end
  endtask

  task ahb_read_word_al4s3b_fabric;
    input  [ADDRWIDTH-1:0] TARGET_ADDRESS;  //        Address to be written on the SPI bus
    output [DATAWIDTH-1:0] TARGET_DATA;     //        Data    to be written on the SPI bus

    reg [DATAWIDTH-1:0] read_data;

    integer i, j, k;

    begin
      // Read Command Bit
      //

      wait(A2F_HRESET == 0);
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      // Issue Diagnostic Messages
      //
      ahb_bfm_msg1 = "AHB Single Read";
      ahb_bfm_msg2 = "Address Phase";
      ahb_bfm_msg3 = "SEQ";

      A2F_HADDRS = TARGET_ADDRESS;  // Transfer Address

      // Define the Transfer Request
      //
      // Transfer decode of: A2F_HTRANS[1]  A2F_HTRANS[0]  Description
      //                     -------------  -------------  ------------------------------------
      //                          0             0            IDLE               (No Transfer)
      //                          0             1            BUSY               (No Transfer)
      //                          1             0            NONSEQ             (Do Transfer)
      //                          1             1            SEQ                (Do Transfer)
      //
      // Transfer decode of: A2F_HREADYS                   Description
      //                     -----------                   ------------------------------------
      //                          0                          Slave is not ready (No Transfer)
      //                          1                          Slave is     ready (Do Transfer)
      //
      A2F_HSEL = 1'b1;     // Bridge   selected
      A2F_HREADYS = 1'b1;  // Slave is ready
      A2F_HTRANSS = 2'h2;  // "NONSEQ" State

      //
      // Define "Transfer Size Encoding" is based on the following:
      //
      //       HSIZE[2]  HSIZE[1]  HSIZE[0]  Bits  Description
      //       --------  --------  --------  ----  -----------
      //          0         0         0         8  Byte
      //          0         0         1        16  Halfword
      //          0         1         0        32  Word
      //          0         1         1        64  Doublword
      //          1         0         0       128  4-word line
      //          1         0         1       256  8-word line
      //          1         1         0       512  -
      //          1         1         1      1024  -
      //
      //       The fabric design only supports up to 32 bits at a time.
      //
      A2F_HSIZES = 3'b010;  // Transfer Size

      A2F_HWRITES = 1'b0;  // "Read"  operation
      A2F_HWDATAS = {(DATAWIDTH) {1'b0}};  // Write Data Value of "0"

      //
      // Wait for next clock to sampe the slave's response
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      ahb_bfm_msg2 = "Data Phase";
      ahb_bfm_msg3 = "IDLE";
      ahb_bfm_msg4 = "Waiting for Slave";

      // Set the next transfer cycle to "IDLE"
      A2F_HADDRS = DEFAULT_AHB_ADDRESS;  // Default Address
      A2F_HSEL = 1'b0;  // Bridge not selected
      A2F_HTRANSS = 2'h0;  // "IDLE" State
      A2F_HSIZES = 3'h0;  // "Byte" Transfer Size

      //
      // Check if the slave has returend data
      //
      while (A2F_HREADYOUTS == 1'b0) begin
        @(posedge A2F_HCLK) #STD_CLK_DLY;
      end

      A2F_HREADYS = 1'b0;  // Slave is not ready
      TARGET_DATA = A2F_HRDATAS;  // Read slave data value

      // Clear Diagnostic Messages
      //
      ahb_bfm_msg1 <= "NO ACTIVITY";
      ahb_bfm_msg2 <= "NO ACTIVITY";
      ahb_bfm_msg3 <= "NO ACTIVITY";
      ahb_bfm_msg4 <= "NO ACTIVITY";
      ahb_bfm_msg5 <= "NO ACTIVITY";
      ahb_bfm_msg6 <= "NO ACTIVITY";

    end
  endtask


  task ahb_write_word_al4s3b_fabric;
    input [ADDRWIDTH-1:0] TARGET_ADDRESS;  //        Address to be written on the SPI bus
    input [DATAWIDTH-1:0] TARGET_DATA;     //        Data    to be written on the SPI bus

    reg [DATAWIDTH-1:0] read_data;

    integer i, j, k;

    begin
      // Read Command Bit
      //
      wait(A2F_HRESET == 0);

      @(posedge A2F_HCLK) #STD_CLK_DLY;

      // Issue Diagnostic Messages
      //
      ahb_bfm_msg1 = "AHB Single Write";
      ahb_bfm_msg2 = "Address Phase";
      ahb_bfm_msg3 = "SEQ";

      A2F_HADDRS = TARGET_ADDRESS;  // Transfer Address

      // Define the Transfer Request
      //
      // Transfer decode of: A2F_HTRANS[1]  A2F_HTRANS[0]  Description
      //                     -------------  -------------  ------------------------------------
      //                          0             0            IDLE               (No Transfer)
      //                          0             1            BUSY               (No Transfer)
      //                          1             0            NONSEQ             (Do Transfer)
      //                          1             1            SEQ                (Do Transfer)
      //
      // Transfer decode of: A2F_HREADYS                   Description
      //                     -----------                   ------------------------------------
      //                          0                          Slave is not ready (No Transfer)
      //                          1                          Slave is     ready (Do Transfer)
      //
      A2F_HSEL = 1'b1;     // Bridge selected
      A2F_HREADYS = 1'b1;  // Slave is ready
      A2F_HTRANSS = 2'h2;  // "NONSEQ" State

      //
      // Define "Transfer Size Encoding" is based on the following:
      //
      //       HSIZE[2]  HSIZE[1]  HSIZE[0]  Bits  Description
      //       --------  --------  --------  ----  -----------
      //          0         0         0         8  Byte
      //          0         0         1        16  Halfword
      //          0         1         0        32  Word
      //          0         1         1        64  Doublword
      //          1         0         0       128  4-word line
      //          1         0         1       256  8-word line
      //          1         1         0       512  -
      //          1         1         1      1024  -
      //
      //       The fabric design only supports up to 32 bits at a time.
      //
      A2F_HSIZES = 3'b010;  // Transfer Size

      A2F_HWRITES = 1'b1;  // "Write"  operation
      A2F_HWDATAS = {(DATAWIDTH) {1'b0}};  // Write Data Value of "0"

      //
      // Wait for next clock to sampe the slave's response
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      ahb_bfm_msg2 = "Data Phase";
      ahb_bfm_msg3 = "IDLE";
      ahb_bfm_msg4 = "Waiting for Slave";

      // Set the next transfer cycle to "IDLE"
      A2F_HADDRS = DEFAULT_AHB_ADDRESS;  // Default Address
      A2F_HSEL = 1'b0;     // Bridge not selected
      A2F_HTRANSS = 2'h0;  // "IDLE" State
      A2F_HSIZES = 3'h0;   // "Byte" Transfer Size
      A2F_HWDATAS = TARGET_DATA;  // Write From test routine
      A2F_HWRITES = 1'b0;  // "Read" operation

      //
      // Check if the slave has returend data
      //
      while (A2F_HREADYOUTS == 1'b0) begin
        @(posedge A2F_HCLK) #STD_CLK_DLY;
      end

      A2F_HREADYS = 1'b0;  // Slave is not ready
      TARGET_DATA = A2F_HRDATAS;  // Read slave data value

      // Clear Diagnostic Messages
      //
      ahb_bfm_msg1 <= "NO ACTIVITY";
      ahb_bfm_msg2 <= "NO ACTIVITY";
      ahb_bfm_msg3 <= "NO ACTIVITY";
      ahb_bfm_msg4 <= "NO ACTIVITY";
      ahb_bfm_msg5 <= "NO ACTIVITY";
      ahb_bfm_msg6 <= "NO ACTIVITY";

      //$stop();

    end
  endtask

  task ahb_write_al4s3b_fabric_mod;
    input [ADDRWIDTH-1:0] TARGET_ADDRESS;   //        Address to be written on the SPI bus
    input           [2:0] TARGET_XFR_SIZE;  //        Transfer Size for AHB bus
    input [DATAWIDTH-1:0] TARGET_DATA;      //        Data to be written on the SPI bus

    reg [DATAWIDTH-1:0] read_data;

    integer i, j, k;

    begin
      // Read Command Bit
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      // Issue Diagnostic Messages
      //
      ahb_bfm_msg1 = "AHB Single Write";
      ahb_bfm_msg2 = "Address Phase";
      ahb_bfm_msg3 = "SEQ";

      //A2F_HADDRS    =  TARGET_ADDRESS;       // Transfer Address
      A2F_HADDRS = {
        TARGET_ADDRESS[ADDRWIDTH-1:11], (TARGET_ADDRESS[10:0] << 2)
      };  // Transfer Address

      // Define the Transfer Request
      //
      // Transfer decode of: A2F_HTRANS[1]  A2F_HTRANS[0]  Description
      //                     -------------  -------------  ------------------------------------
      //                          0             0            IDLE               (No Transfer)
      //                          0             1            BUSY               (No Transfer)
      //                          1             0            NONSEQ             (Do Transfer)
      //                          1             1            SEQ                (Do Transfer)
      //
      // Transfer decode of: A2F_HREADYS                   Description
      //                     -----------                   ------------------------------------
      //                          0                          Slave is not ready (No Transfer)
      //                          1                          Slave is     ready (Do Transfer)
      //
      A2F_HSEL = 1'b1;     // Bridge selected
      A2F_HREADYS = 1'b1;  // Slave is ready
      A2F_HTRANSS = 2'h2;  // "NONSEQ" State

      //
      // Define "Transfer Size Encoding" is based on the following:
      //
      //       HSIZE[2]  HSIZE[1]  HSIZE[0]  Bits  Description
      //       --------  --------  --------  ----  -----------
      //          0         0         0         8  Byte
      //          0         0         1        16  Halfword
      //          0         1         0        32  Word
      //          0         1         1        64  Doublword
      //          1         0         0       128  4-word line
      //          1         0         1       256  8-word line
      //          1         1         0       512  -
      //          1         1         1      1024  -
      //
      //       The fabric design only supports up to 32 bits at a time.
      //
      A2F_HSIZES = TARGET_XFR_SIZE;  // Transfer Size

      A2F_HWRITES = 1'b1;  // "Write" operation
      A2F_HWDATAS = {(DATAWIDTH) {1'b0}};  // Write Data Value of "0"

      //
      // Wait for next clock to sampe the slave's response
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      ahb_bfm_msg2 = "Data Phase";
      ahb_bfm_msg3 = "IDLE";
      ahb_bfm_msg4 = "Waiting for Slave";

      // Set the next transfer cycle to "IDLE"
      A2F_HADDRS = DEFAULT_AHB_ADDRESS;  // Default Address
      A2F_HSEL = 1'b0;     // Bridge not selected
      A2F_HTRANSS = 2'h0;  // "IDLE" State
      A2F_HSIZES = 3'h0;   // "Byte" Transfer Size
      A2F_HWDATAS = TARGET_DATA;  // Write From test routine
      A2F_HWRITES = 1'b0;  // "Read" operation

      //
      // Check if the slave has returend data
      //
      while (A2F_HREADYOUTS == 1'b0) begin
        @(posedge A2F_HCLK) #STD_CLK_DLY;
      end

      A2F_HREADYS = 1'b0;  // Slave is not ready
      TARGET_DATA = A2F_HRDATAS;  // Read slave data value

      // Clear Diagnostic Messages
      //
      ahb_bfm_msg1 <= "NO ACTIVITY";
      ahb_bfm_msg2 <= "NO ACTIVITY";
      ahb_bfm_msg3 <= "NO ACTIVITY";
      ahb_bfm_msg4 <= "NO ACTIVITY";
      ahb_bfm_msg5 <= "NO ACTIVITY";
      ahb_bfm_msg6 <= "NO ACTIVITY";

    end
  endtask


  task ahb_read_al4s3b_fabric_mod;
    input  [ADDRWIDTH-1:0] TARGET_ADDRESS;   //        Address to be written on the SPI bus
    input            [2:0] TARGET_XFR_SIZE;  //        Transfer Size for AHB bus
    output [DATAWIDTH-1:0] TARGET_DATA;      //        Data to be written on the SPI bus

    reg [DATAWIDTH-1:0] read_data;

    integer i, j, k;

    begin
      // Read Command Bit
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      // Issue Diagnostic Messages
      //
      ahb_bfm_msg1 = "AHB Single Read";
      ahb_bfm_msg2 = "Address Phase";
      ahb_bfm_msg3 = "SEQ";

      //A2F_HADDRS    =  TARGET_ADDRESS;       // Transfer Address
      A2F_HADDRS = {
        TARGET_ADDRESS[ADDRWIDTH-1:11], (TARGET_ADDRESS[10:0] << 2)
      };  // Transfer Address

      // Define the Transfer Request
      //
      // Transfer decode of: A2F_HTRANS[1]  A2F_HTRANS[0]  Description
      //                     -------------  -------------  ------------------------------------
      //                          0             0            IDLE               (No Transfer)
      //                          0             1            BUSY               (No Transfer)
      //                          1             0            NONSEQ             (Do Transfer)
      //                          1             1            SEQ                (Do Transfer)
      //
      // Transfer decode of: A2F_HREADYS                   Description
      //                     -----------                   ------------------------------------
      //                          0                          Slave is not ready (No Transfer)
      //                          1                          Slave is     ready (Do Transfer)
      //
      A2F_HSEL = 1'b1;     // Bridge selected
      A2F_HREADYS = 1'b1;  // Slave is ready
      A2F_HTRANSS = 2'h2;  // "NONSEQ" State

      //
      // Define "Transfer Size Encoding" is based on the following:
      //
      //       HSIZE[2]  HSIZE[1]  HSIZE[0]  Bits  Description
      //       --------  --------  --------  ----  -----------
      //          0         0         0         8  Byte
      //          0         0         1        16  Halfword
      //          0         1         0        32  Word
      //          0         1         1        64  Doublword
      //          1         0         0       128  4-word line
      //          1         0         1       256  8-word line
      //          1         1         0       512  -
      //          1         1         1      1024  -
      //
      //       The fabric design only supports up to 32 bits at a time.
      //
      A2F_HSIZES = TARGET_XFR_SIZE;  // Transfer Size

      A2F_HWRITES = 1'b0;  // "Read"  operation
      A2F_HWDATAS = {(DATAWIDTH) {1'b0}};  // Write Data Value of "0"

      //
      // Wait for next clock to sampe the slave's response
      //
      @(posedge A2F_HCLK) #STD_CLK_DLY;

      ahb_bfm_msg2 = "Data Phase";
      ahb_bfm_msg3 = "IDLE";
      ahb_bfm_msg4 = "Waiting for Slave";

      // Set the next transfer cycle to "IDLE"
      A2F_HADDRS = DEFAULT_AHB_ADDRESS;  // Default Address
      A2F_HSEL = 1'b0;     // Bridge not selected
      A2F_HTRANSS = 2'h0;  // "IDLE" State
      A2F_HSIZES = 3'h0;   // "Byte" Transfer Size

      //
      // Check if the slave has returend data
      //
      while (A2F_HREADYOUTS == 1'b0) begin
        @(posedge A2F_HCLK) #STD_CLK_DLY;
      end

      A2F_HREADYS = 1'b0;  // Slave is not ready
      TARGET_DATA = A2F_HRDATAS;  // Read slave data value

      // Clear Diagnostic Messages
      //
      ahb_bfm_msg1 <= "NO ACTIVITY";
      ahb_bfm_msg2 <= "NO ACTIVITY";
      ahb_bfm_msg3 <= "NO ACTIVITY";
      ahb_bfm_msg4 <= "NO ACTIVITY";
      ahb_bfm_msg5 <= "NO ACTIVITY";
      ahb_bfm_msg6 <= "NO ACTIVITY";

    end
  endtask
`endif

endmodule

`timescale 1ns / 10ps

module oscillator_s1 (

  OSC_CLK_EN,
  OSC_CLK

);

  // Define the oscillator's frequency
  //
  // Note: The parameter above assumes that values are calculated in units of nS.
  //
  parameter T_CYCLE_CLK = (1000.0 / 19.2);

  input OSC_CLK_EN;
  output OSC_CLK;

  wire OSC_CLK_EN;
  wire OSC_CLK;

  reg osc_int_clk;

  // Define the output enable
  //
  assign OSC_CLK = OSC_CLK_EN ? osc_int_clk : 1'bZ;

  // Define the clock oscillator section
  //
  initial begin
    osc_int_clk = 0;  // Intialize the clock at time 0ns.
`ifndef YOSYS
    forever  // Generate a clock with an expected frequency.
    begin
      #(T_CYCLE_CLK / 2) osc_int_clk = 1;
      #(T_CYCLE_CLK / 2) osc_int_clk = 0;
    end
`endif
  end

endmodule

`timescale 1ns / 10ps

module sdma_bfm (

  // SDMA Interface Signals
  //
  sdma_req_i,
  sdma_sreq_i,
  sdma_done_o,
  sdma_active_o

);

  input [3:0] sdma_req_i;
  input [3:0] sdma_sreq_i;
  output [3:0] sdma_done_o;
  output [3:0] sdma_active_o;

  reg [3:0] sdma_done_sig;
  reg [3:0] sdma_active_sig;

  assign sdma_done_o = sdma_done_sig;
  assign sdma_active_o = sdma_active_sig;

  initial begin
    sdma_done_sig <= 4'h0;
    sdma_active_sig <= 4'h0;

  end

`ifndef YOSYS
  task drive_dma_active;
    input [3:0] dma_active_i;
    begin
      sdma_active_sig <= dma_active_i;
      #100;
      //sdma_active_sig <= 4'h0;

    end
  endtask
`endif
endmodule

`timescale 1ns / 10ps
module ahb2fb_asynbrig_if (

  A2F_HCLK,  // clock
  A2F_HRESET,  // reset

  // AHB connection to master
  //
  A2F_HSEL,
  A2F_HADDRS,
  A2F_HTRANSS,
  A2F_HSIZES,
  A2F_HWRITES,
  A2F_HREADYS,

  A2F_HREADYOUTS,
  A2F_HRESPS,

  // Fabric Interface
  //
  AHB_ASYNC_ADDR_O,
  AHB_ASYNC_READ_EN_O,
  AHB_ASYNC_WRITE_EN_O,
  AHB_ASYNC_BYTE_STROBE_O,

  AHB_ASYNC_STB_TOGGLE_O,

  FABRIC_ASYNC_ACK_TOGGLE_I

);


  //-----Port Parameters-----------------
  //

  parameter DATAWIDTH = 32;
  parameter APERWIDTH = 17;

  parameter STATE_WIDTH = 1;

  parameter AHB_ASYNC_IDLE = 0;
  parameter AHB_ASYNC_WAIT = 1;


  //-----Port Signals--------------------
  //


  //------------------------------------------
  // AHB connection to master
  //
  input A2F_HCLK;  // clock
  input A2F_HRESET;  // reset

  input [APERWIDTH-1:0] A2F_HADDRS;
  input A2F_HSEL;
  input [1:0] A2F_HTRANSS;
  input [2:0] A2F_HSIZES;
  input A2F_HWRITES;
  input A2F_HREADYS;

  output A2F_HREADYOUTS;
  output A2F_HRESPS;


  //------------------------------------------
  // Fabric Interface
  //
  output [APERWIDTH-1:0] AHB_ASYNC_ADDR_O;
  output AHB_ASYNC_READ_EN_O;
  output AHB_ASYNC_WRITE_EN_O;
  output [3:0] AHB_ASYNC_BYTE_STROBE_O;

  output AHB_ASYNC_STB_TOGGLE_O;

  input FABRIC_ASYNC_ACK_TOGGLE_I;


  //------------------------------------------
  // AHB connection to master
  //
  wire A2F_HCLK;  // clock
  wire A2F_HRESET;  // reset

  wire [APERWIDTH-1:0] A2F_HADDRS;
  wire A2F_HSEL;
  wire [1:0] A2F_HTRANSS;
  wire [2:0] A2F_HSIZES;
  wire A2F_HWRITES;
  wire A2F_HREADYS;

  reg A2F_HREADYOUTS;
  reg A2F_HREADYOUTS_nxt;

  wire A2F_HRESPS;


  //------------------------------------------
  // Fabric Interface
  //
  reg [APERWIDTH-1:0] AHB_ASYNC_ADDR_O;
  reg AHB_ASYNC_READ_EN_O;
  reg AHB_ASYNC_WRITE_EN_O;

  reg [3:0] AHB_ASYNC_BYTE_STROBE_O;
  reg [3:0] AHB_ASYNC_BYTE_STROBE_O_nxt;



  reg AHB_ASYNC_STB_TOGGLE_O;
  reg AHB_ASYNC_STB_TOGGLE_O_nxt;

  wire FABRIC_ASYNC_ACK_TOGGLE_I;


  //------Define Parameters---------
  //

  //
  // None at this time
  //


  //-----Internal Signals--------------------
  //

  wire trans_req;  // transfer request

  reg [STATE_WIDTH-1:0] ahb_to_fabric_state;
  reg [STATE_WIDTH-1:0] ahb_to_fabric_state_nxt;

  reg fabric_async_ack_toggle_i_1ff;
  reg fabric_async_ack_toggle_i_2ff;
  reg fabric_async_ack_toggle_i_3ff;

  wire fabric_async_ack;

  //------Logic Operations----------
  //


  // Define the Transfer Request
  //
  // Transfer decode of: A2F_HTRANS[1]  A2F_HTRANS[0]  Description
  //                     -------------  -------------  ------------------------------------
  //                          0             0            IDLE               (No Transfer)
  //                          0             1            BUSY               (No Transfer)
  //                          1             0            NONSEQ             (Do Transfer)
  //                          1             1            SEQ                (Do Transfer)
  //
  // Transfer decode of: A2F_HREADYS                   Description
  //                     -----------                   ------------------------------------
  //                          0                          Slave is not ready (No Transfer)
  //                          1                          Slave is     ready (Do Transfer)
  //
  assign trans_req = A2F_HSEL & A2F_HREADYS & A2F_HTRANSS[1]; // transfer request issued only in SEQ and NONSEQ status and slave is
  // selected and last transfer finish


  // Check for acknowldge from the fabric
  //
  // Note: The fabric is on a different and potentially asynchronous clock.
  //       Therefore, acknowledge is passed as a toggle signal.
  //
  assign fabric_async_ack = fabric_async_ack_toggle_i_2ff ^ fabric_async_ack_toggle_i_3ff;


  // Issue transfer status
  //
  // Note: All transfers are considered to have completed successfully.
  //
  assign A2F_HRESPS = 1'b0;  // OKAY response from slave


  // Address signal registering, to make the address and data active at the same cycle
  //
  always @(posedge A2F_HCLK or posedge A2F_HRESET) begin
    if (A2F_HRESET) begin
      ahb_to_fabric_state <= AHB_ASYNC_IDLE;

      AHB_ASYNC_ADDR_O <= {(APERWIDTH) {1'b0}};  //default address 0 is selected
      AHB_ASYNC_READ_EN_O <= 1'b0;
      AHB_ASYNC_WRITE_EN_O <= 1'b0;
      AHB_ASYNC_BYTE_STROBE_O <= 4'b0;

      AHB_ASYNC_STB_TOGGLE_O <= 1'b0;

      fabric_async_ack_toggle_i_1ff <= 1'b0;
      fabric_async_ack_toggle_i_2ff <= 1'b0;
      fabric_async_ack_toggle_i_3ff <= 1'b0;

      A2F_HREADYOUTS <= 1'b0;
    end else begin
      ahb_to_fabric_state <= ahb_to_fabric_state_nxt;

      if (trans_req) begin
        AHB_ASYNC_ADDR_O <= A2F_HADDRS[APERWIDTH-1:0];
        AHB_ASYNC_READ_EN_O <= ~A2F_HWRITES;
        AHB_ASYNC_WRITE_EN_O <= A2F_HWRITES;
        AHB_ASYNC_BYTE_STROBE_O <= AHB_ASYNC_BYTE_STROBE_O_nxt;
      end

      AHB_ASYNC_STB_TOGGLE_O <= AHB_ASYNC_STB_TOGGLE_O_nxt;

      fabric_async_ack_toggle_i_1ff <= FABRIC_ASYNC_ACK_TOGGLE_I;
      fabric_async_ack_toggle_i_2ff <= fabric_async_ack_toggle_i_1ff;
      fabric_async_ack_toggle_i_3ff <= fabric_async_ack_toggle_i_2ff;

      A2F_HREADYOUTS <= A2F_HREADYOUTS_nxt;
    end
  end


  // Byte Strobe Signal Decode
  //
  // Note: The "Transfer Size Encoding" is defined as follows:
  //
  //       HSIZE[2]  HSIZE[1]  HSIZE[0]  Bits  Description
  //       --------  --------  --------  ----  -----------
  //          0         0         0         8  Byte
  //          0         0         1        16  Halfword
  //          0         1         0        32  Word
  //          0         1         1        64  Doublword
  //          1         0         0       128  4-word line
  //          1         0         1       256  8-word line
  //          1         1         0       512  -
  //          1         1         1      1024  -
  //
  //       The fabric design only supports up to 32 bits at a time.
  //
  always @(A2F_HSIZES or A2F_HADDRS) begin
    case (A2F_HSIZES)
      3'b000:                                  //byte
        begin
        case (A2F_HADDRS[1:0])
          2'b00: AHB_ASYNC_BYTE_STROBE_O_nxt <= 4'b0001;
          2'b01: AHB_ASYNC_BYTE_STROBE_O_nxt <= 4'b0010;
          2'b10: AHB_ASYNC_BYTE_STROBE_O_nxt <= 4'b0100;
          2'b11: AHB_ASYNC_BYTE_STROBE_O_nxt <= 4'b1000;
          default: AHB_ASYNC_BYTE_STROBE_O_nxt <= 4'b0000;
        endcase
      end
      3'b001:                                  //half word
        begin
        case (A2F_HADDRS[1])
          1'b0: AHB_ASYNC_BYTE_STROBE_O_nxt <= 4'b0011;
          1'b1: AHB_ASYNC_BYTE_STROBE_O_nxt <= 4'b1100;
          default: AHB_ASYNC_BYTE_STROBE_O_nxt <= 4'b0000;
        endcase
      end
      default: AHB_ASYNC_BYTE_STROBE_O_nxt <= 4'b1111;  // default 32 bits, word
    endcase
  end


  // Define the AHB Interface Statemachine
  //
  always @(trans_req or fabric_async_ack or AHB_ASYNC_STB_TOGGLE_O or ahb_to_fabric_state) begin
    case (ahb_to_fabric_state)
      AHB_ASYNC_IDLE: begin
        case (trans_req)
          1'b0:  // Wait for an AHB Transfer
            begin
            ahb_to_fabric_state_nxt <= AHB_ASYNC_IDLE;
            A2F_HREADYOUTS_nxt <= 1'b1;
            AHB_ASYNC_STB_TOGGLE_O_nxt <= AHB_ASYNC_STB_TOGGLE_O;
          end
          1'b1:  // AHB Transfer Detected
            begin
            ahb_to_fabric_state_nxt <= AHB_ASYNC_WAIT;
            A2F_HREADYOUTS_nxt <= 1'b0;
            AHB_ASYNC_STB_TOGGLE_O_nxt <= ~AHB_ASYNC_STB_TOGGLE_O;
          end
        endcase
      end
      AHB_ASYNC_WAIT: begin
        AHB_ASYNC_STB_TOGGLE_O_nxt <= AHB_ASYNC_STB_TOGGLE_O;

        case (fabric_async_ack)
          1'b0:  // Wait for Acknowledge from Fabric Interface
            begin
            ahb_to_fabric_state_nxt <= AHB_ASYNC_WAIT;
            A2F_HREADYOUTS_nxt <= 1'b0;
          end
          1'b1:  // Received Acknowledge from Fabric Interface
            begin
            ahb_to_fabric_state_nxt <= AHB_ASYNC_IDLE;
            A2F_HREADYOUTS_nxt <= 1'b1;
          end
        endcase
      end
      default: begin
        ahb_to_fabric_state_nxt <= AHB_ASYNC_IDLE;
        A2F_HREADYOUTS_nxt <= 1'b0;
        AHB_ASYNC_STB_TOGGLE_O_nxt <= AHB_ASYNC_STB_TOGGLE_O;
      end
    endcase
  end

endmodule

`timescale 1ns / 10ps

module fb2ahb_asynbrig_if (

  A2F_HRDATAS,

  // AHB Interface
  //
  AHB_ASYNC_READ_EN_I,
  AHB_ASYNC_WRITE_EN_I,
  AHB_ASYNC_BYTE_STROBE_I,

  AHB_ASYNC_STB_TOGGLE_I,

  // Fabric Interface
  //
  WB_CLK_I,
  WB_RST_I,
  WB_ACK_I,
  WB_DAT_I,

  WB_CYC_O,
  WB_BYTE_STB_O,
  WB_WE_O,
  WB_RD_O,
  WB_STB_O,

  FABRIC_ASYNC_ACK_TOGGLE_O

);


  //-----Port Parameters-----------------
  //

  parameter DATAWIDTH = 32;

  parameter STATE_WIDTH = 1;

  parameter FAB_ASYNC_IDLE = 0;
  parameter FAB_ASYNC_WAIT = 1;


  //-----Port Signals--------------------
  //


  //------------------------------------------
  // AHB connection to master
  //
  output [DATAWIDTH-1:0] A2F_HRDATAS;


  //------------------------------------------
  // Fabric Interface
  //
  input AHB_ASYNC_READ_EN_I;
  input AHB_ASYNC_WRITE_EN_I;
  input [3:0] AHB_ASYNC_BYTE_STROBE_I;

  input AHB_ASYNC_STB_TOGGLE_I;


  input WB_CLK_I;
  input WB_RST_I;
  input WB_ACK_I;
  input [DATAWIDTH-1:0] WB_DAT_I;

  output WB_CYC_O;
  output [3:0] WB_BYTE_STB_O;
  output WB_WE_O;
  output WB_RD_O;
  output WB_STB_O;

  output FABRIC_ASYNC_ACK_TOGGLE_O;


  //------------------------------------------
  // AHB connection to master
  //

  reg [DATAWIDTH-1:0] A2F_HRDATAS;
  reg [DATAWIDTH-1:0] A2F_HRDATAS_nxt;


  //------------------------------------------
  // Fabric Interface
  //
  wire AHB_ASYNC_READ_EN_I;
  wire AHB_ASYNC_WRITE_EN_I;

  wire [3:0] AHB_ASYNC_BYTE_STROBE_I;

  wire AHB_ASYNC_STB_TOGGLE_I;


  wire WB_CLK_I;
  wire WB_RST_I;
  wire WB_ACK_I;

  reg WB_CYC_O;
  reg WB_CYC_O_nxt;

  reg [3:0] WB_BYTE_STB_O;
  reg [3:0] WB_BYTE_STB_O_nxt;

  reg WB_WE_O;
  reg WB_WE_O_nxt;

  reg WB_RD_O;
  reg WB_RD_O_nxt;

  reg WB_STB_O;
  reg WB_STB_O_nxt;

  reg FABRIC_ASYNC_ACK_TOGGLE_O;
  reg FABRIC_ASYNC_ACK_TOGGLE_O_nxt;


  //------Define Parameters---------
  //

  //
  // None at this time
  //


  //-----Internal Signals--------------------
  //

  reg [STATE_WIDTH-1:0] fabric_to_ahb_state;
  reg [STATE_WIDTH-1:0] fabric_to_ahb_state_nxt;

  reg ahb_async_stb_toggle_i_1ff;
  reg ahb_async_stb_toggle_i_2ff;
  reg ahb_async_stb_toggle_i_3ff;

  wire ahb_async_stb;


  //------Logic Operations----------
  //


  // Check for transfer from the AHB
  //
  // Note: The AHB is on a different and potentially asynchronous clock.
  //       Therefore, strobe is passed as a toggle signal.
  //
  assign ahb_async_stb = ahb_async_stb_toggle_i_2ff ^ ahb_async_stb_toggle_i_3ff;


  // Address signal registering, to make the address and data active at the same cycle
  //
  always @(posedge WB_CLK_I or posedge WB_RST_I) begin
    if (WB_RST_I) begin
      fabric_to_ahb_state <= FAB_ASYNC_IDLE;

      A2F_HRDATAS <= {(DATAWIDTH) {1'b0}};

      WB_CYC_O <= 1'b0;
      WB_BYTE_STB_O <= 4'b0;
      WB_WE_O <= 1'b0;
      WB_RD_O <= 1'b0;
      WB_STB_O <= 1'b0;

      FABRIC_ASYNC_ACK_TOGGLE_O <= 1'b0;

      ahb_async_stb_toggle_i_1ff <= 1'b0;
      ahb_async_stb_toggle_i_2ff <= 1'b0;
      ahb_async_stb_toggle_i_3ff <= 1'b0;

    end else begin

      fabric_to_ahb_state <= fabric_to_ahb_state_nxt;

      A2F_HRDATAS <= A2F_HRDATAS_nxt;

      WB_CYC_O <= WB_CYC_O_nxt;
      WB_BYTE_STB_O <= WB_BYTE_STB_O_nxt;
      WB_WE_O <= WB_WE_O_nxt;
      WB_RD_O <= WB_RD_O_nxt;
      WB_STB_O <= WB_STB_O_nxt;

      FABRIC_ASYNC_ACK_TOGGLE_O <= FABRIC_ASYNC_ACK_TOGGLE_O_nxt;

      ahb_async_stb_toggle_i_1ff <= AHB_ASYNC_STB_TOGGLE_I;
      ahb_async_stb_toggle_i_2ff <= ahb_async_stb_toggle_i_1ff;
      ahb_async_stb_toggle_i_3ff <= ahb_async_stb_toggle_i_2ff;

    end
  end


  // Define the Fabric Interface Statemachine
  //
  always @(
            ahb_async_stb             or
            AHB_ASYNC_READ_EN_I       or
            AHB_ASYNC_WRITE_EN_I      or
            AHB_ASYNC_BYTE_STROBE_I   or
            A2F_HRDATAS               or
            WB_ACK_I                  or
            WB_DAT_I                  or
            WB_CYC_O                  or
            WB_BYTE_STB_O             or
            WB_WE_O                   or
            WB_RD_O                   or
            WB_STB_O                  or
            FABRIC_ASYNC_ACK_TOGGLE_O or
            fabric_to_ahb_state
    )
    begin
    case (fabric_to_ahb_state)
      FAB_ASYNC_IDLE: begin
        FABRIC_ASYNC_ACK_TOGGLE_O_nxt <= FABRIC_ASYNC_ACK_TOGGLE_O;
        A2F_HRDATAS_nxt <= A2F_HRDATAS;

        case (ahb_async_stb)
          1'b0:  // Wait for an AHB Transfer
            begin
            fabric_to_ahb_state_nxt <= FAB_ASYNC_IDLE;

            WB_CYC_O_nxt <= 1'b0;
            WB_BYTE_STB_O_nxt <= 4'b0;
            WB_WE_O_nxt <= 1'b0;
            WB_RD_O_nxt <= 1'b0;
            WB_STB_O_nxt <= 1'b0;

          end
          1'b1:  // AHB Transfer Detected
            begin
            fabric_to_ahb_state_nxt <= FAB_ASYNC_WAIT;

            WB_CYC_O_nxt <= 1'b1;
            WB_BYTE_STB_O_nxt <= AHB_ASYNC_BYTE_STROBE_I;
            WB_WE_O_nxt <= AHB_ASYNC_WRITE_EN_I;
            WB_RD_O_nxt <= AHB_ASYNC_READ_EN_I;
            WB_STB_O_nxt <= 1'b1;

          end
        endcase
      end
      FAB_ASYNC_WAIT: begin

        case (WB_ACK_I)
          1'b0:  // Wait for Acknowledge from Fabric Interface
            begin
            fabric_to_ahb_state_nxt <= FAB_ASYNC_WAIT;

            A2F_HRDATAS_nxt <= A2F_HRDATAS;

            WB_CYC_O_nxt <= WB_CYC_O;
            WB_BYTE_STB_O_nxt <= WB_BYTE_STB_O;
            WB_WE_O_nxt <= WB_WE_O;
            WB_RD_O_nxt <= WB_RD_O;
            WB_STB_O_nxt <= WB_STB_O;

            FABRIC_ASYNC_ACK_TOGGLE_O_nxt <= FABRIC_ASYNC_ACK_TOGGLE_O;
          end
          1'b1:  // Received Acknowledge from Fabric Interface
            begin
            fabric_to_ahb_state_nxt <= FAB_ASYNC_IDLE;

            A2F_HRDATAS_nxt <= WB_DAT_I;

            WB_CYC_O_nxt <= 1'b0;
            WB_BYTE_STB_O_nxt <= 4'b0;
            WB_WE_O_nxt <= 1'b0;
            WB_RD_O_nxt <= 1'b0;
            WB_STB_O_nxt <= 1'b0;

            FABRIC_ASYNC_ACK_TOGGLE_O_nxt <= ~FABRIC_ASYNC_ACK_TOGGLE_O;
          end
        endcase
      end
      default: begin
        fabric_to_ahb_state_nxt <= FAB_ASYNC_IDLE;

        A2F_HRDATAS_nxt <= A2F_HRDATAS;

        WB_CYC_O_nxt <= 1'b0;
        WB_BYTE_STB_O_nxt <= 4'b0;
        WB_WE_O_nxt <= 1'b0;
        WB_RD_O_nxt <= 1'b0;
        WB_STB_O_nxt <= 1'b0;

        FABRIC_ASYNC_ACK_TOGGLE_O_nxt <= FABRIC_ASYNC_ACK_TOGGLE_O;
      end
    endcase
  end

endmodule

`timescale 1ns / 10ps

module ahb2fb_asynbrig (

  // AHB Slave Interface to AHB Bus Matrix
  //
  A2F_HCLK,
  A2F_HRESET,

  A2F_HADDRS,
  A2F_HSEL,
  A2F_HTRANSS,
  A2F_HSIZES,
  A2F_HWRITES,
  A2F_HREADYS,
  A2F_HWDATAS,

  A2F_HREADYOUTS,
  A2F_HRESPS,
  A2F_HRDATAS,

  // Fabric Wishbone Bus
  //
  WB_CLK_I,
  WB_RST_I,
  WB_DAT_I,
  WB_ACK_I,

  WB_ADR_O,
  WB_CYC_O,
  WB_BYTE_STB_O,
  WB_WE_O,
  WB_RD_O,
  WB_STB_O,
  WB_DAT_O

);


  //-----Port Parameters-----------------
  //

  parameter ADDRWIDTH = 32;
  parameter DATAWIDTH = 32;
  parameter APERWIDTH = 17;


  //-----Port Signals--------------------
  //

  input A2F_HCLK;  // Clock
  input A2F_HRESET;  // Reset

  // AHB connection to master
  //
  input [ADDRWIDTH-1:0] A2F_HADDRS;
  input A2F_HSEL;
  input [1:0] A2F_HTRANSS;
  input [2:0] A2F_HSIZES;
  input A2F_HWRITES;
  input A2F_HREADYS;
  input [DATAWIDTH-1:0] A2F_HWDATAS;

  output A2F_HREADYOUTS;
  output A2F_HRESPS;
  output [DATAWIDTH-1:0] A2F_HRDATAS;

  // Wishbone connection to Fabric IP
  //
  input WB_CLK_I;                   // Fabric Clock Input         from Fabric
  input WB_RST_I;                   // Fabric Reset Input         from Fabric
  input [DATAWIDTH-1:0] WB_DAT_I;   // Read Data Bus              from Fabric
  input WB_ACK_I;                   // Transfer Cycle Acknowledge from Fabric

  output [APERWIDTH-1:0] WB_ADR_O;  // Address Bus                to   Fabric
  output WB_CYC_O;                  // Cycle Chip Select          to   Fabric
  output [3:0] WB_BYTE_STB_O;       // Byte Select                to   Fabric
  output WB_WE_O;                   // Write Enable               to   Fabric
  output WB_RD_O;                   // Read  Enable               to   Fabric
  output WB_STB_O;                  // Strobe Signal              to   Fabric
  output [DATAWIDTH-1:0] WB_DAT_O;  // Write Data Bus             to   Fabric


  wire A2F_HCLK;  // Clock
  wire A2F_HRESET;  // Reset

  // AHB connection to master
  //
  wire [ADDRWIDTH-1:0] A2F_HADDRS;
  wire A2F_HSEL;
  wire [1:0] A2F_HTRANSS;
  wire [2:0] A2F_HSIZES;
  wire A2F_HWRITES;
  wire A2F_HREADYS;
  wire [DATAWIDTH-1:0] A2F_HWDATAS;

  wire A2F_HREADYOUTS;
  wire A2F_HRESPS;
  wire [DATAWIDTH-1:0] A2F_HRDATAS;


  // Wishbone connection to Fabric IP
  //
  wire WB_CLK_I;                  // Fabric Clock Input         from Fabric
  wire WB_RST_I;                  // Fabric Reset Input         from Fabric
  wire [DATAWIDTH-1:0] WB_DAT_I;  // Read Data Bus              from Fabric
  wire WB_ACK_I;                  // Transfer Cycle Acknowledge from Fabric

  wire [APERWIDTH-1:0] WB_ADR_O;  // Address Bus (128KB)        to   Fabric
  wire WB_CYC_O;                  // Cycle Chip Select          to   Fabric
  wire [3:0] WB_BYTE_STB_O;       // Byte Select                to   Fabric
  wire WB_WE_O;                   // Write Enable               to   Fabric
  wire WB_RD_O;                   // Read  Enable               to   Fabric
  wire WB_STB_O;                  // Strobe Signal              to   Fabric
  wire [DATAWIDTH-1:0] WB_DAT_O;  // Write Data Bus             to   Fabric



  //------Define Parameters---------
  //

  //
  // None at this time
  //


  //-----Internal Signals--------------------
  //

  // Register module interface signals
  wire [APERWIDTH-1:0] ahb_async_addr;
  wire ahb_async_read_en;
  wire ahb_async_write_en;
  wire [3:0] ahb_async_byte_strobe;

  wire ahb_async_stb_toggle;

  wire fabric_async_ack_toggle;


  //------Logic Operations----------
  //

  // Define the data input from the AHB and output to the fabric
  //
  // Note: Due to the nature of the bus timing, there is no need to register
  //       this value locally.
  //
  assign WB_DAT_O = A2F_HWDATAS;

  // Define the Address bus output from the AHB and output to the fabric
  //
  // Note: Due to the nature of the bus timing, there is no need to register
  //       this value locally.
  //
  assign WB_ADR_O = ahb_async_addr;


  //------Instantiate Modules----------------
  //

  // Interface block to convert AHB transfers to simple read/write
  // controls.
  ahb2fb_asynbrig_if #(

    .DATAWIDTH(DATAWIDTH),
    .APERWIDTH(APERWIDTH)

  ) u_FFE_ahb_to_fabric_async_bridge_interface (
    .A2F_HCLK(A2F_HCLK),
    .A2F_HRESET(A2F_HRESET),

    // Input slave port: 32 bit data bus interface
    .A2F_HSEL(A2F_HSEL),
    .A2F_HADDRS(A2F_HADDRS[APERWIDTH-1:0]),
    .A2F_HTRANSS(A2F_HTRANSS),
    .A2F_HSIZES(A2F_HSIZES),
    .A2F_HWRITES(A2F_HWRITES),
    .A2F_HREADYS(A2F_HREADYS),

    .A2F_HREADYOUTS(A2F_HREADYOUTS),
    .A2F_HRESPS(A2F_HRESPS),

    // Register interface
    .AHB_ASYNC_ADDR_O(ahb_async_addr),
    .AHB_ASYNC_READ_EN_O(ahb_async_read_en),
    .AHB_ASYNC_WRITE_EN_O(ahb_async_write_en),
    .AHB_ASYNC_BYTE_STROBE_O(ahb_async_byte_strobe),
    .AHB_ASYNC_STB_TOGGLE_O(ahb_async_stb_toggle),

    .FABRIC_ASYNC_ACK_TOGGLE_I(fabric_async_ack_toggle)

  );


  fb2ahb_asynbrig_if

  u_FFE_fabric_to_ahb_async_bridge_interface (
    .A2F_HRDATAS(A2F_HRDATAS),

    .AHB_ASYNC_READ_EN_I(ahb_async_read_en),
    .AHB_ASYNC_WRITE_EN_I(ahb_async_write_en),
    .AHB_ASYNC_BYTE_STROBE_I(ahb_async_byte_strobe),
    .AHB_ASYNC_STB_TOGGLE_I(ahb_async_stb_toggle),

    .WB_CLK_I(WB_CLK_I),            // Fabric Clock Input         from Fabric
    .WB_RST_I(WB_RST_I),            // Fabric Reset Input         from Fabric
    .WB_ACK_I(WB_ACK_I),            // Transfer Cycle Acknowledge from Fabric
    .WB_DAT_I(WB_DAT_I),            // Data Bus Input             from Fabric

    .WB_CYC_O(WB_CYC_O),            // Cycle Chip Select          to   Fabric
    .WB_BYTE_STB_O(WB_BYTE_STB_O),  // Byte Select                to   Fabric
    .WB_WE_O(WB_WE_O),              // Write Enable               to   Fabric
    .WB_RD_O(WB_RD_O),              // Read  Enable               to   Fabric
    .WB_STB_O(WB_STB_O),            // Strobe Signal              to   Fabric

    .FABRIC_ASYNC_ACK_TOGGLE_O(fabric_async_ack_toggle)
  );
endmodule


`timescale 1ns / 10ps
module qlal4s3b_cell_macro_bfm (

  // AHB-To-Fabric Bridge
  //
  WBs_ADR,
  WBs_CYC,
  WBs_BYTE_STB,
  WBs_WE,
  WBs_RD,
  WBs_STB,
  WBs_WR_DAT,
  WB_CLK,
  WB_RST,
  WBs_RD_DAT,
  WBs_ACK,
  //
  // SDMA Signals
  //
  SDMA_Req,
  SDMA_Sreq,
  SDMA_Done,
  SDMA_Active,
  //
  // FB Interrupts
  //
  FB_msg_out,
  FB_Int_Clr,
  FB_Start,
  FB_Busy,
  //
  // FB Clocks
  //
  Sys_Clk0,
  Sys_Clk0_Rst,
  Sys_Clk1,
  Sys_Clk1_Rst,
  //
  // Packet FIFO
  //
  Sys_PKfb_Clk,
  Sys_PKfb_Rst,
  FB_PKfbData,
  FB_PKfbPush,
  FB_PKfbSOF,
  FB_PKfbEOF,
  FB_PKfbOverflow,
  //
  // Sensor Interface
  //
  Sensor_Int,
  TimeStamp,
  //
  // SPI Master APB Bus
  //
  Sys_Pclk,
  Sys_Pclk_Rst,
  Sys_PSel,
  SPIm_Paddr,
  SPIm_PEnable,
  SPIm_PWrite,
  SPIm_PWdata,
  SPIm_Prdata,
  SPIm_PReady,
  SPIm_PSlvErr,
  //
  // Misc
  //
  Device_ID,
  //
  // FBIO Signals
  //
  FBIO_In,
  FBIO_In_En,
  FBIO_Out,
  FBIO_Out_En,
  //
  // ???
  //
  SFBIO,
  Device_ID_6S,
  Device_ID_4S,
  SPIm_PWdata_26S,
  SPIm_PWdata_24S,
  SPIm_PWdata_14S,
  SPIm_PWdata_11S,
  SPIm_PWdata_0S,
  SPIm_Paddr_8S,
  SPIm_Paddr_6S,
  FB_PKfbPush_1S,
  FB_PKfbData_31S,
  FB_PKfbData_21S,
  FB_PKfbData_19S,
  FB_PKfbData_9S,
  FB_PKfbData_6S,
  Sys_PKfb_ClkS,
  FB_BusyS,
  WB_CLKS
);
  //------Port Parameters----------------
  //

  //
  // None at this time
  //

  //------Port Signals-------------------
  //

  //
  // AHB-To-Fabric Bridge
  //
  output [16:0] WBs_ADR;
  output WBs_CYC;
  output [3:0] WBs_BYTE_STB;
  output WBs_WE;
  output WBs_RD;
  output WBs_STB;
  output [31:0] WBs_WR_DAT;
  input WB_CLK;
  output WB_RST;
  input [31:0] WBs_RD_DAT;
  input WBs_ACK;
  //
  // SDMA Signals
  //
  input [3:0] SDMA_Req;
  input [3:0] SDMA_Sreq;
  output [3:0] SDMA_Done;
  output [3:0] SDMA_Active;
  //
  // FB Interrupts
  //
  input [3:0] FB_msg_out;
  input [7:0] FB_Int_Clr;
  output FB_Start;
  input FB_Busy;
  //
  // FB Clocks
  //
  output Sys_Clk0;
  output Sys_Clk0_Rst;
  output Sys_Clk1;
  output Sys_Clk1_Rst;
  //
  // Packet FIFO
  //
  input Sys_PKfb_Clk;
  output Sys_PKfb_Rst;
  input [31:0] FB_PKfbData;
  input [3:0] FB_PKfbPush;
  input FB_PKfbSOF;
  input FB_PKfbEOF;
  output FB_PKfbOverflow;
  //
  // Sensor Interface
  //
  output [7:0] Sensor_Int;
  output [23:0] TimeStamp;
  //
  // SPI Master APB Bus
  //
  output Sys_Pclk;
  output Sys_Pclk_Rst;
  input Sys_PSel;
  input [15:0] SPIm_Paddr;
  input SPIm_PEnable;
  input SPIm_PWrite;
  input [31:0] SPIm_PWdata;
  output [31:0] SPIm_Prdata;
  output SPIm_PReady;
  output SPIm_PSlvErr;
  //
  // Misc
  //
  input [15:0] Device_ID;
  //
  // FBIO Signals
  //
  output [13:0] FBIO_In;
  input [13:0] FBIO_In_En;
  input [13:0] FBIO_Out;
  input [13:0] FBIO_Out_En;
  //
  // ???
  //
  inout [13:0] SFBIO;
  input Device_ID_6S;
  input Device_ID_4S;
  input SPIm_PWdata_26S;
  input SPIm_PWdata_24S;
  input SPIm_PWdata_14S;
  input SPIm_PWdata_11S;
  input SPIm_PWdata_0S;
  input SPIm_Paddr_8S;
  input SPIm_Paddr_6S;
  input FB_PKfbPush_1S;
  input FB_PKfbData_31S;
  input FB_PKfbData_21S;
  input FB_PKfbData_19S;
  input FB_PKfbData_9S;
  input FB_PKfbData_6S;
  input Sys_PKfb_ClkS;
  input FB_BusyS;
  input WB_CLKS;


  wire [16:0] WBs_ADR;
  wire WBs_CYC;
  wire [3:0] WBs_BYTE_STB;
  wire WBs_WE;
  wire WBs_RD;
  wire WBs_STB;
  wire [31:0] WBs_WR_DAT;
  wire WB_CLK;
  reg WB_RST;
  wire [31:0] WBs_RD_DAT;
  wire WBs_ACK;

  wire [3:0] SDMA_Req;
  wire [3:0] SDMA_Sreq;
  //reg [3:0] SDMA_Done;//SDMA BFM
  //reg [3:0] SDMA_Active;//SDMA BFM
  wire [3:0] SDMA_Done;
  wire [3:0] SDMA_Active;

  wire [3:0] FB_msg_out;
  wire [7:0] FB_Int_Clr;
  reg FB_Start;
  wire FB_Busy;

  wire Sys_Clk0;
  reg Sys_Clk0_Rst;
  wire Sys_Clk1;
  reg Sys_Clk1_Rst;

  wire Sys_PKfb_Clk;
  reg Sys_PKfb_Rst;
  wire [31:0] FB_PKfbData;
  wire [3:0] FB_PKfbPush;
  wire FB_PKfbSOF;
  wire FB_PKfbEOF;
  reg FB_PKfbOverflow;

  reg [7:0] Sensor_Int;
  reg [23:0] TimeStamp;

  reg Sys_Pclk;
  reg Sys_Pclk_Rst;
  wire Sys_PSel;

  wire [15:0] SPIm_Paddr;
  wire SPIm_PEnable;
  wire SPIm_PWrite;
  wire [31:0] SPIm_PWdata;
  reg [31:0] SPIm_Prdata;
  reg SPIm_PReady;
  reg SPIm_PSlvErr;

  wire [15:0] Device_ID;

  reg [13:0] FBIO_In;
  wire [13:0] FBIO_In_En;
  wire [13:0] FBIO_Out;
  wire [13:0] FBIO_Out_En;

  wire [13:0] SFBIO;
  wire Device_ID_6S;
  wire Device_ID_4S;

  wire SPIm_PWdata_26S;
  wire SPIm_PWdata_24S;
  wire SPIm_PWdata_14S;
  wire SPIm_PWdata_11S;
  wire SPIm_PWdata_0S;
  wire SPIm_Paddr_8S;
  wire SPIm_Paddr_6S;

  wire FB_PKfbPush_1S;
  wire FB_PKfbData_31S;
  wire FB_PKfbData_21S;
  wire FB_PKfbData_19S;
  wire FB_PKfbData_9S;
  wire FB_PKfbData_6S;
  wire Sys_PKfb_ClkS;

  wire FB_BusyS;
  wire WB_CLKS;


  //------Define Parameters--------------
  //

  parameter ADDRWIDTH = 32;
  parameter DATAWIDTH = 32;
  parameter APERWIDTH = 17;

  parameter ENABLE_AHB_REG_WR_DEBUG_MSG = 1'b1;
  parameter ENABLE_AHB_REG_RD_DEBUG_MSG = 1'b1;

  parameter T_CYCLE_CLK_SYS_CLK0 = 200;//230;//ACSLIPTEST-230;//100;//180;//(1000.0/(80.0/16)) ; // Default EOS S3B Clock Rate
  parameter T_CYCLE_CLK_SYS_CLK1 = 650;//3906;//650;////83.33;//250;//30517;//(1000.0/(80.0/16)) ; // Default EOS S3B Clock Rate
  parameter T_CYCLE_CLK_A2F_HCLK = (1000.0 / (80.0 / 12));  // Default EOS S3B Clock Rate

  parameter SYS_CLK0_RESET_LOOP = 5;  //4.34;//5;
  parameter SYS_CLK1_RESET_LOOP = 5;
  parameter WB_CLK_RESET_LOOP = 5;
  parameter A2F_HCLK_RESET_LOOP = 5;

  //------Internal Signals---------------
  //

  integer Sys_Clk0_Reset_Loop_Cnt;
  integer Sys_Clk1_Reset_Loop_Cnt;
  integer WB_CLK_Reset_Loop_Cnt;
  integer A2F_HCLK_Reset_Loop_Cnt;


  wire A2F_HCLK;
  reg A2F_HRESET;

  wire [31:0] A2F_HADDRS;
  wire A2F_HSEL;
  wire [1:0] A2F_HTRANSS;
  wire [2:0] A2F_HSIZES;
  wire A2F_HWRITES;
  wire A2F_HREADYS;
  wire [31:0] A2F_HWDATAS;

  wire A2F_HREADYOUTS;
  wire A2F_HRESPS;
  wire [31:0] A2F_HRDATAS;


  //------Logic Operations---------------
  //

  // Apply Reset to Sys_Clk0 domain
  //
  initial begin

    Sys_Clk0_Rst <= 1'b1;
`ifndef YOSYS
    for (
        Sys_Clk0_Reset_Loop_Cnt = 0;
        Sys_Clk0_Reset_Loop_Cnt < SYS_CLK0_RESET_LOOP;
        Sys_Clk0_Reset_Loop_Cnt = Sys_Clk0_Reset_Loop_Cnt + 1
    ) begin
      wait(Sys_Clk0 == 1'b1) #1;
      wait(Sys_Clk0 == 1'b0) #1;
    end

    wait(Sys_Clk0 == 1'b1) #1;
`endif
    Sys_Clk0_Rst <= 1'b0;
  end

  // Apply Reset to Sys_Clk1 domain
  //
  initial begin

    Sys_Clk1_Rst <= 1'b1;
`ifndef YOSYS
    for (
        Sys_Clk1_Reset_Loop_Cnt = 0;
        Sys_Clk1_Reset_Loop_Cnt < SYS_CLK1_RESET_LOOP;
        Sys_Clk1_Reset_Loop_Cnt = Sys_Clk1_Reset_Loop_Cnt + 1
    ) begin
      wait(Sys_Clk1 == 1'b1) #1;
      wait(Sys_Clk1 == 1'b0) #1;
    end

    wait(Sys_Clk1 == 1'b1) #1;
`endif
    Sys_Clk1_Rst <= 1'b0;
  end

  // Apply Reset to the Wishbone domain
  //
  // Note: In the ASSP, this reset is distict from the reset domains for Sys_Clk[1:0].
  //
  initial begin

    WB_RST <= 1'b1;
`ifndef YOSYS
    for (
        WB_CLK_Reset_Loop_Cnt = 0;
        WB_CLK_Reset_Loop_Cnt < WB_CLK_RESET_LOOP;
        WB_CLK_Reset_Loop_Cnt = WB_CLK_Reset_Loop_Cnt + 1
    ) begin
      wait(WB_CLK == 1'b1) #1;
      wait(WB_CLK == 1'b0) #1;
    end

    wait(WB_CLK == 1'b1) #1;
`endif
    WB_RST <= 1'b0;

  end

  // Apply Reset to the AHB Bus domain
  //
  // Note: The AHB bus clock domain is separate from the Sys_Clk[1:0] domains
  initial begin

    A2F_HRESET <= 1'b1;
`ifndef YOSYS
    for (
        A2F_HCLK_Reset_Loop_Cnt = 0;
        A2F_HCLK_Reset_Loop_Cnt < A2F_HCLK_RESET_LOOP;
        A2F_HCLK_Reset_Loop_Cnt = A2F_HCLK_Reset_Loop_Cnt + 1
    ) begin
      wait(A2F_HCLK == 1'b1) #1;
      wait(A2F_HCLK == 1'b0) #1;
    end

    wait(A2F_HCLK == 1'b1) #1;
`endif
    A2F_HRESET <= 1'b0;

  end

  // Initialize all outputs
  //
  // Note: These may be replaced in the future by BFMs as the become available.
  //
  //       These registers allow test bench routines to drive these signals as needed.
  //
  initial begin

    //
    // SDMA Signals
    //
    //SDMA_Done       <=  4'h0;//Added SDMA BFM
    // SDMA_Active     <=  4'h0;//Added SDMA BFM

    //
    // FB Interrupts
    //
    FB_Start <= 1'b0;

    //
    // Packet FIFO
    //
    Sys_PKfb_Rst <= 1'b0;
    FB_PKfbOverflow <= 1'b0;

    //
    // Sensor Interface
    //
    Sensor_Int <= 8'h0;
    TimeStamp <= 24'h0;

    //
    // SPI Master APB Bus
    //
    Sys_Pclk <= 1'b0;
    Sys_Pclk_Rst <= 1'b0;

    SPIm_Prdata <= 32'h0;
    SPIm_PReady <= 1'b0;
    SPIm_PSlvErr <= 1'b0;

    //
    // FBIO Signals
    //
    FBIO_In <= 14'h0;

  end


  //------Instantiate Modules------------
  //

  ahb2fb_asynbrig #(
    .ADDRWIDTH(ADDRWIDTH),
    .DATAWIDTH(DATAWIDTH),
    .APERWIDTH(APERWIDTH)
  ) u_ffe_ahb_to_fabric_async_bridge (
    // AHB Slave Interface to AHB Bus Matrix
    //
    .A2F_HCLK(A2F_HCLK),
    .A2F_HRESET(A2F_HRESET),

    .A2F_HADDRS(A2F_HADDRS),
    .A2F_HSEL(A2F_HSEL),
    .A2F_HTRANSS(A2F_HTRANSS),
    .A2F_HSIZES(A2F_HSIZES),
    .A2F_HWRITES(A2F_HWRITES),
    .A2F_HREADYS(A2F_HREADYS),
    .A2F_HWDATAS(A2F_HWDATAS),

    .A2F_HREADYOUTS(A2F_HREADYOUTS),
    .A2F_HRESPS(A2F_HRESPS),
    .A2F_HRDATAS(A2F_HRDATAS),

    // Fabric Wishbone Bus
    //
    .WB_CLK_I(WB_CLK),
    .WB_RST_I(WB_RST),
    .WB_DAT_I(WBs_RD_DAT),
    .WB_ACK_I(WBs_ACK),

    .WB_ADR_O(WBs_ADR),
    .WB_CYC_O(WBs_CYC),
    .WB_BYTE_STB_O(WBs_BYTE_STB),
    .WB_WE_O(WBs_WE),
    .WB_RD_O(WBs_RD),
    .WB_STB_O(WBs_STB),
    .WB_DAT_O(WBs_WR_DAT)

  );


  ahb_gen_bfm #(
    .ADDRWIDTH(ADDRWIDTH),
    .DATAWIDTH(DATAWIDTH),
    .DEFAULT_AHB_ADDRESS({(ADDRWIDTH) {1'b1}}),
    .STD_CLK_DLY(2),
    .ENABLE_AHB_REG_WR_DEBUG_MSG(ENABLE_AHB_REG_WR_DEBUG_MSG),
    .ENABLE_AHB_REG_RD_DEBUG_MSG(ENABLE_AHB_REG_RD_DEBUG_MSG)
  ) u_ahb_gen_bfm (
    // AHB Slave Interface to AHB Bus Matrix
    //
    .A2F_HCLK(A2F_HCLK),
    .A2F_HRESET(A2F_HRESET),

    .A2F_HADDRS(A2F_HADDRS),
    .A2F_HSEL(A2F_HSEL),
    .A2F_HTRANSS(A2F_HTRANSS),
    .A2F_HSIZES(A2F_HSIZES),
    .A2F_HWRITES(A2F_HWRITES),
    .A2F_HREADYS(A2F_HREADYS),
    .A2F_HWDATAS(A2F_HWDATAS),

    .A2F_HREADYOUTS(A2F_HREADYOUTS),
    .A2F_HRESPS(A2F_HRESPS),
    .A2F_HRDATAS(A2F_HRDATAS)

  );

  // Define the clock cycle times.
  //
  // Note:    Values are calculated to output in units of nS.
  //
  oscillator_s1 #(
    .T_CYCLE_CLK(T_CYCLE_CLK_SYS_CLK0)
  ) u_osc_sys_clk0 (
    .OSC_CLK_EN(1'b1),
    .OSC_CLK(Sys_Clk0)
  );
  oscillator_s1 #(
    .T_CYCLE_CLK(T_CYCLE_CLK_SYS_CLK1)
  ) u_osc_sys_clk1 (
    .OSC_CLK_EN(1'b1),
    .OSC_CLK(Sys_Clk1)
  );
  oscillator_s1 #(
    .T_CYCLE_CLK(T_CYCLE_CLK_A2F_HCLK)
  ) u_osc_a2f_hclk (
    .OSC_CLK_EN(1'b1),
    .OSC_CLK(A2F_HCLK)
  );

  //SDMA bfm
  sdma_bfm sdma_bfm_inst0 (
    .sdma_req_i(SDMA_Req),
    .sdma_sreq_i(SDMA_Sreq),
    .sdma_done_o(SDMA_Done),
    .sdma_active_o(SDMA_Active)
  );

endmodule  /* qlal4s3b_cell_macro_bfm*/

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

  qlal4s3b_cell_macro_bfm u_ASSP_bfm_inst (
    .WBs_ADR(WBs_ADR),
    .WBs_CYC(WBs_CYC),
    .WBs_BYTE_STB(WBs_BYTE_STB),
    .WBs_WE(WBs_WE),
    .WBs_RD(WBs_RD),
    .WBs_STB(WBs_STB),
    .WBs_WR_DAT(WBs_WR_DAT),
    .WB_CLK(WB_CLK),
    .WB_RST(WB_RST),
    .WBs_RD_DAT(WBs_RD_DAT),
    .WBs_ACK(WBs_ACK),
    //
    // SDMA Signals
    //
    .SDMA_Req(SDMA_Req),
    .SDMA_Sreq(SDMA_Sreq),
    .SDMA_Done(SDMA_Done),
    .SDMA_Active(SDMA_Active),
    //
    // FB Interrupts
    //
    .FB_msg_out(FB_msg_out),
    .FB_Int_Clr(FB_Int_Clr),
    .FB_Start(FB_Start),
    .FB_Busy(FB_Busy),
    //
    // FB Clocks
    //
    .Sys_Clk0(Sys_Clk12),
    .Sys_Clk0_Rst(Sys_Clk12_Rst),
    .Sys_Clk1(Sys_Clk21),
    .Sys_Clk1_Rst(Sys_Clk21_Rst),
    //
    // Packet FIFO
    //
    .Sys_PKfb_Clk(Sys_PKfb_Clk),
    .Sys_PKfb_Rst(Sys_PKfb_Rst),
    .FB_PKfbData(FB_PKfbData),
    .FB_PKfbPush(FB_PKfbPush),
    .FB_PKfbSOF(FB_PKfbSOF),
    .FB_PKfbEOF(FB_PKfbEOF),
    .FB_PKfbOverflow(FB_PKfbOverflow),
    //
    // Sensor Interface
    //
    .Sensor_Int(Sensor_Int),
    .TimeStamp(TimeStamp),
    //
    // SPI Master APB Bus
    //
    .Sys_Pclk(Sys_Pclk),
    .Sys_Pclk_Rst(Sys_Pclk_Rst),
    .Sys_PSel(Sys_PSel),
    .SPIm_Paddr(SPIm_Paddr),
    .SPIm_PEnable(SPIm_PEnable),
    .SPIm_PWrite(SPIm_PWrite),
    .SPIm_PWdata(SPIm_PWdata),
    .SPIm_Prdata(SPIm_Prdata),
    .SPIm_PReady(SPIm_PReady),
    .SPIm_PSlvErr(SPIm_PSlvErr),
    //
    // Misc
    //
    .Device_ID(Device_ID),
    //
    // FBIO Signals
    //
    .FBIO_In(FBIO_In),
    .FBIO_In_En(FBIO_In_En),
    .FBIO_Out(FBIO_Out),
    .FBIO_Out_En(FBIO_Out_En),
    //
    // ???
    //
    .SFBIO(SFBIO),
    .Device_ID_6S(Device_ID_6S),
    .Device_ID_4S(Device_ID_4S),
    .SPIm_PWdata_26S(SPIm_PWdata_26S),
    .SPIm_PWdata_24S(SPIm_PWdata_24S),
    .SPIm_PWdata_14S(SPIm_PWdata_14S),
    .SPIm_PWdata_11S(SPIm_PWdata_11S),
    .SPIm_PWdata_0S(SPIm_PWdata_0S),
    .SPIm_Paddr_8S(SPIm_Paddr_8S),
    .SPIm_Paddr_6S(SPIm_Paddr_6S),
    .FB_PKfbPush_1S(FB_PKfbPush_1S),
    .FB_PKfbData_31S(FB_PKfbData_31S),
    .FB_PKfbData_21S(FB_PKfbData_21S),
    .FB_PKfbData_19S(FB_PKfbData_19S),
    .FB_PKfbData_9S(FB_PKfbData_9S),
    .FB_PKfbData_6S(FB_PKfbData_6S),
    .Sys_PKfb_ClkS(Sys_PKfb_ClkS),
    .FB_BusyS(FB_BusyS),
    .WB_CLKS(WB_CLKS)
  );

endmodule  /* qlal4s3b_cell_macro */

`timescale 1ns / 10ps
module fifo_controller_model (
  Rst_n,
  Push_Clk,
  Pop_Clk,

  Fifo_Push,
  Fifo_Push_Flush,
  Fifo_Full,
  Fifo_Full_Usr,

  Fifo_Pop,
  Fifo_Pop_Flush,
  Fifo_Empty,
  Fifo_Empty_Usr,

  Write_Addr,

  Read_Addr,

  //	 Static Control Signals
  Fifo_Ram_Mode,
  Fifo_Sync_Mode,
  Fifo_Push_Width,
  Fifo_Pop_Width
);

  //************* PPII 4K Parameters **************************//

  parameter MAX_PTR_WIDTH = 12;

  parameter DEPTH1 = (1 << (MAX_PTR_WIDTH - 3));
  parameter DEPTH2 = (1 << (MAX_PTR_WIDTH - 2));
  parameter DEPTH3 = (1 << (MAX_PTR_WIDTH - 1));

  parameter D1_QTR_A = MAX_PTR_WIDTH - 5;
  parameter D2_QTR_A = MAX_PTR_WIDTH - 4;
  parameter D3_QTR_A = MAX_PTR_WIDTH - 3;

  input Rst_n;
  input Push_Clk;
  input Pop_Clk;

  input Fifo_Push;
  input Fifo_Push_Flush;
  output Fifo_Full;
  output [3:0] Fifo_Full_Usr;

  input Fifo_Pop;
  input Fifo_Pop_Flush;
  output Fifo_Empty;
  output [3:0] Fifo_Empty_Usr;

  output [MAX_PTR_WIDTH-2:0] Write_Addr;

  output [MAX_PTR_WIDTH-2:0] Read_Addr;

  input Fifo_Ram_Mode;
  input Fifo_Sync_Mode;
  input [1:0] Fifo_Push_Width;
  input [1:0] Fifo_Pop_Width;

  reg flush_pop_clk_tf;
  reg flush_pop2push_clk1;
  reg flush_push_clk_tf;
  reg flush_push2pop_clk1;
  reg pop_local_flush_mask;
  reg push_flush_tf_pop_clk;
  reg pop2push_ack1;
  reg pop2push_ack2;
  reg push_local_flush_mask;
  reg pop_flush_tf_push_clk;
  reg push2pop_ack1;
  reg push2pop_ack2;

  reg fifo_full_flag_f;
  reg [3:0] Fifo_Full_Usr;

  reg fifo_empty_flag_f;
  reg [3:0] Fifo_Empty_Usr;

  reg [MAX_PTR_WIDTH-1:0] push_ptr_push_clk;
  reg [MAX_PTR_WIDTH-1:0] pop_ptr_push_clk;
  reg [MAX_PTR_WIDTH-1:0] pop_ptr_async;
  reg [MAX_PTR_WIDTH-1:0] pop_ptr_pop_clk;
  reg [MAX_PTR_WIDTH-1:0] push_ptr_pop_clk;
  reg [MAX_PTR_WIDTH-1:0] push_ptr_async;

  reg [1:0] push_ptr_push_clk_mask;
  reg [1:0] pop_ptr_pop_clk_mask;

  reg [MAX_PTR_WIDTH-1:0] pop_ptr_push_clk_mux;
  reg [MAX_PTR_WIDTH-1:0] push_ptr_pop_clk_mux;

  reg match_room4none;
  reg match_room4one;
  reg match_room4half;
  reg match_room4quart;

  reg match_all_left;
  reg match_half_left;
  reg match_quart_left;

  reg [MAX_PTR_WIDTH-1:0] depth1_reg;
  reg [MAX_PTR_WIDTH-1:0] depth2_reg;
  reg [MAX_PTR_WIDTH-1:0] depth3_reg;


  wire push_clk_rst;
  wire push_clk_rst_mux;
  wire push_flush_done;
  wire pop_clk_rst;
  wire pop_clk_rst_mux;
  wire pop_flush_done;

  wire push_flush_gated;
  wire pop_flush_gated;

  wire [MAX_PTR_WIDTH-2:0] Write_Addr;
  wire [MAX_PTR_WIDTH-2:0] Read_Addr;

  wire [MAX_PTR_WIDTH-1:0] push_ptr_push_clk_plus1;
  wire [MAX_PTR_WIDTH-1:0] next_push_ptr_push_clk;
  wire [MAX_PTR_WIDTH-1:0] pop_ptr_pop_clk_plus1;
  wire [MAX_PTR_WIDTH-1:0] next_pop_ptr_pop_clk;
  wire [MAX_PTR_WIDTH-1:0] next_push_ptr_push_clk_mask;
  wire [MAX_PTR_WIDTH-1:0] next_pop_ptr_pop_clk_mask;

  wire [MAX_PTR_WIDTH-1:0] pop_ptr_push_clk_l_shift1;
  wire [MAX_PTR_WIDTH-1:0] pop_ptr_push_clk_l_shift2;
  wire [MAX_PTR_WIDTH-1:0] pop_ptr_push_clk_r_shift1;
  wire [MAX_PTR_WIDTH-1:0] pop_ptr_push_clk_r_shift2;

  wire [MAX_PTR_WIDTH-1:0] push_ptr_pop_clk_l_shift1;
  wire [MAX_PTR_WIDTH-1:0] push_ptr_pop_clk_l_shift2;
  wire [MAX_PTR_WIDTH-1:0] push_ptr_pop_clk_r_shift1;
  wire [MAX_PTR_WIDTH-1:0] push_ptr_pop_clk_r_shift2;

  wire [MAX_PTR_WIDTH-1:0] push_diff;
  wire [MAX_PTR_WIDTH-1:0] push_diff_plus_1;
  wire [MAX_PTR_WIDTH-1:0] pop_diff;

  wire match_room4all;
  wire match_room4eight;

  wire match_one_left;
  wire match_one2eight_left;

  integer depth_sel_push;
  integer depth_sel_pop;

  initial begin
    depth1_reg = DEPTH1;
    depth2_reg = DEPTH2;
    depth3_reg = DEPTH3;
  end

  initial begin
    flush_pop_clk_tf <= 1'b0;
    push2pop_ack1 <= 1'b0;
    push2pop_ack2 <= 1'b0;
    pop_local_flush_mask <= 1'b0;
    flush_push2pop_clk1 <= 1'b0;
    push_flush_tf_pop_clk <= 1'b0;
    flush_push_clk_tf <= 1'b0;
    pop2push_ack1 <= 1'b0;
    pop2push_ack2 <= 1'b0;
    push_local_flush_mask <= 1'b0;
    flush_pop2push_clk1 <= 1'b0;
    pop_flush_tf_push_clk <= 1'b0;
    push_ptr_push_clk <= 0;
    pop_ptr_push_clk <= 0;
    pop_ptr_async <= 0;
    fifo_full_flag_f <= 0;
    pop_ptr_pop_clk <= 0;
    push_ptr_pop_clk <= 0;
    push_ptr_async <= 0;
    fifo_empty_flag_f <= 1;
    Fifo_Full_Usr <= 4'b0001;
    Fifo_Empty_Usr <= 4'b0000;
  end

  assign Fifo_Full = fifo_full_flag_f;
  assign Fifo_Empty = fifo_empty_flag_f;

  assign Write_Addr = push_ptr_push_clk[MAX_PTR_WIDTH-2:0];
  assign Read_Addr = next_pop_ptr_pop_clk[MAX_PTR_WIDTH-2:0];

  assign push_ptr_push_clk_plus1 = push_ptr_push_clk + 1;
  assign next_push_ptr_push_clk = (Fifo_Push) ? push_ptr_push_clk_plus1 : push_ptr_push_clk;
  assign next_push_ptr_push_clk_mask = {
    (push_ptr_push_clk_mask & next_push_ptr_push_clk[MAX_PTR_WIDTH-1:MAX_PTR_WIDTH-2]),
    next_push_ptr_push_clk[MAX_PTR_WIDTH-3:0]
  };

  assign pop_ptr_pop_clk_plus1 = pop_ptr_pop_clk + 1;
  assign next_pop_ptr_pop_clk = (Fifo_Pop) ? pop_ptr_pop_clk_plus1 : pop_ptr_pop_clk;
  assign next_pop_ptr_pop_clk_mask = {
    (pop_ptr_pop_clk_mask & next_pop_ptr_pop_clk[MAX_PTR_WIDTH-1:MAX_PTR_WIDTH-2]),
    next_pop_ptr_pop_clk[MAX_PTR_WIDTH-3:0]
  };

  assign pop_ptr_push_clk_l_shift1 = {pop_ptr_push_clk[MAX_PTR_WIDTH-2:0], 1'b0};
  assign pop_ptr_push_clk_l_shift2 = {pop_ptr_push_clk[MAX_PTR_WIDTH-3:0], 2'b0};
  assign pop_ptr_push_clk_r_shift1 = {1'b0, pop_ptr_push_clk[MAX_PTR_WIDTH-1:1]};
  assign pop_ptr_push_clk_r_shift2 = {2'b0, pop_ptr_push_clk[MAX_PTR_WIDTH-1:2]};

  assign push_ptr_pop_clk_l_shift1 = {push_ptr_pop_clk[MAX_PTR_WIDTH-2:0], 1'b0};
  assign push_ptr_pop_clk_l_shift2 = {push_ptr_pop_clk[MAX_PTR_WIDTH-3:0], 2'b0};
  assign push_ptr_pop_clk_r_shift1 = {1'b0, push_ptr_pop_clk[MAX_PTR_WIDTH-1:1]};
  assign push_ptr_pop_clk_r_shift2 = {2'b0, push_ptr_pop_clk[MAX_PTR_WIDTH-1:2]};

  assign push_diff = next_push_ptr_push_clk_mask - pop_ptr_push_clk_mux;
  assign push_diff_plus_1 = push_diff + 1;
  assign pop_diff = push_ptr_pop_clk_mux - next_pop_ptr_pop_clk_mask;

  assign match_room4all = ~|push_diff;
  assign	match_room4eight	= ( depth_sel_push == 3 ) ? ( push_diff >= DEPTH3-8 ) : ( depth_sel_push == 2 ) ? ( push_diff >= DEPTH2-8 ) : ( push_diff >= DEPTH1-8 );

  assign match_one_left = (pop_diff == 1);
  assign match_one2eight_left = (pop_diff < 8);

  assign push_flush_gated = Fifo_Push_Flush & ~push_local_flush_mask;
  assign pop_flush_gated = Fifo_Pop_Flush & ~pop_local_flush_mask;

  assign push_clk_rst = flush_pop2push_clk1 ^ pop_flush_tf_push_clk;
  assign pop_clk_rst = flush_push2pop_clk1 ^ push_flush_tf_pop_clk;

  assign pop_flush_done = push2pop_ack1 ^ push2pop_ack2;
  assign push_flush_done = pop2push_ack1 ^ pop2push_ack2;

  assign	push_clk_rst_mux	= ( Fifo_Sync_Mode ) ? ( Fifo_Push_Flush | Fifo_Pop_Flush ) : ( push_flush_gated | push_clk_rst );
  assign	pop_clk_rst_mux		= ( Fifo_Sync_Mode ) ? ( Fifo_Push_Flush | Fifo_Pop_Flush ) : ( pop_flush_gated | ( pop_local_flush_mask & ~pop_flush_done ) | pop_clk_rst );


  reg match_room_at_most63, match_at_most63_left;

  always@( push_diff or push_diff_plus_1 or depth_sel_push or match_room4none or match_room4one )
	begin
    if (depth_sel_push == 1) begin
      match_room4none <= (push_diff[D1_QTR_A+2:0] == depth1_reg[D1_QTR_A+2:0]);
      // syao 2/12/2013
      match_room4one <= (push_diff_plus_1[D1_QTR_A+2:0] == depth1_reg) | match_room4none;

      match_room4half <= (push_diff[D1_QTR_A+1] == 1'b1);
      match_room4quart <= (push_diff[D1_QTR_A] == 1'b1);

      match_room_at_most63 <= push_diff[6];
    end else if (depth_sel_push == 2) begin
      match_room4none <= (push_diff[D2_QTR_A+2:0] == depth2_reg[D2_QTR_A+2:0]);
      // syao 2/12/2013
      match_room4one <= (push_diff_plus_1[D2_QTR_A+2:0] == depth2_reg) | match_room4none;

      match_room4half <= (push_diff[D2_QTR_A+1] == 1'b1);
      match_room4quart <= (push_diff[D2_QTR_A] == 1'b1);

      // syao 2/12/2013
      //			match_room_at_most63    <=  push_diff[6];
      match_room_at_most63 <= &push_diff[7:6];
    end else begin
      match_room4none <= (push_diff == depth3_reg);
      match_room4one <= (push_diff_plus_1 == depth3_reg) | match_room4none;

      match_room4half <= (push_diff[D3_QTR_A+1] == 1'b1);
      match_room4quart <= (push_diff[D3_QTR_A] == 1'b1);

      // syao 2/12/2013
      //			match_room_at_most63	<= &push_diff[7:6];
      match_room_at_most63 <= &push_diff[8:6];
    end
  end

  assign room4_32s = ~push_diff[5];
  assign room4_16s = ~push_diff[4];
  assign room4_8s = ~push_diff[3];
  assign room4_4s = ~push_diff[2];
  assign room4_2s = ~push_diff[1];
  assign room4_1s = &push_diff[1:0];

  always @(depth_sel_pop or pop_diff) begin
    if (depth_sel_pop == 1) begin
      match_all_left <= (pop_diff[D1_QTR_A+2:0] == depth1_reg[D1_QTR_A+2:0]);

      match_half_left <= (pop_diff[D1_QTR_A+1] == 1'b1);
      match_quart_left <= (pop_diff[D1_QTR_A] == 1'b1);

      match_at_most63_left <= ~pop_diff[6];
    end else if (depth_sel_pop == 2) begin
      match_all_left <= (pop_diff[D2_QTR_A+2:0] == depth2_reg[D2_QTR_A+2:0]);

      match_half_left <= (pop_diff[D2_QTR_A+1] == 1'b1);
      match_quart_left <= (pop_diff[D2_QTR_A] == 1'b1);

      // syao 2/12/2013
      //			match_at_most63_left	<= ~pop_diff[6];
      match_at_most63_left <= ~|pop_diff[7:6];
    end else begin
      match_all_left <= (pop_diff == depth3_reg);

      match_half_left <= (pop_diff[D3_QTR_A+1] == 1'b1);
      match_quart_left <= (pop_diff[D3_QTR_A] == 1'b1);

      // syao 2/12/2013
      //			match_at_most63_left	<= ~|pop_diff[7:6];
      match_at_most63_left <= ~|pop_diff[8:6];
    end
  end

  assign at_least_32 = pop_diff[5];
  assign at_least_16 = pop_diff[4];
  assign at_least_8 = pop_diff[3];
  assign at_least_4 = pop_diff[2];
  assign at_least_2 = pop_diff[1];
  assign one_left = pop_diff[0];

  always @(posedge Pop_Clk or negedge Rst_n) begin
    if (~Rst_n) begin
      push2pop_ack1 <= 1'b0;
      push2pop_ack2 <= 1'b0;
      flush_pop_clk_tf <= 1'b0;
      pop_local_flush_mask <= 1'b0;
      flush_push2pop_clk1 <= 1'b0;
      push_flush_tf_pop_clk <= 1'b0;
    end else begin
      push2pop_ack1 <= pop_flush_tf_push_clk;
      push2pop_ack2 <= push2pop_ack1;
      flush_push2pop_clk1 <= flush_push_clk_tf;
      if (pop_flush_gated) begin
        flush_pop_clk_tf <= ~flush_pop_clk_tf;
      end

      if (pop_flush_gated & ~Fifo_Sync_Mode) begin
        pop_local_flush_mask <= 1'b1;
      end else if (pop_flush_done) begin
        pop_local_flush_mask <= 1'b0;
      end

      if (pop_clk_rst) begin
        push_flush_tf_pop_clk <= ~push_flush_tf_pop_clk;
      end
    end
  end

  always @(posedge Push_Clk or negedge Rst_n) begin
    if (~Rst_n) begin
      pop2push_ack1 <= 1'b0;
      pop2push_ack2 <= 1'b0;
      flush_push_clk_tf <= 1'b0;
      push_local_flush_mask <= 1'b0;
      flush_pop2push_clk1 <= 1'b0;
      pop_flush_tf_push_clk <= 1'b0;
    end else begin
      pop2push_ack1 <= push_flush_tf_pop_clk;
      pop2push_ack2 <= pop2push_ack1;
      flush_pop2push_clk1 <= flush_pop_clk_tf;
      if (push_flush_gated) begin
        flush_push_clk_tf <= ~flush_push_clk_tf;
      end

      if (push_flush_gated & ~Fifo_Sync_Mode) begin
        push_local_flush_mask <= 1'b1;
      end else if (push_flush_done) begin
        push_local_flush_mask <= 1'b0;
      end

      if (push_clk_rst) begin
        pop_flush_tf_push_clk <= ~pop_flush_tf_push_clk;
      end
    end
  end

  always@( Fifo_Push_Width or Fifo_Pop_Width or pop_ptr_push_clk_l_shift1 or pop_ptr_push_clk_l_shift2 or pop_ptr_push_clk_r_shift1 or
						pop_ptr_push_clk_r_shift2 or push_ptr_pop_clk_l_shift1 or push_ptr_pop_clk_l_shift2 or push_ptr_pop_clk_r_shift1 or push_ptr_pop_clk_r_shift2 or
						pop_ptr_push_clk or push_ptr_pop_clk )
	begin
    case ({
      Fifo_Push_Width, Fifo_Pop_Width
    })
      4'b0001:	//	byte push halfword pop
      begin
        push_ptr_push_clk_mask <= 2'b11;
        pop_ptr_pop_clk_mask <= 2'b01;
        pop_ptr_push_clk_mux <= pop_ptr_push_clk_l_shift1;
        push_ptr_pop_clk_mux <= push_ptr_pop_clk_r_shift1;
      end
      4'b0010:	//	byte push word pop
      begin
        push_ptr_push_clk_mask <= 2'b11;
        pop_ptr_pop_clk_mask <= 2'b00;
        pop_ptr_push_clk_mux <= pop_ptr_push_clk_l_shift2;
        push_ptr_pop_clk_mux <= push_ptr_pop_clk_r_shift2;
      end
      4'b0100:	//	halfword push byte pop
      begin
        push_ptr_push_clk_mask <= 2'b01;
        pop_ptr_pop_clk_mask <= 2'b11;
        pop_ptr_push_clk_mux <= pop_ptr_push_clk_r_shift1;
        push_ptr_pop_clk_mux <= push_ptr_pop_clk_l_shift1;
      end
      4'b0110:	//	halfword push word pop
      begin
        push_ptr_push_clk_mask <= 2'b11;
        pop_ptr_pop_clk_mask <= 2'b01;
        pop_ptr_push_clk_mux <= pop_ptr_push_clk_l_shift1;
        push_ptr_pop_clk_mux <= push_ptr_pop_clk_r_shift1;
      end
      4'b1000:	//	word push byte pop
      begin
        push_ptr_push_clk_mask <= 2'b00;
        pop_ptr_pop_clk_mask <= 2'b11;
        pop_ptr_push_clk_mux <= pop_ptr_push_clk_r_shift2;
        push_ptr_pop_clk_mux <= push_ptr_pop_clk_l_shift2;
      end
      4'b1001:	//	word push halfword pop
      begin
        push_ptr_push_clk_mask <= 2'b01;
        pop_ptr_pop_clk_mask <= 2'b11;
        pop_ptr_push_clk_mux <= pop_ptr_push_clk_r_shift1;
        push_ptr_pop_clk_mux <= push_ptr_pop_clk_l_shift1;
      end
      default:	//	no conversion
      begin
        push_ptr_push_clk_mask <= 2'b11;
        pop_ptr_pop_clk_mask <= 2'b11;
        pop_ptr_push_clk_mux <= pop_ptr_push_clk;
        push_ptr_pop_clk_mux <= push_ptr_pop_clk;
      end
    endcase
  end

  always @(Fifo_Ram_Mode or Fifo_Push_Width) begin
    if (Fifo_Ram_Mode == Fifo_Push_Width[0]) begin
      depth_sel_push <= 2;
    end else if (Fifo_Ram_Mode == Fifo_Push_Width[1]) begin
      depth_sel_push <= 1;
    end else begin
      depth_sel_push <= 3;
    end
  end

  always @(Fifo_Ram_Mode or Fifo_Pop_Width) begin
    if (Fifo_Ram_Mode == Fifo_Pop_Width[0]) begin
      depth_sel_pop <= 2;
    end else if (Fifo_Ram_Mode == Fifo_Pop_Width[1]) begin
      depth_sel_pop <= 1;
    end else begin
      depth_sel_pop <= 3;
    end
  end

  always @(posedge Push_Clk or negedge Rst_n) begin
    if (~Rst_n) begin
      push_ptr_push_clk <= 0;
      pop_ptr_push_clk <= 0;
      pop_ptr_async <= 0;
      fifo_full_flag_f <= 0;
    end else begin
      if (push_clk_rst_mux) begin
        push_ptr_push_clk <= 0;
        pop_ptr_push_clk <= 0;
        pop_ptr_async <= 0;
        fifo_full_flag_f <= 0;
      end else begin
        push_ptr_push_clk <= next_push_ptr_push_clk;
        pop_ptr_push_clk <= (Fifo_Sync_Mode) ? next_pop_ptr_pop_clk : pop_ptr_async;
        pop_ptr_async <= pop_ptr_pop_clk;
        fifo_full_flag_f <= match_room4one | match_room4none;
      end
    end
  end

  always @(posedge Pop_Clk or negedge Rst_n) begin
    if (~Rst_n) begin
      pop_ptr_pop_clk <= 0;
      push_ptr_pop_clk <= 0;
      push_ptr_async <= 0;
      fifo_empty_flag_f <= 1;
    end else begin
      if (pop_clk_rst_mux) begin
        pop_ptr_pop_clk <= 0;
        push_ptr_pop_clk <= 0;
        push_ptr_async <= 0;
        fifo_empty_flag_f <= 1;
      end else begin
        pop_ptr_pop_clk <= next_pop_ptr_pop_clk;
        push_ptr_pop_clk <= (Fifo_Sync_Mode) ? next_push_ptr_push_clk : push_ptr_async;
        push_ptr_async <= push_ptr_push_clk;
        fifo_empty_flag_f <= (pop_diff == 1) | (pop_diff == 0);
      end
    end
  end

  always @(posedge Push_Clk or negedge Rst_n) begin
    if (~Rst_n) begin

      // based on rtl, this should be full after reset
      // Fifo_Full_Usr <= 4'b1000;
      Fifo_Full_Usr <= 4'b0001;
    end else begin
      if (match_room4none) begin
        Fifo_Full_Usr <= 4'b0000;
      end else if (match_room4all) begin
        Fifo_Full_Usr <= 4'b0001;
      end else if (~match_room4half) begin
        Fifo_Full_Usr <= 4'b0010;
      end else if (~match_room4quart) begin
        Fifo_Full_Usr <= 4'b0011;
      end else begin
        if (match_room_at_most63) begin
          if (room4_32s) Fifo_Full_Usr <= 4'b1010;
          else if (room4_16s) Fifo_Full_Usr <= 4'b1011;
          else if (room4_8s) Fifo_Full_Usr <= 4'b1100;
          else if (room4_4s) Fifo_Full_Usr <= 4'b1101;
          else if (room4_2s) Fifo_Full_Usr <= 4'b1110;
          else if (room4_1s) Fifo_Full_Usr <= 4'b1111;
          else Fifo_Full_Usr <= 4'b1110;
        end else Fifo_Full_Usr <= 4'b0100;
      end
    end
  end

  always @(posedge Pop_Clk or negedge Rst_n) begin
    if (~Rst_n) begin
      Fifo_Empty_Usr <= 4'b0000;
    end else begin
      if (Fifo_Pop_Flush | (pop_local_flush_mask & ~pop_flush_done) | pop_clk_rst) begin
        Fifo_Empty_Usr <= 4'b0000;
      end else if (match_all_left) begin
        Fifo_Empty_Usr <= 4'b1111;
      end else if (match_half_left) begin
        Fifo_Empty_Usr <= 4'b1110;
      end else if (match_quart_left) begin
        Fifo_Empty_Usr <= 4'b1101;
      end else begin
        if (match_at_most63_left) begin
          if (at_least_32) Fifo_Empty_Usr <= 4'b0110;
          else if (at_least_16) Fifo_Empty_Usr <= 4'b0101;
          else if (at_least_8) Fifo_Empty_Usr <= 4'b0100;
          else if (at_least_4) Fifo_Empty_Usr <= 4'b0011;
          else if (at_least_2) Fifo_Empty_Usr <= 4'b0010;
          else if (one_left) Fifo_Empty_Usr <= 4'b0001;
          else Fifo_Empty_Usr <= 4'b0000;
        end else Fifo_Empty_Usr <= 4'b1000;
      end
    end
  end
endmodule

`timescale 10 ps / 1 ps

//`define ADDRWID 8
`define DATAWID 18
`define WEWID 2
//`define DEPTH 256

module ram (
  AA,
  AB,
  CLKA,
  CLKB,
  WENA,
  WENB,
  CENA,
  CENB,
  WENBA,
  WENBB,
  DA,
  QA,
  DB,
  QB
);

  parameter ADDRWID = 8;
  parameter DEPTH = (1 << ADDRWID);

  parameter [9215:0] INIT = 9216'bx;
  parameter INIT_FILE = "init.mem";
  parameter init_ad = 0;

  parameter data_width_int = 16;
  parameter data_depth_int = 1024;

  output [`DATAWID-1:0] QA;
  input CLKA;
  input CENA;
  input WENA;
  input [`WEWID-1:0] WENBA;
  input [ADDRWID-1:0] AA;
  input [`DATAWID-1:0] DA;
  output [`DATAWID-1:0] QB;

  input CLKB;
  input CENB;
  input WENB;
  input [`WEWID-1:0] WENBB;
  input [ADDRWID-1:0] AB;
  input [`DATAWID-1:0] DB;

  integer i, j, k, l, m, n, o;

  wire CEN1;
  wire OEN1;
  wire WEN1;
  wire [`WEWID-1:0] WENB1;
  wire [ADDRWID-1:0] A1;

  reg [ADDRWID-1:0] AddrOut1;
  wire [`DATAWID-1:0] I1;

  wire CEN2;
  wire OEN2;
  wire WEN2;
  wire [`WEWID-1:0] WENB2;
  wire [ADDRWID-1:0] A2;

  reg [ADDRWID-1:0] AddrOut2;
  wire [`DATAWID-1:0] I2;

  reg [`DATAWID-1:0] O1, QAreg;
  reg [`DATAWID-1:0] O2, QBreg;

  reg WEN1_f;
  reg WEN2_f;
  reg [ADDRWID-1:0] A2_f;
  reg [ADDRWID-1:0] A1_f;

  wire CEN1_SEL;
  wire WEN1_SEL;
  wire [ADDRWID-1:0] A1_SEL;
  wire [`DATAWID-1:0] I1_SEL;
  wire [`WEWID-1:0] WENB1_SEL;

  wire CEN2_SEL;
  wire WEN2_SEL;
  wire [ADDRWID-1:0] A2_SEL;
  wire [`DATAWID-1:0] I2_SEL;
  wire [`WEWID-1:0] WENB2_SEL;
  wire overlap;

  wire CLKA_d, CLKB_d, CEN1_d, CEN2_d;

  assign A1_SEL = AA;
  assign I1_SEL = DA;
  assign CEN1_SEL = CENA;
  assign WEN1_SEL = WENA;
  assign WENB1_SEL = WENBA;

  assign A2_SEL = AB;
  assign I2_SEL = DB;
  assign CEN2_SEL = CENB;
  assign WEN2_SEL = WENB;
  assign WENB2_SEL = WENBB;

  assign CEN1 = CEN1_SEL;
  assign OEN1 = 1'b0;
  assign WEN1 = WEN1_SEL;
  assign WENB1 = WENB1_SEL;
  assign A1 = A1_SEL;
  assign I1 = I1_SEL;

  assign CEN2 = CEN2_SEL;
  assign OEN2 = 1'b0;
  assign WEN2 = WEN2_SEL;
  assign WENB2 = WENB2_SEL;
  assign A2 = A2_SEL;
  assign I2 = I2_SEL;

  //assign QA = O1;
  //assign QB = O2;

  reg [`DATAWID-1:0] ram[DEPTH-1:0];
  reg [data_width_int-1 : 0] ram_dum[data_depth_int-1:0];
  reg [`DATAWID-1:0] wrData1;
  reg [`DATAWID-1:0] wrData2;
  wire [`DATAWID-1:0] tmpData1;
  wire [`DATAWID-1:0] tmpData2;

  reg CENreg1, CENreg2;

  assign #1 CLKA_d = CLKA;
  assign #1 CLKB_d = CLKB;
  // updated by sya 20130523
  assign #2 CEN1_d = CEN1;
  assign #2 CEN2_d = CEN2;

  assign QA = QAreg | O1;
  assign QB = QBreg | O2;

  assign tmpData1 = ram[A1];
  assign tmpData2 = ram[A2];

  assign overlap = (A1_f == A2_f) & WEN1_f & WEN2_f;

  initial begin
`ifndef YOSYS
    $readmemh(INIT_FILE, ram_dum);
`endif
    #10 n = 0;
    o = 0;
    for (i = 0; i < DEPTH; i = i + 1) begin
      if (data_width_int > 16)
        ram[i] <= {
          1'b0,
          ram_dum[i][((16*init_ad)+16)-1:((16*init_ad)+8)],
          1'b0,
          ram_dum[i][((16*init_ad)+8)-1:(16*init_ad)]
        };
      else if (data_width_int <= 8 && data_depth_int <= 1024)
        ram[i] <= {
          1'b0, ram_dum[i+n+1+(1024*init_ad)][7:0], 1'b0, ram_dum[i+n+(1024*init_ad)][7:0]
        };
      else if (data_width_int <= 8 && data_depth_int > 1024)
        ram[i] <= {1'b0, ram_dum[i+o+init_ad+1][7:0], 1'b0, ram_dum[i+o+init_ad][7:0]};
      else if (data_width_int > 8 && data_width_int <= 16 && data_depth_int > 512)
        ram[i] <= {1'b0, ram_dum[i+n+init_ad][15:8], 1'b0, ram_dum[i+n+init_ad][7:0]};
      else ram[i] <= {1'b0, ram_dum[i+(512*init_ad)][15:8], 1'b0, ram_dum[i+(512*init_ad)][7:0]};

      n = n + 1;
      o = o + 3;
    end
  end

  always @(WENB1 or I1 or tmpData1) begin
    for (j = 0; j < 9; j = j + 1) begin
      wrData1[j] <= (WENB1[0]) ? tmpData1[j] : I1[j];
    end
    for (l = 9; l < 19; l = l + 1) begin
      wrData1[l] <= (WENB1[1]) ? tmpData1[l] : I1[l];
    end
  end

  always @(posedge CLKA) begin
    if (~WEN1 & ~CEN1) begin
      ram[A1] <= wrData1[`DATAWID-1:0];
    end
  end

  //pre-charging to 1 every clock cycle
  always @(posedge CLKA_d)
    if (~CEN1_d) begin
      O1 = 18'h3ffff;
      #100;
      O1 = 18'h00000;
    end

  always @(posedge CLKA)
    if (~CEN1) begin
      AddrOut1 <= A1;
    end

  always @(posedge CLKA_d)
    if (~CEN1_d) begin
      QAreg <= ram[AddrOut1];
    end

  always @(posedge CLKA) begin
    WEN1_f <= ~WEN1 & ~CEN1;
    A1_f <= A1;
  end

  always @(WENB2 or I2 or tmpData2) begin
    for (k = 0; k < 9; k = k + 1) begin
      wrData2[k] <= (WENB2[0]) ? tmpData2[k] : I2[k];
    end
    for (m = 9; m < 19; m = m + 1) begin
      wrData2[m] <= (WENB2[1]) ? tmpData2[m] : I2[m];
    end
  end

  always @(posedge CLKB) begin
    if (~WEN2 & ~CEN2) begin
      ram[A2] <= wrData2[`DATAWID-1:0];
    end
  end

  //pre-charging to 1 every clock cycle
  always @(posedge CLKB_d)
    if (~CEN2_d) begin
      O2 = 18'h3ffff;
      #100;
      O2 = 18'h00000;
    end

  always @(posedge CLKB)
    if (~CEN2) begin
      AddrOut2 <= A2;
    end

  always @(posedge CLKB_d)
    if (~CEN2_d) begin
      QBreg <= ram[AddrOut2];
    end

  always @(posedge CLKB) begin
    WEN2_f <= ~WEN2 & ~CEN2;
    A2_f <= A2;

  end

  always @(A1_f or A2_f or overlap) begin
    if (overlap) begin
      ram[A1_f] <= 18'bxxxxxxxxxxxxxxxxxx;
    end
  end

endmodule

`timescale 1 ns / 10 ps
//`define ADDRWID 10
`define DATAWID 18
`define WEWID 2

module x2_model (
  Concat_En,

  ram0_WIDTH_SELA,
  ram0_WIDTH_SELB,
  ram0_PLRD,

  ram0_CEA,
  ram0_CEB,
  ram0_I,
  ram0_O,
  ram0_AA,
  ram0_AB,
  ram0_CSBA,
  ram0_CSBB,
  ram0_WENBA,

  ram1_WIDTH_SELA,
  ram1_WIDTH_SELB,
  ram1_PLRD,

  ram1_CEA,
  ram1_CEB,
  ram1_I,
  ram1_O,
  ram1_AA,
  ram1_AB,
  ram1_CSBA,
  ram1_CSBB,
  ram1_WENBA
);

  parameter ADDRWID = 10;
  parameter [18431:0] INIT = 18432'bx;
  parameter INIT_FILE = "init.mem";
  parameter data_width_int = 16;
  parameter data_depth_int = 1024;
  parameter init_ad1 = 0;
  parameter init_ad2 = (data_depth_int > 1024) ? 2 : 1;

  input Concat_En;

  input [1:0] ram0_WIDTH_SELA;
  input [1:0] ram0_WIDTH_SELB;
  input ram0_PLRD;
  input ram0_CEA;
  input ram0_CEB;
  input [`DATAWID-1:0] ram0_I;
  output [`DATAWID-1:0] ram0_O;
  input [ADDRWID-1:0] ram0_AA;
  input [ADDRWID-1:0] ram0_AB;
  input ram0_CSBA;
  input ram0_CSBB;
  input [`WEWID-1:0] ram0_WENBA;

  input [1:0] ram1_WIDTH_SELA;
  input [1:0] ram1_WIDTH_SELB;
  input ram1_PLRD;
  input ram1_CEA;
  input ram1_CEB;
  input [`DATAWID-1:0] ram1_I;
  output [`DATAWID-1:0] ram1_O;
  input [ADDRWID-1:0] ram1_AA;
  input [ADDRWID-1:0] ram1_AB;
  input ram1_CSBA;
  input ram1_CSBB;
  input [`WEWID-1:0] ram1_WENBA;

  reg ram0_PLRDA_SEL;
  reg ram0_PLRDB_SEL;
  reg ram1_PLRDA_SEL;
  reg ram1_PLRDB_SEL;
  reg ram_AA_ram_SEL;
  reg ram_AB_ram_SEL;

  reg [`WEWID-1:0] ram0_WENBA_SEL;
  reg [`WEWID-1:0] ram0_WENBB_SEL;
  reg [`WEWID-1:0] ram1_WENBA_SEL;
  reg [`WEWID-1:0] ram1_WENBB_SEL;

  reg ram0_A_x9_SEL;
  reg ram0_B_x9_SEL;
  reg ram1_A_x9_SEL;
  reg ram1_B_x9_SEL;

  reg [ADDRWID-3:0] ram0_AA_SEL;
  reg [ADDRWID-3:0] ram0_AB_SEL;
  reg [ADDRWID-3:0] ram1_AA_SEL;
  reg [ADDRWID-3:0] ram1_AB_SEL;

  reg ram0_AA_byte_SEL;
  reg ram0_AB_byte_SEL;
  reg ram1_AA_byte_SEL;
  reg ram1_AB_byte_SEL;

  reg ram0_AA_byte_SEL_Q;
  reg ram0_AB_byte_SEL_Q;
  reg ram1_AA_byte_SEL_Q;
  reg ram1_AB_byte_SEL_Q;
  reg ram0_A_mux_ctl_Q;
  reg ram0_B_mux_ctl_Q;
  reg ram1_A_mux_ctl_Q;
  reg ram1_B_mux_ctl_Q;

  reg ram0_O_mux_ctrl_Q;
  reg ram1_O_mux_ctrl_Q;

  reg ram_AA_ram_SEL_Q;
  reg ram_AB_ram_SEL_Q;

  wire [`DATAWID-1:0] QA_1_SEL3;
  wire [`DATAWID-1:0] QB_0_SEL2;
  wire [`DATAWID-1:0] QB_1_SEL2;

  reg [`DATAWID-1:0] QA_0_Q;
  reg [`DATAWID-1:0] QB_0_Q;
  reg [`DATAWID-1:0] QA_1_Q;
  reg [`DATAWID-1:0] QB_1_Q;

  wire [`DATAWID-1:0] QA_0;
  wire [`DATAWID-1:0] QB_0;
  wire [`DATAWID-1:0] QA_1;
  wire [`DATAWID-1:0] QB_1;

  wire ram0_CSBA_SEL;
  wire ram0_CSBB_SEL;
  wire ram1_CSBA_SEL;
  wire ram1_CSBB_SEL;

  wire [`DATAWID-1:0] ram0_I_SEL1;
  wire [`DATAWID-1:0] ram1_I_SEL1;

  wire dual_port;

  wire ram0_WEBA_SEL;
  wire ram0_WEBB_SEL;
  wire ram1_WEBA_SEL;
  wire ram1_WEBB_SEL;

  wire [`DATAWID-1:0] ram1_I_SEL2;

  wire [`DATAWID-1:0] QA_1_SEL2;
  wire [`DATAWID-1:0] QA_0_SEL1;
  wire [`DATAWID-1:0] QB_0_SEL1;
  wire [`DATAWID-1:0] QA_1_SEL1;
  wire [`DATAWID-1:0] QB_1_SEL1;

  wire [`DATAWID-1:0] QB_0_SEL3;
  wire [`DATAWID-1:0] QA_0_SEL2;

  initial begin
    QA_0_Q <= 0;
    QB_0_Q <= 0;
    QA_1_Q <= 0;
    QB_1_Q <= 0;
    ram0_AA_byte_SEL_Q <= 0;
    ram0_A_mux_ctl_Q <= 0;
    ram0_AB_byte_SEL_Q <= 0;
    ram0_B_mux_ctl_Q <= 0;
    ram1_AA_byte_SEL_Q <= 0;
    ram1_A_mux_ctl_Q <= 0;
    ram1_AB_byte_SEL_Q <= 0;
    ram1_B_mux_ctl_Q <= 0;
    ram_AA_ram_SEL_Q <= 0;
    ram1_O_mux_ctrl_Q <= 0;
    ram_AB_ram_SEL_Q <= 0;
    ram0_O_mux_ctrl_Q <= 0;
  end

  assign dual_port = Concat_En & ~(ram0_WIDTH_SELA[1] | ram0_WIDTH_SELB[1]);

  assign ram0_CSBA_SEL = ram0_CSBA;
  assign ram0_CSBB_SEL = ram0_CSBB;
  assign ram1_CSBA_SEL = Concat_En ? ram0_CSBA : ram1_CSBA;
  assign ram1_CSBB_SEL = Concat_En ? ram0_CSBB : ram1_CSBB;

  assign ram0_O = QB_0_SEL3;
  assign ram1_O = dual_port ? QA_1_SEL3 : QB_1_SEL2;

  assign ram0_I_SEL1[8:0] = ram0_I[8:0];
  assign ram1_I_SEL1[8:0] = ram1_I[8:0];
  assign ram0_I_SEL1[17:9] = ram0_AA_byte_SEL ? ram0_I[8:0] : ram0_I[17:9];
  assign ram1_I_SEL1[17:9]	= ( ( ~Concat_En & ram1_AA_byte_SEL ) | ( dual_port & ram0_AB_byte_SEL ) ) ? ram1_I[8:0] : ram1_I[17:9];

  assign ram1_I_SEL2 = (Concat_En & ~ram0_WIDTH_SELA[1]) ? ram0_I_SEL1 : ram1_I_SEL1;

  assign ram0_WEBA_SEL = &ram0_WENBA_SEL;
  assign ram0_WEBB_SEL = &ram0_WENBB_SEL;
  assign ram1_WEBA_SEL = &ram1_WENBA_SEL;
  assign ram1_WEBB_SEL = &ram1_WENBB_SEL;

  assign QA_0_SEL1 = (ram0_PLRDA_SEL) ? QA_0_Q : QA_0;
  assign QB_0_SEL1 = (ram0_PLRDB_SEL) ? QB_0_Q : QB_0;
  assign QA_1_SEL1 = (ram1_PLRDA_SEL) ? QA_1_Q : QA_1;
  assign QB_1_SEL1 = (ram1_PLRDB_SEL) ? QB_1_Q : QB_1;

  assign QA_1_SEL3 = ram1_O_mux_ctrl_Q ? QA_1_SEL2 : QA_0_SEL2;

  assign QA_0_SEL2[8:0] = ram0_A_mux_ctl_Q ? QA_0_SEL1[17:9] : QA_0_SEL1[8:0];
  assign QB_0_SEL2[8:0] = ram0_B_mux_ctl_Q ? QB_0_SEL1[17:9] : QB_0_SEL1[8:0];
  assign QA_1_SEL2[8:0] = ram1_A_mux_ctl_Q ? QA_1_SEL1[17:9] : QA_1_SEL1[8:0];
  assign QB_1_SEL2[8:0] = ram1_B_mux_ctl_Q ? QB_1_SEL1[17:9] : QB_1_SEL1[8:0];

  assign QA_0_SEL2[17:9] = QA_0_SEL1[17:9];
  assign QB_0_SEL2[17:9] = QB_0_SEL1[17:9];
  assign QA_1_SEL2[17:9] = QA_1_SEL1[17:9];
  assign QB_1_SEL2[17:9] = QB_1_SEL1[17:9];

  assign QB_0_SEL3 = ram0_O_mux_ctrl_Q ? QB_1_SEL2 : QB_0_SEL2;

  always @(posedge ram0_CEA) begin
    QA_0_Q <= QA_0;
  end
  always @(posedge ram0_CEB) begin
    QB_0_Q <= QB_0;
  end
  always @(posedge ram1_CEA) begin
    QA_1_Q <= QA_1;
  end
  always @(posedge ram1_CEB) begin
    QB_1_Q <= QB_1;
  end

  always @(posedge ram0_CEA) begin
    if (ram0_CSBA_SEL == 0) ram0_AA_byte_SEL_Q <= ram0_AA_byte_SEL;
    if (ram0_PLRDA_SEL || (ram0_CSBA_SEL == 0))
      ram0_A_mux_ctl_Q <= ram0_A_x9_SEL & (ram0_PLRDA_SEL ? ram0_AA_byte_SEL_Q : ram0_AA_byte_SEL);
  end

  always @(posedge ram0_CEB) begin
    if (ram0_CSBB_SEL == 0) ram0_AB_byte_SEL_Q <= ram0_AB_byte_SEL;
    if (ram0_PLRDB_SEL || (ram0_CSBB_SEL == 0))
      ram0_B_mux_ctl_Q <= ram0_B_x9_SEL & (ram0_PLRDB_SEL ? ram0_AB_byte_SEL_Q : ram0_AB_byte_SEL);
  end

  always @(posedge ram1_CEA) begin
    if (ram1_CSBA_SEL == 0) ram1_AA_byte_SEL_Q <= ram1_AA_byte_SEL;
    if (ram1_PLRDA_SEL || (ram1_CSBA_SEL == 0))
      ram1_A_mux_ctl_Q <= ram1_A_x9_SEL & (ram1_PLRDA_SEL ? ram1_AA_byte_SEL_Q : ram1_AA_byte_SEL);
  end

  always @(posedge ram1_CEB) begin
    if (ram1_CSBB_SEL == 0) ram1_AB_byte_SEL_Q <= ram1_AB_byte_SEL;
    if (ram1_PLRDB_SEL || (ram1_CSBB_SEL == 0))
      ram1_B_mux_ctl_Q <= ram1_B_x9_SEL & (ram1_PLRDB_SEL ? ram1_AB_byte_SEL_Q : ram1_AB_byte_SEL);
  end

  always @(posedge ram0_CEA) begin
    ram_AA_ram_SEL_Q <= ram_AA_ram_SEL;
    ram1_O_mux_ctrl_Q <= (ram0_PLRDA_SEL ? ram_AA_ram_SEL_Q : ram_AA_ram_SEL);
  end

  always @(posedge ram0_CEB) begin
    ram_AB_ram_SEL_Q <= ram_AB_ram_SEL;
    ram0_O_mux_ctrl_Q <= (ram0_PLRDB_SEL ? ram_AB_ram_SEL_Q : ram_AB_ram_SEL);
  end

  always@( Concat_En or ram0_WIDTH_SELA or ram0_WIDTH_SELB or ram0_AA or ram0_AB or ram0_WENBA or
	         ram1_AA or ram1_AB or ram1_WENBA or ram0_PLRD or ram1_PLRD or ram1_WIDTH_SELA or ram1_WIDTH_SELB )
	begin
    ram0_A_x9_SEL <= (~|ram0_WIDTH_SELA);
    ram1_A_x9_SEL <= (~|ram0_WIDTH_SELA);
    ram0_B_x9_SEL <= (~|ram0_WIDTH_SELB);
    ram0_AA_byte_SEL <= ram0_AA[0] & (~|ram0_WIDTH_SELA);
    ram0_AB_byte_SEL <= ram0_AB[0] & (~|ram0_WIDTH_SELB);
    if (~Concat_En) begin
      ram_AA_ram_SEL <= 1'b0;
      ram_AB_ram_SEL <= 1'b0;
      ram1_B_x9_SEL <= (~|ram1_WIDTH_SELB);

      ram0_PLRDA_SEL <= ram0_PLRD;
      ram0_PLRDB_SEL <= ram0_PLRD;
      ram1_PLRDA_SEL <= ram1_PLRD;
      ram1_PLRDB_SEL <= ram1_PLRD;
      ram0_WENBB_SEL <= {`WEWID{1'b1}};
      ram1_WENBB_SEL <= {`WEWID{1'b1}};

      ram0_AA_SEL <= ram0_AA >> (~|ram0_WIDTH_SELA);
      ram0_WENBA_SEL[0] <= (ram0_AA[0] & (~|ram0_WIDTH_SELA)) | ram0_WENBA[0];
      ram0_WENBA_SEL[1] <= (~ram0_AA[0] & (~|ram0_WIDTH_SELA)) | ram0_WENBA[(|ram0_WIDTH_SELA)];
      ram0_AB_SEL <= ram0_AB >> (~|ram0_WIDTH_SELB);

      ram1_AA_SEL <= ram1_AA >> (~|ram1_WIDTH_SELA);
      ram1_AA_byte_SEL <= ram1_AA[0] & (~|ram1_WIDTH_SELA);
      ram1_WENBA_SEL[0] <= (ram1_AA[0] & (~|ram1_WIDTH_SELA)) | ram1_WENBA[0];
      ram1_WENBA_SEL[1] <= (~ram1_AA[0] & (~|ram1_WIDTH_SELA)) | ram1_WENBA[(|ram1_WIDTH_SELA)];
      ram1_AB_SEL <= ram1_AB >> (~|ram1_WIDTH_SELB);
      ram1_AB_byte_SEL <= ram1_AB[0] & (~|ram1_WIDTH_SELB);
    end else begin
      ram_AA_ram_SEL <= ~ram0_WIDTH_SELA[1] & ram0_AA[~ram0_WIDTH_SELA[0]];
      ram_AB_ram_SEL <= ~ram0_WIDTH_SELB[1] & ram0_AB[~ram0_WIDTH_SELB[0]];
      ram1_B_x9_SEL <= (~|ram0_WIDTH_SELB);

      ram0_PLRDA_SEL <= ram1_PLRD;
      ram1_PLRDA_SEL <= ram1_PLRD;
      ram0_PLRDB_SEL <= ram0_PLRD;
      ram1_PLRDB_SEL <= ram0_PLRD;

      ram0_AA_SEL <= ram0_AA >> {
        ~ram0_WIDTH_SELA[1] & ~(ram0_WIDTH_SELA[1] ^ ram0_WIDTH_SELA[0]),
        ~ram0_WIDTH_SELA[1] & ram0_WIDTH_SELA[0]
      };
      ram1_AA_SEL <= ram0_AA >> {
        ~ram0_WIDTH_SELA[1] & ~(ram0_WIDTH_SELA[1] ^ ram0_WIDTH_SELA[0]),
        ~ram0_WIDTH_SELA[1] & ram0_WIDTH_SELA[0]
      };
      ram1_AA_byte_SEL <= ram0_AA[0] & (~|ram0_WIDTH_SELA);
      ram0_WENBA_SEL[0] <= ram0_WENBA[0] | (~ram0_WIDTH_SELA[1] & (ram0_AA[0] | (~ram0_WIDTH_SELA[0] & ram0_AA[1])));
      ram0_WENBA_SEL[1] <= ((~|ram0_WIDTH_SELA & ram0_WENBA[0]) | (|ram0_WIDTH_SELA & ram0_WENBA[1])) | (~ram0_WIDTH_SELA[1] & ((ram0_WIDTH_SELA[0] & ram0_AA[0]) | (~ram0_WIDTH_SELA[0] & ~ram0_AA[0]) | (~ram0_WIDTH_SELA[0] & ram0_AA[1])));

      ram1_WENBA_SEL[0] <= ((~ram0_WIDTH_SELA[1] & ram0_WENBA[0]) | (ram0_WIDTH_SELA[1] & ram1_WENBA[0])) | (~ram0_WIDTH_SELA[1] & ((ram0_WIDTH_SELA[0] & ~ram0_AA[0]) | (~ram0_WIDTH_SELA[0] & ram0_AA[0]) | (~ram0_WIDTH_SELA[0] & ~ram0_AA[1])));
      ram1_WENBA_SEL[1] <= (((ram0_WIDTH_SELA == 2'b00) & ram0_WENBA[0]) | ((ram0_WIDTH_SELA[1] == 1'b1) & ram1_WENBA[1]) | ((ram0_WIDTH_SELA == 2'b01) & ram0_WENBA[1])) | (~ram0_WIDTH_SELA[1] & (~ram0_AA[0] | (~ram0_WIDTH_SELA[0] & ~ram0_AA[1])));

      ram0_AB_SEL <= ram0_AB >> {
        ~ram0_WIDTH_SELB[1] & ~(ram0_WIDTH_SELB[1] ^ ram0_WIDTH_SELB[0]),
        ~ram0_WIDTH_SELB[1] & ram0_WIDTH_SELB[0]
      };
      ram1_AB_SEL <= ram0_AB >> {
        ~ram0_WIDTH_SELB[1] & ~(ram0_WIDTH_SELB[1] ^ ram0_WIDTH_SELB[0]),
        ~ram0_WIDTH_SELB[1] & ram0_WIDTH_SELB[0]
      };
      ram1_AB_byte_SEL <= ram0_AB[0] & (~|ram0_WIDTH_SELB);
      ram0_WENBB_SEL[0] <= ram0_WIDTH_SELB[1] | (ram0_WIDTH_SELA[1] | ram1_WENBA[0] | (ram0_AB[0] | (~ram0_WIDTH_SELB[0] & ram0_AB[1])));
      ram0_WENBB_SEL[1] <= ram0_WIDTH_SELB[1] | (ram0_WIDTH_SELA[1] | ((~|ram0_WIDTH_SELB & ram1_WENBA[0]) | (|ram0_WIDTH_SELB & ram1_WENBA[1])) | ((ram0_WIDTH_SELB[0] & ram0_AB[0]) | (~ram0_WIDTH_SELB[0] & ~ram0_AB[0]) | (~ram0_WIDTH_SELB[0] & ram0_AB[1])));
      ram1_WENBB_SEL[0] <= ram0_WIDTH_SELB[1] | (ram0_WIDTH_SELA[1] | ram1_WENBA[0] | ((ram0_WIDTH_SELB[0] & ~ram0_AB[0] ) | (~ram0_WIDTH_SELB[0] & ram0_AB[0]) | (~ram0_WIDTH_SELB[0] & ~ram0_AB[1])));
      ram1_WENBB_SEL[1] <= ram0_WIDTH_SELB[1] | (ram0_WIDTH_SELA[1] | ((~|ram0_WIDTH_SELB & ram1_WENBA[0]) | (|ram0_WIDTH_SELB & ram1_WENBA[1])) | (~ram0_AB[0] | (~ram0_WIDTH_SELB[0] & ~ram0_AB[1])));
    end
  end

  ram #(
    .ADDRWID(ADDRWID - 2),
    .INIT(INIT[0*9216 +: 9216]),
    .INIT_FILE(INIT_FILE),
    .data_width_int(data_width_int),
    .data_depth_int(data_depth_int),
    .init_ad(init_ad1)
  ) ram0_inst (
    .AA(ram0_AA_SEL),
    .AB(ram0_AB_SEL),
    .CLKA(ram0_CEA),
    .CLKB(ram0_CEB),
    .WENA(ram0_WEBA_SEL),
    .WENB(ram0_WEBB_SEL),
    .CENA(ram0_CSBA_SEL),
    .CENB(ram0_CSBB_SEL),
    .WENBA(ram0_WENBA_SEL),
    .WENBB(ram0_WENBB_SEL),
    .DA(ram0_I_SEL1),
    .QA(QA_0),
    .DB(ram1_I_SEL1),
    .QB(QB_0)
  );

  ram #(
    .ADDRWID(ADDRWID - 2),
    .INIT(INIT[1*9216 +: 9216]),
    .INIT_FILE(INIT_FILE),
    .data_width_int(data_width_int),
    .data_depth_int(data_depth_int),
    .init_ad(init_ad2)
  ) ram1_inst (
    .AA(ram1_AA_SEL),
    .AB(ram1_AB_SEL),
    .CLKA(ram1_CEA),
    .CLKB(ram1_CEB),
    .WENA(ram1_WEBA_SEL),
    .WENB(ram1_WEBB_SEL),
    .CENA(ram1_CSBA_SEL),
    .CENB(ram1_CSBB_SEL),
    .WENBA(ram1_WENBA_SEL),
    .WENBB(ram1_WENBB_SEL),
    .DA(ram1_I_SEL2),
    .QA(QA_1),
    .DB(ram1_I_SEL1),
    .QB(QB_1)
  );

endmodule

`timescale 1 ns / 10 ps
`define ADDRWID 11
`define DATAWID 18
`define WEWID 2

module ram_block_8K (
  CLK1_0,
  CLK2_0,
  WD_0,
  RD_0,
  A1_0,
  A2_0,
  CS1_0,
  CS2_0,
  WEN1_0,
  POP_0,
  Almost_Full_0,
  Almost_Empty_0,
  PUSH_FLAG_0,
  POP_FLAG_0,

  FIFO_EN_0,
  SYNC_FIFO_0,
  PIPELINE_RD_0,
  WIDTH_SELECT1_0,
  WIDTH_SELECT2_0,

  CLK1_1,
  CLK2_1,
  WD_1,
  RD_1,
  A1_1,
  A2_1,
  CS1_1,
  CS2_1,
  WEN1_1,
  POP_1,
  Almost_Empty_1,
  Almost_Full_1,
  PUSH_FLAG_1,
  POP_FLAG_1,

  FIFO_EN_1,
  SYNC_FIFO_1,
  PIPELINE_RD_1,
  WIDTH_SELECT1_1,
  WIDTH_SELECT2_1,

  CONCAT_EN_0,
  CONCAT_EN_1,

  PUSH_0,
  PUSH_1,
  aFlushN_0,
  aFlushN_1
);

  parameter [18431:0] INIT = 18432'bx;
  parameter INIT_FILE = "init.mem";
  parameter data_width_int = 16;
  parameter data_depth_int = 1024;

  input CLK1_0;
  input CLK2_0;
  input [`DATAWID-1:0] WD_0;
  output [`DATAWID-1:0] RD_0;
  input [`ADDRWID-1:0] A1_0;  //chnge
  input [`ADDRWID-1:0] A2_0;  //chnge
  input CS1_0;
  input CS2_0;
  input [`WEWID-1:0] WEN1_0;
  input POP_0;
  output Almost_Full_0;
  output Almost_Empty_0;
  output [3:0] PUSH_FLAG_0;
  output [3:0] POP_FLAG_0;
  input FIFO_EN_0;
  input SYNC_FIFO_0;
  input PIPELINE_RD_0;
  input [1:0] WIDTH_SELECT1_0;
  input [1:0] WIDTH_SELECT2_0;

  input CLK1_1;
  input CLK2_1;
  input [`DATAWID-1:0] WD_1;
  output [`DATAWID-1:0] RD_1;
  input [`ADDRWID-1:0] A1_1;  //chnge
  input [`ADDRWID-1:0] A2_1;  //chnge
  input CS1_1;
  input CS2_1;
  input [`WEWID-1:0] WEN1_1;
  input POP_1;
  output Almost_Full_1;
  output Almost_Empty_1;
  output [3:0] PUSH_FLAG_1;
  output [3:0] POP_FLAG_1;
  input FIFO_EN_1;
  input SYNC_FIFO_1;
  input PIPELINE_RD_1;
  input [1:0] WIDTH_SELECT1_1;
  input [1:0] WIDTH_SELECT2_1;

  input CONCAT_EN_0;
  input CONCAT_EN_1;


  input PUSH_0;
  input PUSH_1;
  input aFlushN_0;
  input aFlushN_1;

  reg rstn;

  wire [`WEWID-1:0] RAM0_WENb1_SEL;
  wire [`WEWID-1:0] RAM1_WENb1_SEL;

  wire RAM0_CS1_SEL;
  wire RAM0_CS2_SEL;
  wire RAM1_CS1_SEL;
  wire RAM1_CS2_SEL;

  wire [`ADDRWID-1:0] Fifo0_Write_Addr;
  wire [`ADDRWID-1:0] Fifo0_Read_Addr;

  wire [`ADDRWID-1:0] Fifo1_Write_Addr;
  wire [`ADDRWID-1:0] Fifo1_Read_Addr;

  wire [`ADDRWID-1:0] RAM0_AA_SEL;
  wire [`ADDRWID-1:0] RAM0_AB_SEL;
  wire [`ADDRWID-1:0] RAM1_AA_SEL;
  wire [`ADDRWID-1:0] RAM1_AB_SEL;

  wire Concat_En_SEL;

  //  To simulate POR
  initial begin
    rstn = 1'b0;
    #30 rstn = 1'b1;
  end

  assign fifo0_rstn = rstn & aFlushN_0;
  assign fifo1_rstn = rstn & aFlushN_1;

  assign Concat_En_SEL = (CONCAT_EN_0 | WIDTH_SELECT1_0[1] | WIDTH_SELECT2_0[1]) ? 1'b1 : 1'b0;

  assign RAM0_AA_SEL = FIFO_EN_0 ? Fifo0_Write_Addr : A1_0[`ADDRWID-1:0];
  assign RAM0_AB_SEL = FIFO_EN_0 ? Fifo0_Read_Addr : A2_0[`ADDRWID-1:0];
  assign RAM1_AA_SEL = FIFO_EN_1 ? Fifo1_Write_Addr : A1_1[`ADDRWID-1:0];
  assign RAM1_AB_SEL = FIFO_EN_1 ? Fifo1_Read_Addr : A2_1[`ADDRWID-1:0];

  assign RAM0_WENb1_SEL = FIFO_EN_0 ? {`WEWID{~PUSH_0}} : ~WEN1_0;
  assign RAM1_WENb1_SEL = (FIFO_EN_1 & ~Concat_En_SEL) ? {`WEWID{~PUSH_1}} :
                          ((FIFO_EN_0 & Concat_En_SEL) ? (WIDTH_SELECT1_0[1] ? {`WEWID{~PUSH_0}} : {`WEWID{1'b1}}) : ~WEN1_1);

  assign RAM0_CS1_SEL = (FIFO_EN_0 ? CS1_0 : ~CS1_0);
  assign RAM0_CS2_SEL = (FIFO_EN_0 ? CS2_0 : ~CS2_0);
  assign RAM1_CS1_SEL = (FIFO_EN_1 ? CS1_1 : ~CS1_1);
  assign RAM1_CS2_SEL = (FIFO_EN_1 ? CS2_1 : ~CS2_1);

  x2_model #(
    .ADDRWID(`ADDRWID),
    .INIT(INIT),
    .INIT_FILE(INIT_FILE),
    .data_width_int(data_width_int),
    .data_depth_int(data_depth_int)
  ) x2_8K_model_inst (
    .Concat_En(Concat_En_SEL),

    .ram0_WIDTH_SELA(WIDTH_SELECT1_0),
    .ram0_WIDTH_SELB(WIDTH_SELECT2_0),
    .ram0_PLRD(PIPELINE_RD_0),

    .ram0_CEA(CLK1_0),
    .ram0_CEB(CLK2_0),
    .ram0_I(WD_0),
    .ram0_O(RD_0),
    .ram0_AA(RAM0_AA_SEL),
    .ram0_AB(RAM0_AB_SEL),
    .ram0_CSBA(RAM0_CS1_SEL),
    .ram0_CSBB(RAM0_CS2_SEL),
    .ram0_WENBA(RAM0_WENb1_SEL),

    .ram1_WIDTH_SELA(WIDTH_SELECT1_1),
    .ram1_WIDTH_SELB(WIDTH_SELECT2_1),
    .ram1_PLRD(PIPELINE_RD_1),

    .ram1_CEA(CLK1_1),
    .ram1_CEB(CLK2_1),
    .ram1_I(WD_1),
    .ram1_O(RD_1),
    .ram1_AA(RAM1_AA_SEL),
    .ram1_AB(RAM1_AB_SEL),
    .ram1_CSBA(RAM1_CS1_SEL),
    .ram1_CSBB(RAM1_CS2_SEL),
    .ram1_WENBA(RAM1_WENb1_SEL)
  );

  fifo_controller_model #(
    .MAX_PTR_WIDTH(`ADDRWID + 1)
  ) fifo_controller0_inst (
    .Push_Clk(CLK1_0),
    .Pop_Clk(CLK2_0),

    .Fifo_Push(PUSH_0),
    .Fifo_Push_Flush(CS1_0),
    .Fifo_Full(Almost_Full_0),
    .Fifo_Full_Usr(PUSH_FLAG_0),

    .Fifo_Pop(POP_0),
    .Fifo_Pop_Flush(CS2_0),
    .Fifo_Empty(Almost_Empty_0),
    .Fifo_Empty_Usr(POP_FLAG_0),

    .Write_Addr(Fifo0_Write_Addr),

    .Read_Addr(Fifo0_Read_Addr),

    .Fifo_Ram_Mode(Concat_En_SEL),
    .Fifo_Sync_Mode(SYNC_FIFO_0),
    .Fifo_Push_Width(WIDTH_SELECT1_0),
    .Fifo_Pop_Width(WIDTH_SELECT2_0),
    .Rst_n(fifo0_rstn)
  );

  fifo_controller_model #(
    .MAX_PTR_WIDTH(`ADDRWID + 1)
  ) fifo_controller1_inst (
    .Push_Clk(CLK1_1),
    .Pop_Clk(CLK2_1),

    .Fifo_Push(PUSH_1),
    .Fifo_Push_Flush(CS1_1),
    .Fifo_Full(Almost_Full_1),
    .Fifo_Full_Usr(PUSH_FLAG_1),

    .Fifo_Pop(POP_1),
    .Fifo_Pop_Flush(CS2_1),
    .Fifo_Empty(Almost_Empty_1),
    .Fifo_Empty_Usr(POP_FLAG_1),

    .Write_Addr(Fifo1_Write_Addr),

    .Read_Addr(Fifo1_Read_Addr),

    .Fifo_Ram_Mode(1'b0),
    .Fifo_Sync_Mode(SYNC_FIFO_1),
    .Fifo_Push_Width({1'b0, WIDTH_SELECT1_1[0]}),
    .Fifo_Pop_Width({1'b0, WIDTH_SELECT2_1[0]}),
    .Rst_n(fifo1_rstn)
  );

endmodule

module sw_mux (
  port_out,
  default_port,
  alt_port,
  switch
);

  output port_out;
  input default_port;
  input alt_port;
  input switch;

  assign port_out = switch ? alt_port : default_port;

endmodule


`define ADDRWID_8k2 11
`define DATAWID 18
`define WEWID 2

module ram8k_2x1_cell (
  CLK1_0,
  CLK2_0,
  CLK1S_0,
  CLK2S_0,
  WD_0,
  RD_0,
  A1_0,
  A2_0,
  CS1_0,
  CS2_0,
  WEN1_0,
  CLK1EN_0,
  CLK2EN_0,
  P1_0,
  P2_0,
  Almost_Full_0,
  Almost_Empty_0,
  PUSH_FLAG_0,
  POP_FLAG_0,

  FIFO_EN_0,
  SYNC_FIFO_0,
  PIPELINE_RD_0,
  WIDTH_SELECT1_0,
  WIDTH_SELECT2_0,
  DIR_0,
  ASYNC_FLUSH_0,
  ASYNC_FLUSH_S0,

  CLK1_1,
  CLK2_1,
  CLK1S_1,
  CLK2S_1,
  WD_1,
  RD_1,
  A1_1,
  A2_1,
  CS1_1,
  CS2_1,
  WEN1_1,
  CLK1EN_1,
  CLK2EN_1,
  P1_1,
  P2_1,
  Almost_Empty_1,
  Almost_Full_1,
  PUSH_FLAG_1,
  POP_FLAG_1,

  FIFO_EN_1,
  SYNC_FIFO_1,
  PIPELINE_RD_1,
  WIDTH_SELECT1_1,
  WIDTH_SELECT2_1,
  DIR_1,
  ASYNC_FLUSH_1,
  ASYNC_FLUSH_S1,

  CONCAT_EN_0,
  CONCAT_EN_1
);

  parameter [18431:0] INIT = 18432'bx;
  parameter INIT_FILE = "init.mem";
  parameter data_width_int = 16;
  parameter data_depth_int = 1024;

  input CLK1_0;
  input CLK2_0;
  input CLK1S_0;
  input CLK2S_0;
  input [`DATAWID-1:0] WD_0;
  output [`DATAWID-1:0] RD_0;
  input [`ADDRWID_8k2-1:0] A1_0;
  input [`ADDRWID_8k2-1:0] A2_0;
  input CS1_0;
  input CS2_0;
  input [`WEWID-1:0] WEN1_0;
  input CLK1EN_0;
  input CLK2EN_0;
  input P1_0;
  input P2_0;
  output Almost_Full_0;
  output Almost_Empty_0;
  output [3:0] PUSH_FLAG_0;
  output [3:0] POP_FLAG_0;
  input FIFO_EN_0;
  input SYNC_FIFO_0;
  input DIR_0;
  input ASYNC_FLUSH_0;
  input ASYNC_FLUSH_S0;
  input PIPELINE_RD_0;
  input [1:0] WIDTH_SELECT1_0;
  input [1:0] WIDTH_SELECT2_0;

  input CLK1_1;
  input CLK2_1;
  input CLK1S_1;
  input CLK2S_1;
  input [`DATAWID-1:0] WD_1;
  output [`DATAWID-1:0] RD_1;
  input [`ADDRWID_8k2-1:0] A1_1;
  input [`ADDRWID_8k2-1:0] A2_1;
  input CS1_1;
  input CS2_1;
  input [`WEWID-1:0] WEN1_1;
  input CLK1EN_1;
  input CLK2EN_1;
  input P1_1;
  input P2_1;
  output Almost_Full_1;
  output Almost_Empty_1;
  output [3:0] PUSH_FLAG_1;
  output [3:0] POP_FLAG_1;
  input FIFO_EN_1;
  input SYNC_FIFO_1;
  input DIR_1;
  input ASYNC_FLUSH_1;
  input ASYNC_FLUSH_S1;
  input PIPELINE_RD_1;
  input [1:0] WIDTH_SELECT1_1;
  input [1:0] WIDTH_SELECT2_1;

  input CONCAT_EN_0;
  input CONCAT_EN_1;

  //CODE here
  reg RAM0_domain_sw;
  reg RAM1_domain_sw;

  wire CLK1P_0, CLK1P_1, CLK2P_0, CLK2P_1, ASYNC_FLUSHP_1, ASYNC_FLUSHP_0;

  assign WidSel1_1 = WIDTH_SELECT1_0[1];
  assign WidSel2_1 = WIDTH_SELECT2_0[1];

  assign CLK1P_0 = CLK1S_0 ? ~CLK1_0 : CLK1_0;
  assign CLK1P_1 = CLK1S_1 ? ~CLK1_1 : CLK1_1;
  assign CLK2P_0 = CLK2S_0 ? ~CLK2_0 : CLK2_0;
  assign CLK2P_1 = CLK2S_1 ? ~CLK2_1 : CLK2_1;
  assign ASYNC_FLUSHP_0 = ASYNC_FLUSH_S0 ? ~ASYNC_FLUSH_0 : ASYNC_FLUSH_0;
  assign ASYNC_FLUSHP_1 = ASYNC_FLUSH_S1 ? ~ASYNC_FLUSH_1 : ASYNC_FLUSH_1;


  /* FIFO mode-only switching */
  always @(CONCAT_EN_0 or FIFO_EN_0 or FIFO_EN_1 or WidSel1_1 or WidSel2_1 or DIR_0 or DIR_1) begin
    if (CONCAT_EN_0)  //CONCAT enabled, only RAM0 ports are checked
    begin
      if (~FIFO_EN_0)  //RAM MODE (no switching)
      begin
        RAM0_domain_sw = 1'b0;  //Both Switches are on default during RAM mode
        RAM1_domain_sw = 1'b0;
      end
    else  //FIFO Mode
      begin
        RAM0_domain_sw = DIR_0;  //Both Switches will get DIR_0 (primary port) during concat
        RAM1_domain_sw = DIR_0;
      end
    end
  else  //CONCAT disabled, RAM0 and RAM1 ports are be checked
    begin
      if (WidSel1_1 || WidSel2_1)  //AUTO-CONCAT FIFO/RAM Mode Horizontal Concatenation
        begin
        if (~FIFO_EN_0)  //RAM MODE (no switching)
          begin
          RAM0_domain_sw = 1'b0;  //Both Switches are on default during RAM mode
          RAM1_domain_sw = 1'b0;
        end
        else  //FIFO Mode
          begin
          RAM0_domain_sw = DIR_0;  //Both Switches will get DIR_0 (primary port) during concat
          RAM1_domain_sw = DIR_0;
        end
      end
      else  //FIFO/RAM Individual Mode
        begin
        if (~FIFO_EN_0)  //RAM0 Mode
          RAM0_domain_sw = 1'b0;
        else  //FIFO0 Mode
          RAM0_domain_sw = DIR_0;
        if (~FIFO_EN_1)  //RAM1 Mode
          RAM1_domain_sw = 1'b0;
        else  //FIFO1 Mode
          RAM1_domain_sw = DIR_1;
      end
    end
  end

  assign RAM0_Clk1_gated = CLK1EN_0 & CLK1P_0;
  assign RAM0_Clk2_gated = CLK2EN_0 & CLK2P_0;
  assign RAM1_Clk1_gated = CLK1EN_1 & CLK1P_1;
  assign RAM1_Clk2_gated = CLK2EN_1 & CLK2P_1;

  //PORT1 of RAMs is designated to PUSH circuitry, while PORT2 gets POP circuitry
  sw_mux RAM0_clk_sw_port1 (
    .port_out(RAM0_clk_port1),
    .default_port(RAM0_Clk1_gated),
    .alt_port(RAM0_Clk2_gated),
    .switch(RAM0_domain_sw)
  );
  sw_mux RAM0_P_sw_port1 (
    .port_out(RAM0_push_port1),
    .default_port(P1_0),
    .alt_port(P2_0),
    .switch(RAM0_domain_sw)
  );
  sw_mux RAM0_Flush_sw_port1 (
    .port_out(RAM0CS_Sync_Flush_port1),
    .default_port(CS1_0),
    .alt_port(CS2_0),
    .switch(RAM0_domain_sw)
  );
  sw_mux RAM0_WidSel0_port1 (
    .port_out(RAM0_Wid_Sel0_port1),
    .default_port(WIDTH_SELECT1_0[0]),
    .alt_port(WIDTH_SELECT2_0[0]),
    .switch(RAM0_domain_sw)
  );
  sw_mux RAM0_WidSel1_port1 (
    .port_out(RAM0_Wid_Sel1_port1),
    .default_port(WIDTH_SELECT1_0[1]),
    .alt_port(WIDTH_SELECT2_0[1]),
    .switch(RAM0_domain_sw)
  );

  sw_mux RAM0_clk_sw_port2 (
    .port_out(RAM0_clk_port2),
    .default_port(RAM0_Clk2_gated),
    .alt_port(RAM0_Clk1_gated),
    .switch(RAM0_domain_sw)
  );
  sw_mux RAM0_P_sw_port2 (
    .port_out(RAM0_pop_port2),
    .default_port(P2_0),
    .alt_port(P1_0),
    .switch(RAM0_domain_sw)
  );
  sw_mux RAM0_Flush_sw_port2 (
    .port_out(RAM0CS_Sync_Flush_port2),
    .default_port(CS2_0),
    .alt_port(CS1_0),
    .switch(RAM0_domain_sw)
  );
  sw_mux RAM0_WidSel0_port2 (
    .port_out(RAM0_Wid_Sel0_port2),
    .default_port(WIDTH_SELECT2_0[0]),
    .alt_port(WIDTH_SELECT1_0[0]),
    .switch(RAM0_domain_sw)
  );
  sw_mux RAM0_WidSel1_port2 (
    .port_out(RAM0_Wid_Sel1_port2),
    .default_port(WIDTH_SELECT2_0[1]),
    .alt_port(WIDTH_SELECT1_0[1]),
    .switch(RAM0_domain_sw)
  );

  sw_mux RAM1_clk_sw_port1 (
    .port_out(RAM1_clk_port1),
    .default_port(RAM1_Clk1_gated),
    .alt_port(RAM1_Clk2_gated),
    .switch(RAM1_domain_sw)
  );
  sw_mux RAM1_P_sw_port1 (
    .port_out(RAM1_push_port1),
    .default_port(P1_1),
    .alt_port(P2_1),
    .switch(RAM1_domain_sw)
  );
  sw_mux RAM1_Flush_sw_port1 (
    .port_out(RAM1CS_Sync_Flush_port1),
    .default_port(CS1_1),
    .alt_port(CS2_1),
    .switch(RAM1_domain_sw)
  );
  sw_mux RAM1_WidSel0_port1 (
    .port_out(RAM1_Wid_Sel0_port1),
    .default_port(WIDTH_SELECT1_1[0]),
    .alt_port(WIDTH_SELECT2_1[0]),
    .switch(RAM1_domain_sw)
  );
  sw_mux RAM1_WidSel1_port1 (
    .port_out(RAM1_Wid_Sel1_port1),
    .default_port(WIDTH_SELECT1_1[1]),
    .alt_port(WIDTH_SELECT2_1[1]),
    .switch(RAM1_domain_sw)
  );


  sw_mux RAM1_clk_sw_port2 (
    .port_out(RAM1_clk_port2),
    .default_port(RAM1_Clk2_gated),
    .alt_port(RAM1_Clk1_gated),
    .switch(RAM1_domain_sw)
  );
  sw_mux RAM1_P_sw_port2 (
    .port_out(RAM1_pop_port2),
    .default_port(P2_1),
    .alt_port(P1_1),
    .switch(RAM1_domain_sw)
  );
  sw_mux RAM1_Flush_sw_port2 (
    .port_out(RAM1CS_Sync_Flush_port2),
    .default_port(CS2_1),
    .alt_port(CS1_1),
    .switch(RAM1_domain_sw)
  );
  sw_mux RAM1_WidSel0_port2 (
    .port_out(RAM1_Wid_Sel0_port2),
    .default_port(WIDTH_SELECT2_1[0]),
    .alt_port(WIDTH_SELECT1_1[0]),
    .switch(RAM1_domain_sw)
  );
  sw_mux RAM1_WidSel1_port2 (
    .port_out(RAM1_Wid_Sel1_port2),
    .default_port(WIDTH_SELECT2_1[1]),
    .alt_port(WIDTH_SELECT1_1[1]),
    .switch(RAM1_domain_sw)
  );

  ram_block_8K #(
    .INIT(INIT),
    .INIT_FILE(INIT_FILE),
    .data_width_int(data_width_int),
    .data_depth_int(data_depth_int)
  ) ram_block_8K_inst (
    .CLK1_0(RAM0_clk_port1),
    .CLK2_0(RAM0_clk_port2),
    .WD_0(WD_0),
    .RD_0(RD_0),
    .A1_0(A1_0),
    .A2_0(A2_0),
    .CS1_0(RAM0CS_Sync_Flush_port1),
    .CS2_0(RAM0CS_Sync_Flush_port2),
    .WEN1_0(WEN1_0),
    .POP_0(RAM0_pop_port2),
    .Almost_Full_0(Almost_Full_0),
    .Almost_Empty_0(Almost_Empty_0),
    .PUSH_FLAG_0(PUSH_FLAG_0),
    .POP_FLAG_0(POP_FLAG_0),

    .FIFO_EN_0(FIFO_EN_0),
    .SYNC_FIFO_0(SYNC_FIFO_0),
    .PIPELINE_RD_0(PIPELINE_RD_0),
    .WIDTH_SELECT1_0({RAM0_Wid_Sel1_port1, RAM0_Wid_Sel0_port1}),
    .WIDTH_SELECT2_0({RAM0_Wid_Sel1_port2, RAM0_Wid_Sel0_port2}),

    .CLK1_1(RAM1_clk_port1),
    .CLK2_1(RAM1_clk_port2),
    .WD_1(WD_1),
    .RD_1(RD_1),
    .A1_1(A1_1),
    .A2_1(A2_1),
    .CS1_1(RAM1CS_Sync_Flush_port1),
    .CS2_1(RAM1CS_Sync_Flush_port2),
    .WEN1_1(WEN1_1),
    .POP_1(RAM1_pop_port2),
    .Almost_Empty_1(Almost_Empty_1),
    .Almost_Full_1(Almost_Full_1),
    .PUSH_FLAG_1(PUSH_FLAG_1),
    .POP_FLAG_1(POP_FLAG_1),

    .FIFO_EN_1(FIFO_EN_1),
    .SYNC_FIFO_1(SYNC_FIFO_1),
    .PIPELINE_RD_1(PIPELINE_RD_1),
    .WIDTH_SELECT1_1({RAM1_Wid_Sel1_port1, RAM1_Wid_Sel0_port1}),
    .WIDTH_SELECT2_1({RAM1_Wid_Sel1_port2, RAM1_Wid_Sel0_port2}),

    .CONCAT_EN_0(CONCAT_EN_0),
    .CONCAT_EN_1(CONCAT_EN_1),

    .PUSH_0(RAM0_push_port1),
    .PUSH_1(RAM1_push_port1),
    .aFlushN_0(~ASYNC_FLUSHP_0),
    .aFlushN_1(~ASYNC_FLUSHP_1)
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

  ram8k_2x1_cell #(
    .INIT(INIT),
    .INIT_FILE(INIT_FILE),
    .data_width_int(data_width_int),
    .data_depth_int(data_depth_int)
  ) I1 (
    .A1_0({A1_0[10:0]}),
    .A1_1({A1_1[10:0]}),
    .A2_0({A2_0[10:0]}),
    .A2_1({A2_1[10:0]}),
    .Almost_Empty_0(Almost_Empty_0),
    .Almost_Empty_1(Almost_Empty_1),
    .Almost_Full_0(Almost_Full_0),
    .Almost_Full_1(Almost_Full_1),
    .ASYNC_FLUSH_0(ASYNC_FLUSH_0),
    .ASYNC_FLUSH_1(ASYNC_FLUSH_1),
    .ASYNC_FLUSH_S0(ASYNC_FLUSH_S0),
    .ASYNC_FLUSH_S1(ASYNC_FLUSH_S1),
    .CLK1_0(CLK1_0),
    .CLK1_1(CLK1_1),
    .CLK1EN_0(CLK1EN_0),
    .CLK1EN_1(CLK1EN_1),
    .CLK1S_0(CLK1S_0),
    .CLK1S_1(CLK1S_1),
    .CLK2_0(CLK2_0),
    .CLK2_1(CLK2_1),
    .CLK2EN_0(CLK2EN_0),
    .CLK2EN_1(CLK2EN_1),
    .CLK2S_0(CLK2S_0),
    .CLK2S_1(CLK2S_1),
    .CONCAT_EN_0(CONCAT_EN_0),
    .CONCAT_EN_1(CONCAT_EN_1),
    .CS1_0(CS1_0),
    .CS1_1(CS1_1),
    .CS2_0(CS2_0),
    .CS2_1(CS2_1),
    .DIR_0(DIR_0),
    .DIR_1(DIR_1),
    .FIFO_EN_0(FIFO_EN_0),
    .FIFO_EN_1(FIFO_EN_1),
    .P1_0(P1_0),
    .P1_1(P1_1),
    .P2_0(P2_0),
    .P2_1(P2_1),
    .PIPELINE_RD_0(PIPELINE_RD_0),
    .PIPELINE_RD_1(PIPELINE_RD_1),
    .POP_FLAG_0({POP_FLAG_0[3:0]}),
    .POP_FLAG_1({POP_FLAG_1[3:0]}),
    .PUSH_FLAG_0({PUSH_FLAG_0[3:0]}),
    .PUSH_FLAG_1({PUSH_FLAG_1[3:0]}),
    .RD_0({RD_0[17:0]}),
    .RD_1({RD_1[17:0]}),
    .SYNC_FIFO_0(SYNC_FIFO_0),
    .SYNC_FIFO_1(SYNC_FIFO_1),
    .WD_0({WD_0[17:0]}),
    .WD_1({WD_1[17:0]}),
    .WEN1_0({WEN1_0[1:0]}),
    .WEN1_1({WEN1_1[1:0]}),
    .WIDTH_SELECT1_0({WIDTH_SELECT1_0[1:0]}),
    .WIDTH_SELECT1_1({WIDTH_SELECT1_1[1:0]}),
    .WIDTH_SELECT2_0({WIDTH_SELECT2_0[1:0]}),
    .WIDTH_SELECT2_1({WIDTH_SELECT2_1[1:0]})
  );

endmodule  /* ram8k_2x1_cell_macro */

(* blackbox *)
module gpio_cell_macro (

  ESEL,
  IE,
  OSEL,
  OQI,
  OQE,
  DS,
  FIXHOLD,
  IZ,
  IQZ,
  IQE,
  IQC,
  IQCS,
  IQR,
  WPD,
  INEN,
  IP
);

  input ESEL;
  input IE;
  input OSEL;
  input OQI;
  input OQE;
  input DS;
  input FIXHOLD;
  output IZ;
  output IQZ;
  input IQE;
  input IQC;
  input IQCS;
  input INEN;
  input IQR;
  input WPD;
  inout IP;

  reg EN_reg, OQ_reg, IQZ;
  wire AND_OUT;

  assign rstn = ~IQR;
  assign IQCP = IQCS ? ~IQC : IQC;

  always @(posedge IQCP or negedge rstn)
    if (~rstn) EN_reg <= 1'b0;
    else EN_reg <= IE;

  always @(posedge IQCP or negedge rstn)
    if (~rstn) OQ_reg <= 1'b0;
    else if (OQE) OQ_reg <= OQI;

  always @(posedge IQCP or negedge rstn)
    if (~rstn) IQZ <= 1'b0;
    else if (IQE) IQZ <= AND_OUT;

  assign IZ = AND_OUT;
  assign AND_OUT = INEN ? IP : 1'b0;
  assign EN = ESEL ? IE : EN_reg;
  assign OQ = OSEL ? OQI : OQ_reg;
  assign IP = EN ? OQ : 1'bz;

endmodule

(* blackbox *)
module qlal4s3_mult_32x32_cell (
  input [31:0] Amult,
  input [31:0] Bmult,
  input [1:0] Valid_mult,
  output [63:0] Cmult
);

endmodule  /* qlal4s3_32x32_mult_cell */

(* blackbox *)
module qlal4s3_mult_16x16_cell (
  input [15:0] Amult,
  input [15:0] Bmult,
  input [1:0] Valid_mult,
  output [31:0] Cmult
);

endmodule  /* qlal4s3_16x16_mult_cell */


/* Verilog model of QLAL4S3 Multiplier */
/*qlal4s3_mult_cell*/
module signed_mult (
  A,
  B,
  Valid,
  C
);

  parameter WIDTH = 32;
  parameter CWIDTH = 2 * WIDTH;

  input [WIDTH-1:0] A, B;
  input Valid;
  output [CWIDTH-1:0] C;

  reg signed [WIDTH-1:0] A_q, B_q;
  wire signed [CWIDTH-1:0] C_int;

  assign C_int = A_q * B_q;
  assign valid_int = Valid;
  assign C = C_int;

  always @(*) if (valid_int == 1'b1) A_q <= A;

  always @(*) if (valid_int == 1'b1) B_q <= B;

endmodule

(* abc9_box, blackbox *)
module qlal4s3_mult_cell_macro (
  Amult,
  Bmult,
  Valid_mult,
  sel_mul_32x32,
  Cmult
);

  input [31:0] Amult;
  input [31:0] Bmult;
  input [1:0] Valid_mult;
  input sel_mul_32x32;
  output [63:0] Cmult;

  specify
    (Amult[0] => Cmult[0]) = 4872; // Amult0 -> Cmult0
    (Bmult[0] => Cmult[0]) = 4349; // Bmult0 -> Cmult0
    (Amult[0] => Cmult[1]) = 5295; // Amult0 -> Cmult1
    (Bmult[0] => Cmult[1]) = 5010; // Bmult0 -> Cmult1
    (Amult[0] => Cmult[2]) = 6250; // Amult0 -> Cmult2
    (Bmult[0] => Cmult[2]) = 5707; // Bmult0 -> Cmult2
    (Amult[0] => Cmult[3]) = 6539; // Amult0 -> Cmult3
    (Bmult[0] => Cmult[3]) = 5870; // Bmult0 -> Cmult3
    (Amult[0] => Cmult[4]) = 7098; // Amult0 -> Cmult4
    (Bmult[0] => Cmult[4]) = 6425; // Bmult0 -> Cmult4
    (Amult[0] => Cmult[5]) = 8154; // Amult0 -> Cmult5
    (Bmult[0] => Cmult[5]) = 7091; // Bmult0 -> Cmult5
    (Amult[0] => Cmult[6]) = 8932; // Amult0 -> Cmult6
    (Bmult[0] => Cmult[6]) = 7539; // Bmult0 -> Cmult6
    (Amult[0] => Cmult[7]) = 9042; // Amult0 -> Cmult7
    (Bmult[0] => Cmult[7]) = 8226; // Bmult0 -> Cmult7
    (Amult[0] => Cmult[8]) = 10391; // Amult0 -> Cmult8
    (Bmult[0] => Cmult[8]) = 9011; // Bmult0 -> Cmult8
    (Amult[0] => Cmult[9]) = 10712; // Amult0 -> Cmult9
    (Bmult[0] => Cmult[9]) = 9504; // Bmult0 -> Cmult9
    (Amult[0] => Cmult[10]) = 11412; // Amult0 -> Cmult10
    (Bmult[0] => Cmult[10]) = 10192; // Bmult0 -> Cmult10
    (Amult[0] => Cmult[11]) = 11858; // Amult0 -> Cmult11
    (Bmult[0] => Cmult[11]) = 10626; // Bmult0 -> Cmult11
    (Amult[0] => Cmult[12]) = 12329; // Amult0 -> Cmult12
    (Bmult[0] => Cmult[12]) = 10865; // Bmult0 -> Cmult12
    (Amult[0] => Cmult[13]) = 13232; // Amult0 -> Cmult13
    (Bmult[0] => Cmult[13]) = 11571; // Bmult0 -> Cmult13
    (Amult[0] => Cmult[14]) = 13760; // Amult0 -> Cmult14
    (Bmult[0] => Cmult[14]) = 11998; // Bmult0 -> Cmult14
    (Amult[0] => Cmult[15]) = 15290; // Amult0 -> Cmult15
    (Bmult[0] => Cmult[15]) = 13178; // Bmult0 -> Cmult15
    (Amult[0] => Cmult[16]) = 15142; // Amult0 -> Cmult16
    (Bmult[0] => Cmult[16]) = 13295; // Bmult0 -> Cmult16
    (Amult[0] => Cmult[17]) = 15523; // Amult0 -> Cmult17
    (Bmult[0] => Cmult[17]) = 13710; // Bmult0 -> Cmult17
    (Amult[0] => Cmult[18]) = 15779; // Amult0 -> Cmult18
    (Bmult[0] => Cmult[18]) = 13372; // Bmult0 -> Cmult18
    (Amult[0] => Cmult[19]) = 16105; // Amult0 -> Cmult19
    (Bmult[0] => Cmult[19]) = 13563; // Bmult0 -> Cmult19
    (Amult[0] => Cmult[20]) = 16528; // Amult0 -> Cmult20
    (Bmult[0] => Cmult[20]) = 13906; // Bmult0 -> Cmult20
    (Amult[0] => Cmult[21]) = 16848; // Amult0 -> Cmult21
    (Bmult[0] => Cmult[21]) = 14152; // Bmult0 -> Cmult21
    (Amult[0] => Cmult[22]) = 17103; // Amult0 -> Cmult22
    (Bmult[0] => Cmult[22]) = 14506; // Bmult0 -> Cmult22
    (Amult[0] => Cmult[23]) = 17316; // Amult0 -> Cmult23
    (Bmult[0] => Cmult[23]) = 14716; // Bmult0 -> Cmult23
    (Amult[0] => Cmult[24]) = 17187; // Amult0 -> Cmult24
    (Bmult[0] => Cmult[24]) = 15103; // Bmult0 -> Cmult24
    (Amult[0] => Cmult[25]) = 17455; // Amult0 -> Cmult25
    (Bmult[0] => Cmult[25]) = 15370; // Bmult0 -> Cmult25
    (Amult[0] => Cmult[26]) = 18145; // Amult0 -> Cmult26
    (Bmult[0] => Cmult[26]) = 15790; // Bmult0 -> Cmult26
    (Amult[0] => Cmult[27]) = 18346; // Amult0 -> Cmult27
    (Bmult[0] => Cmult[27]) = 16074; // Bmult0 -> Cmult27
    (Amult[0] => Cmult[28]) = 18605; // Amult0 -> Cmult28
    (Bmult[0] => Cmult[28]) = 16634; // Bmult0 -> Cmult28
    (Amult[0] => Cmult[29]) = 18949; // Amult0 -> Cmult29
    (Bmult[0] => Cmult[29]) = 17014; // Bmult0 -> Cmult29
    (Amult[0] => Cmult[30]) = 19627; // Amult0 -> Cmult30
    (Bmult[0] => Cmult[30]) = 17583; // Bmult0 -> Cmult30
    (Amult[0] => Cmult[31]) = 20434; // Amult0 -> Cmult31
    (Bmult[0] => Cmult[31]) = 18437; // Bmult0 -> Cmult31
    (Amult[0] => Cmult[32]) = 25982; // Amult0 -> Cmult32
    (Bmult[0] => Cmult[32]) = 22634; // Bmult0 -> Cmult32
    (Amult[0] => Cmult[33]) = 26319; // Amult0 -> Cmult33
    (Bmult[0] => Cmult[33]) = 22888; // Bmult0 -> Cmult33
    (Amult[0] => Cmult[34]) = 26594; // Amult0 -> Cmult34
    (Bmult[0] => Cmult[34]) = 23211; // Bmult0 -> Cmult34
    (Amult[0] => Cmult[35]) = 26844; // Amult0 -> Cmult35
    (Bmult[0] => Cmult[35]) = 23363; // Bmult0 -> Cmult35
    (Amult[0] => Cmult[36]) = 27001; // Amult0 -> Cmult36
    (Bmult[0] => Cmult[36]) = 23696; // Bmult0 -> Cmult36
    (Amult[0] => Cmult[37]) = 27161; // Amult0 -> Cmult37
    (Bmult[0] => Cmult[37]) = 23882; // Bmult0 -> Cmult37
    (Amult[0] => Cmult[38]) = 27478; // Amult0 -> Cmult38
    (Bmult[0] => Cmult[38]) = 24229; // Bmult0 -> Cmult38
    (Amult[0] => Cmult[39]) = 27779; // Amult0 -> Cmult39
    (Bmult[0] => Cmult[39]) = 24399; // Bmult0 -> Cmult39
    (Amult[0] => Cmult[40]) = 27994; // Amult0 -> Cmult40
    (Bmult[0] => Cmult[40]) = 24736; // Bmult0 -> Cmult40
    (Amult[0] => Cmult[41]) = 28229; // Amult0 -> Cmult41
    (Bmult[0] => Cmult[41]) = 24916; // Bmult0 -> Cmult41
    (Amult[0] => Cmult[42]) = 27662; // Amult0 -> Cmult42
    (Bmult[0] => Cmult[42]) = 24400; // Bmult0 -> Cmult42
    (Amult[0] => Cmult[43]) = 28352; // Amult0 -> Cmult43
    (Bmult[0] => Cmult[43]) = 25001; // Bmult0 -> Cmult43
    (Amult[0] => Cmult[44]) = 28870; // Amult0 -> Cmult44
    (Bmult[0] => Cmult[44]) = 25695; // Bmult0 -> Cmult44
    (Amult[0] => Cmult[45]) = 28967; // Amult0 -> Cmult45
    (Bmult[0] => Cmult[45]) = 25622; // Bmult0 -> Cmult45
    (Amult[0] => Cmult[46]) = 28357; // Amult0 -> Cmult46
    (Bmult[0] => Cmult[46]) = 25179; // Bmult0 -> Cmult46
    (Amult[0] => Cmult[47]) = 28300; // Amult0 -> Cmult47
    (Bmult[0] => Cmult[47]) = 24989; // Bmult0 -> Cmult47
    (Amult[0] => Cmult[48]) = 29279; // Amult0 -> Cmult48
    (Bmult[0] => Cmult[48]) = 26026; // Bmult0 -> Cmult48
    (Amult[0] => Cmult[49]) = 29115; // Amult0 -> Cmult49
    (Bmult[0] => Cmult[49]) = 25852; // Bmult0 -> Cmult49
    (Amult[0] => Cmult[50]) = 29889; // Amult0 -> Cmult50
    (Bmult[0] => Cmult[50]) = 26596; // Bmult0 -> Cmult50
    (Amult[0] => Cmult[51]) = 30116; // Amult0 -> Cmult51
    (Bmult[0] => Cmult[51]) = 26947; // Bmult0 -> Cmult51
    (Amult[0] => Cmult[52]) = 30735; // Amult0 -> Cmult52
    (Bmult[0] => Cmult[52]) = 27409; // Bmult0 -> Cmult52
    (Amult[0] => Cmult[53]) = 31067; // Amult0 -> Cmult53
    (Bmult[0] => Cmult[53]) = 27899; // Bmult0 -> Cmult53
    (Amult[0] => Cmult[54]) = 31392; // Amult0 -> Cmult54
    (Bmult[0] => Cmult[54]) = 28157; // Bmult0 -> Cmult54
    (Amult[0] => Cmult[55]) = 31604; // Amult0 -> Cmult55
    (Bmult[0] => Cmult[55]) = 28435; // Bmult0 -> Cmult55
    (Amult[0] => Cmult[56]) = 32073; // Amult0 -> Cmult56
    (Bmult[0] => Cmult[56]) = 28710; // Bmult0 -> Cmult56
    (Amult[0] => Cmult[57]) = 32359; // Amult0 -> Cmult57
    (Bmult[0] => Cmult[57]) = 29153; // Bmult0 -> Cmult57
    (Amult[0] => Cmult[58]) = 32817; // Amult0 -> Cmult58
    (Bmult[0] => Cmult[58]) = 29517; // Bmult0 -> Cmult58
    (Amult[0] => Cmult[59]) = 32885; // Amult0 -> Cmult59
    (Bmult[0] => Cmult[59]) = 29687; // Bmult0 -> Cmult59
    (Amult[0] => Cmult[60]) = 33447; // Amult0 -> Cmult60
    (Bmult[0] => Cmult[60]) = 30110; // Bmult0 -> Cmult60
    (Amult[0] => Cmult[61]) = 33532; // Amult0 -> Cmult61
    (Bmult[0] => Cmult[61]) = 30363; // Bmult0 -> Cmult61
    (Amult[0] => Cmult[62]) = 34244; // Amult0 -> Cmult62
    (Bmult[0] => Cmult[62]) = 30844; // Bmult0 -> Cmult62
    (Amult[0] => Cmult[63]) = 35339; // Amult0 -> Cmult63
    (Bmult[0] => Cmult[63]) = 31936; // Bmult0 -> Cmult63
    (Amult[1] => Cmult[1]) = 5408; // Amult1 -> Cmult1
    (Bmult[1] => Cmult[1]) = 5012; // Bmult1 -> Cmult1
    (Amult[1] => Cmult[2]) = 6490; // Amult1 -> Cmult2
    (Bmult[1] => Cmult[2]) = 5998; // Bmult1 -> Cmult2
    (Amult[1] => Cmult[3]) = 6767; // Amult1 -> Cmult3
    (Bmult[1] => Cmult[3]) = 6258; // Bmult1 -> Cmult3
    (Amult[1] => Cmult[4]) = 7470; // Amult1 -> Cmult4
    (Bmult[1] => Cmult[4]) = 6721; // Bmult1 -> Cmult4
    (Amult[1] => Cmult[5]) = 8398; // Amult1 -> Cmult5
    (Bmult[1] => Cmult[5]) = 7383; // Bmult1 -> Cmult5
    (Amult[1] => Cmult[6]) = 9281; // Amult1 -> Cmult6
    (Bmult[1] => Cmult[6]) = 7827; // Bmult1 -> Cmult6
    (Amult[1] => Cmult[7]) = 9472; // Amult1 -> Cmult7
    (Bmult[1] => Cmult[7]) = 8516; // Bmult1 -> Cmult7
    (Amult[1] => Cmult[8]) = 10829; // Amult1 -> Cmult8
    (Bmult[1] => Cmult[8]) = 9292; // Bmult1 -> Cmult8
    (Amult[1] => Cmult[9]) = 11136; // Amult1 -> Cmult9
    (Bmult[1] => Cmult[9]) = 9817; // Bmult1 -> Cmult9
    (Amult[1] => Cmult[10]) = 11561; // Amult1 -> Cmult10
    (Bmult[1] => Cmult[10]) = 10465; // Bmult1 -> Cmult10
    (Amult[1] => Cmult[11]) = 12105; // Amult1 -> Cmult11
    (Bmult[1] => Cmult[11]) = 10895; // Bmult1 -> Cmult11
    (Amult[1] => Cmult[12]) = 12679; // Amult1 -> Cmult12
    (Bmult[1] => Cmult[12]) = 11145; // Bmult1 -> Cmult12
    (Amult[1] => Cmult[13]) = 13520; // Amult1 -> Cmult13
    (Bmult[1] => Cmult[13]) = 11832; // Bmult1 -> Cmult13
    (Amult[1] => Cmult[14]) = 14048; // Amult1 -> Cmult14
    (Bmult[1] => Cmult[14]) = 12260; // Bmult1 -> Cmult14
    (Amult[1] => Cmult[15]) = 15613; // Amult1 -> Cmult15
    (Bmult[1] => Cmult[15]) = 13605; // Bmult1 -> Cmult15
    (Amult[1] => Cmult[16]) = 15514; // Amult1 -> Cmult16
    (Bmult[1] => Cmult[16]) = 13779; // Bmult1 -> Cmult16
    (Amult[1] => Cmult[17]) = 15705; // Amult1 -> Cmult17
    (Bmult[1] => Cmult[17]) = 14160; // Bmult1 -> Cmult17
    (Amult[1] => Cmult[18]) = 16067; // Amult1 -> Cmult18
    (Bmult[1] => Cmult[18]) = 13767; // Bmult1 -> Cmult18
    (Amult[1] => Cmult[19]) = 16393; // Amult1 -> Cmult19
    (Bmult[1] => Cmult[19]) = 13908; // Bmult1 -> Cmult19
    (Amult[1] => Cmult[20]) = 16816; // Amult1 -> Cmult20
    (Bmult[1] => Cmult[20]) = 14353; // Bmult1 -> Cmult20
    (Amult[1] => Cmult[21]) = 17136; // Amult1 -> Cmult21
    (Bmult[1] => Cmult[21]) = 14560; // Bmult1 -> Cmult21
    (Amult[1] => Cmult[22]) = 17391; // Amult1 -> Cmult22
    (Bmult[1] => Cmult[22]) = 14898; // Bmult1 -> Cmult22
    (Amult[1] => Cmult[23]) = 17604; // Amult1 -> Cmult23
    (Bmult[1] => Cmult[23]) = 15065; // Bmult1 -> Cmult23
    (Amult[1] => Cmult[24]) = 17476; // Amult1 -> Cmult24
    (Bmult[1] => Cmult[24]) = 15472; // Bmult1 -> Cmult24
    (Amult[1] => Cmult[25]) = 17743; // Amult1 -> Cmult25
    (Bmult[1] => Cmult[25]) = 15876; // Bmult1 -> Cmult25
    (Amult[1] => Cmult[26]) = 18433; // Amult1 -> Cmult26
    (Bmult[1] => Cmult[26]) = 16154; // Bmult1 -> Cmult26
    (Amult[1] => Cmult[27]) = 18635; // Amult1 -> Cmult27
    (Bmult[1] => Cmult[27]) = 16543; // Bmult1 -> Cmult27
    (Amult[1] => Cmult[28]) = 18893; // Amult1 -> Cmult28
    (Bmult[1] => Cmult[28]) = 17066; // Bmult1 -> Cmult28
    (Amult[1] => Cmult[29]) = 19237; // Amult1 -> Cmult29
    (Bmult[1] => Cmult[29]) = 17505; // Bmult1 -> Cmult29
    (Amult[1] => Cmult[30]) = 19915; // Amult1 -> Cmult30
    (Bmult[1] => Cmult[30]) = 18071; // Bmult1 -> Cmult30
    (Amult[1] => Cmult[31]) = 20722; // Amult1 -> Cmult31
    (Bmult[1] => Cmult[31]) = 18881; // Bmult1 -> Cmult31
    (Amult[1] => Cmult[32]) = 26095; // Amult1 -> Cmult32
    (Bmult[1] => Cmult[32]) = 23108; // Bmult1 -> Cmult32
    (Amult[1] => Cmult[33]) = 26417; // Amult1 -> Cmult33
    (Bmult[1] => Cmult[33]) = 23361; // Bmult1 -> Cmult33
    (Amult[1] => Cmult[34]) = 26691; // Amult1 -> Cmult34
    (Bmult[1] => Cmult[34]) = 23626; // Bmult1 -> Cmult34
    (Amult[1] => Cmult[35]) = 26942; // Amult1 -> Cmult35
    (Bmult[1] => Cmult[35]) = 23778; // Bmult1 -> Cmult35
    (Amult[1] => Cmult[36]) = 27112; // Amult1 -> Cmult36
    (Bmult[1] => Cmult[36]) = 24040; // Bmult1 -> Cmult36
    (Amult[1] => Cmult[37]) = 27211; // Amult1 -> Cmult37
    (Bmult[1] => Cmult[37]) = 24187; // Bmult1 -> Cmult37
    (Amult[1] => Cmult[38]) = 27590; // Amult1 -> Cmult38
    (Bmult[1] => Cmult[38]) = 24565; // Bmult1 -> Cmult38
    (Amult[1] => Cmult[39]) = 27891; // Amult1 -> Cmult39
    (Bmult[1] => Cmult[39]) = 24817; // Bmult1 -> Cmult39
    (Amult[1] => Cmult[40]) = 28095; // Amult1 -> Cmult40
    (Bmult[1] => Cmult[40]) = 25096; // Bmult1 -> Cmult40
    (Amult[1] => Cmult[41]) = 28341; // Amult1 -> Cmult41
    (Bmult[1] => Cmult[41]) = 25261; // Bmult1 -> Cmult41
    (Amult[1] => Cmult[42]) = 27773; // Amult1 -> Cmult42
    (Bmult[1] => Cmult[42]) = 24783; // Bmult1 -> Cmult42
    (Amult[1] => Cmult[43]) = 28463; // Amult1 -> Cmult43
    (Bmult[1] => Cmult[43]) = 25472; // Bmult1 -> Cmult43
    (Amult[1] => Cmult[44]) = 28921; // Amult1 -> Cmult44
    (Bmult[1] => Cmult[44]) = 25989; // Bmult1 -> Cmult44
    (Amult[1] => Cmult[45]) = 29079; // Amult1 -> Cmult45
    (Bmult[1] => Cmult[45]) = 26088; // Bmult1 -> Cmult45
    (Amult[1] => Cmult[46]) = 28469; // Amult1 -> Cmult46
    (Bmult[1] => Cmult[46]) = 25478; // Bmult1 -> Cmult46
    (Amult[1] => Cmult[47]) = 28411; // Amult1 -> Cmult47
    (Bmult[1] => Cmult[47]) = 25325; // Bmult1 -> Cmult47
    (Amult[1] => Cmult[48]) = 29390; // Amult1 -> Cmult48
    (Bmult[1] => Cmult[48]) = 26400; // Bmult1 -> Cmult48
    (Amult[1] => Cmult[49]) = 29226; // Amult1 -> Cmult49
    (Bmult[1] => Cmult[49]) = 26146; // Bmult1 -> Cmult49
    (Amult[1] => Cmult[50]) = 30000; // Amult1 -> Cmult50
    (Bmult[1] => Cmult[50]) = 27022; // Bmult1 -> Cmult50
    (Amult[1] => Cmult[51]) = 30193; // Amult1 -> Cmult51
    (Bmult[1] => Cmult[51]) = 27247; // Bmult1 -> Cmult51
    (Amult[1] => Cmult[52]) = 30846; // Amult1 -> Cmult52
    (Bmult[1] => Cmult[52]) = 27868; // Bmult1 -> Cmult52
    (Amult[1] => Cmult[53]) = 31118; // Amult1 -> Cmult53
    (Bmult[1] => Cmult[53]) = 28199; // Bmult1 -> Cmult53
    (Amult[1] => Cmult[54]) = 31503; // Amult1 -> Cmult54
    (Bmult[1] => Cmult[54]) = 28525; // Bmult1 -> Cmult54
    (Amult[1] => Cmult[55]) = 31655; // Amult1 -> Cmult55
    (Bmult[1] => Cmult[55]) = 28736; // Bmult1 -> Cmult55
    (Amult[1] => Cmult[56]) = 32184; // Amult1 -> Cmult56
    (Bmult[1] => Cmult[56]) = 29206; // Bmult1 -> Cmult56
    (Amult[1] => Cmult[57]) = 32470; // Amult1 -> Cmult57
    (Bmult[1] => Cmult[57]) = 29491; // Bmult1 -> Cmult57
    (Amult[1] => Cmult[58]) = 32928; // Amult1 -> Cmult58
    (Bmult[1] => Cmult[58]) = 29949; // Bmult1 -> Cmult58
    (Amult[1] => Cmult[59]) = 32997; // Amult1 -> Cmult59
    (Bmult[1] => Cmult[59]) = 30018; // Bmult1 -> Cmult59
    (Amult[1] => Cmult[60]) = 33559; // Amult1 -> Cmult60
    (Bmult[1] => Cmult[60]) = 30580; // Bmult1 -> Cmult60
    (Amult[1] => Cmult[61]) = 33582; // Amult1 -> Cmult61
    (Bmult[1] => Cmult[61]) = 30663; // Bmult1 -> Cmult61
    (Amult[1] => Cmult[62]) = 34355; // Amult1 -> Cmult62
    (Bmult[1] => Cmult[62]) = 31375; // Bmult1 -> Cmult62
    (Amult[1] => Cmult[63]) = 35450; // Amult1 -> Cmult63
    (Bmult[1] => Cmult[63]) = 32469; // Bmult1 -> Cmult63
    (Amult[2] => Cmult[2]) = 6007; // Amult2 -> Cmult2
    (Bmult[2] => Cmult[2]) = 6032; // Bmult2 -> Cmult2
    (Amult[2] => Cmult[3]) = 6209; // Amult2 -> Cmult3
    (Bmult[2] => Cmult[3]) = 6377; // Bmult2 -> Cmult3
    (Amult[2] => Cmult[4]) = 6895; // Amult2 -> Cmult4
    (Bmult[2] => Cmult[4]) = 6848; // Bmult2 -> Cmult4
    (Amult[2] => Cmult[5]) = 7784; // Amult2 -> Cmult5
    (Bmult[2] => Cmult[5]) = 7568; // Bmult2 -> Cmult5
    (Amult[2] => Cmult[6]) = 8701; // Amult2 -> Cmult6
    (Bmult[2] => Cmult[6]) = 8023; // Bmult2 -> Cmult6
    (Amult[2] => Cmult[7]) = 8892; // Amult2 -> Cmult7
    (Bmult[2] => Cmult[7]) = 8770; // Bmult2 -> Cmult7
    (Amult[2] => Cmult[8]) = 10272; // Amult2 -> Cmult8
    (Bmult[2] => Cmult[8]) = 9515; // Bmult2 -> Cmult8
    (Amult[2] => Cmult[9]) = 10730; // Amult2 -> Cmult9
    (Bmult[2] => Cmult[9]) = 10069; // Bmult2 -> Cmult9
    (Amult[2] => Cmult[10]) = 11045; // Amult2 -> Cmult10
    (Bmult[2] => Cmult[10]) = 10591; // Bmult2 -> Cmult10
    (Amult[2] => Cmult[11]) = 11666; // Amult2 -> Cmult11
    (Bmult[2] => Cmult[11]) = 11080; // Bmult2 -> Cmult11
    (Amult[2] => Cmult[12]) = 12256; // Amult2 -> Cmult12
    (Bmult[2] => Cmult[12]) = 11409; // Bmult2 -> Cmult12
    (Amult[2] => Cmult[13]) = 12759; // Amult2 -> Cmult13
    (Bmult[2] => Cmult[13]) = 12074; // Bmult2 -> Cmult13
    (Amult[2] => Cmult[14]) = 13409; // Amult2 -> Cmult14
    (Bmult[2] => Cmult[14]) = 12600; // Bmult2 -> Cmult14
    (Amult[2] => Cmult[15]) = 15103; // Amult2 -> Cmult15
    (Bmult[2] => Cmult[15]) = 13797; // Bmult2 -> Cmult15
    (Amult[2] => Cmult[16]) = 15003; // Amult2 -> Cmult16
    (Bmult[2] => Cmult[16]) = 13970; // Bmult2 -> Cmult16
    (Amult[2] => Cmult[17]) = 15095; // Amult2 -> Cmult17
    (Bmult[2] => Cmult[17]) = 14352; // Bmult2 -> Cmult17
    (Amult[2] => Cmult[18]) = 15429; // Amult2 -> Cmult18
    (Bmult[2] => Cmult[18]) = 13959; // Bmult2 -> Cmult18
    (Amult[2] => Cmult[19]) = 15755; // Amult2 -> Cmult19
    (Bmult[2] => Cmult[19]) = 14200; // Bmult2 -> Cmult19
    (Amult[2] => Cmult[20]) = 16197; // Amult2 -> Cmult20
    (Bmult[2] => Cmult[20]) = 14544; // Bmult2 -> Cmult20
    (Amult[2] => Cmult[21]) = 16498; // Amult2 -> Cmult21
    (Bmult[2] => Cmult[21]) = 14730; // Bmult2 -> Cmult21
    (Amult[2] => Cmult[22]) = 16797; // Amult2 -> Cmult22
    (Bmult[2] => Cmult[22]) = 15133; // Bmult2 -> Cmult22
    (Amult[2] => Cmult[23]) = 16966; // Amult2 -> Cmult23
    (Bmult[2] => Cmult[23]) = 15419; // Bmult2 -> Cmult23
    (Amult[2] => Cmult[24]) = 16849; // Amult2 -> Cmult24
    (Bmult[2] => Cmult[24]) = 15826; // Bmult2 -> Cmult24
    (Amult[2] => Cmult[25]) = 17105; // Amult2 -> Cmult25
    (Bmult[2] => Cmult[25]) = 16229; // Bmult2 -> Cmult25
    (Amult[2] => Cmult[26]) = 17868; // Amult2 -> Cmult26
    (Bmult[2] => Cmult[26]) = 16508; // Bmult2 -> Cmult26
    (Amult[2] => Cmult[27]) = 17997; // Amult2 -> Cmult27
    (Bmult[2] => Cmult[27]) = 16896; // Bmult2 -> Cmult27
    (Amult[2] => Cmult[28]) = 18261; // Amult2 -> Cmult28
    (Bmult[2] => Cmult[28]) = 17420; // Bmult2 -> Cmult28
    (Amult[2] => Cmult[29]) = 18599; // Amult2 -> Cmult29
    (Bmult[2] => Cmult[29]) = 17858; // Bmult2 -> Cmult29
    (Amult[2] => Cmult[30]) = 19277; // Amult2 -> Cmult30
    (Bmult[2] => Cmult[30]) = 18424; // Bmult2 -> Cmult30
    (Amult[2] => Cmult[31]) = 20084; // Amult2 -> Cmult31
    (Bmult[2] => Cmult[31]) = 19235; // Bmult2 -> Cmult31
    (Amult[2] => Cmult[32]) = 25227; // Amult2 -> Cmult32
    (Bmult[2] => Cmult[32]) = 23404; // Bmult2 -> Cmult32
    (Amult[2] => Cmult[33]) = 25481; // Amult2 -> Cmult33
    (Bmult[2] => Cmult[33]) = 23657; // Bmult2 -> Cmult33
    (Amult[2] => Cmult[34]) = 25723; // Amult2 -> Cmult34
    (Bmult[2] => Cmult[34]) = 23978; // Bmult2 -> Cmult34
    (Amult[2] => Cmult[35]) = 25898; // Amult2 -> Cmult35
    (Bmult[2] => Cmult[35]) = 24131; // Bmult2 -> Cmult35
    (Amult[2] => Cmult[36]) = 26243; // Amult2 -> Cmult36
    (Bmult[2] => Cmult[36]) = 24366; // Bmult2 -> Cmult36
    (Amult[2] => Cmult[37]) = 26451; // Amult2 -> Cmult37
    (Bmult[2] => Cmult[37]) = 24481; // Bmult2 -> Cmult37
    (Amult[2] => Cmult[38]) = 26693; // Amult2 -> Cmult38
    (Bmult[2] => Cmult[38]) = 24843; // Bmult2 -> Cmult38
    (Amult[2] => Cmult[39]) = 26936; // Amult2 -> Cmult39
    (Bmult[2] => Cmult[39]) = 25144; // Bmult2 -> Cmult39
    (Amult[2] => Cmult[40]) = 27284; // Amult2 -> Cmult40
    (Bmult[2] => Cmult[40]) = 25354; // Bmult2 -> Cmult40
    (Amult[2] => Cmult[41]) = 27386; // Amult2 -> Cmult41
    (Bmult[2] => Cmult[41]) = 25588; // Bmult2 -> Cmult41
    (Amult[2] => Cmult[42]) = 26933; // Amult2 -> Cmult42
    (Bmult[2] => Cmult[42]) = 25041; // Bmult2 -> Cmult42
    (Amult[2] => Cmult[43]) = 27508; // Amult2 -> Cmult43
    (Bmult[2] => Cmult[43]) = 25731; // Bmult2 -> Cmult43
    (Amult[2] => Cmult[44]) = 28160; // Amult2 -> Cmult44
    (Bmult[2] => Cmult[44]) = 26173; // Bmult2 -> Cmult44
    (Amult[2] => Cmult[45]) = 28124; // Amult2 -> Cmult45
    (Bmult[2] => Cmult[45]) = 26347; // Bmult2 -> Cmult45
    (Amult[2] => Cmult[46]) = 27644; // Amult2 -> Cmult46
    (Bmult[2] => Cmult[46]) = 25736; // Bmult2 -> Cmult46
    (Amult[2] => Cmult[47]) = 27457; // Amult2 -> Cmult47
    (Bmult[2] => Cmult[47]) = 25652; // Bmult2 -> Cmult47
    (Amult[2] => Cmult[48]) = 28523; // Amult2 -> Cmult48
    (Bmult[2] => Cmult[48]) = 26658; // Bmult2 -> Cmult48
    (Amult[2] => Cmult[49]) = 28317; // Amult2 -> Cmult49
    (Bmult[2] => Cmult[49]) = 26458; // Bmult2 -> Cmult49
    (Amult[2] => Cmult[50]) = 29055; // Amult2 -> Cmult50
    (Bmult[2] => Cmult[50]) = 27280; // Bmult2 -> Cmult50
    (Amult[2] => Cmult[51]) = 29406; // Amult2 -> Cmult51
    (Bmult[2] => Cmult[51]) = 27472; // Bmult2 -> Cmult51
    (Amult[2] => Cmult[52]) = 29892; // Amult2 -> Cmult52
    (Bmult[2] => Cmult[52]) = 28126; // Bmult2 -> Cmult52
    (Amult[2] => Cmult[53]) = 30357; // Amult2 -> Cmult53
    (Bmult[2] => Cmult[53]) = 28383; // Bmult2 -> Cmult53
    (Amult[2] => Cmult[54]) = 30636; // Amult2 -> Cmult54
    (Bmult[2] => Cmult[54]) = 28783; // Bmult2 -> Cmult54
    (Amult[2] => Cmult[55]) = 30894; // Amult2 -> Cmult55
    (Bmult[2] => Cmult[55]) = 28920; // Bmult2 -> Cmult55
    (Amult[2] => Cmult[56]) = 31230; // Amult2 -> Cmult56
    (Bmult[2] => Cmult[56]) = 29464; // Bmult2 -> Cmult56
    (Amult[2] => Cmult[57]) = 31612; // Amult2 -> Cmult57
    (Bmult[2] => Cmult[57]) = 29750; // Bmult2 -> Cmult57
    (Amult[2] => Cmult[58]) = 31976; // Amult2 -> Cmult58
    (Bmult[2] => Cmult[58]) = 30208; // Bmult2 -> Cmult58
    (Amult[2] => Cmult[59]) = 32146; // Amult2 -> Cmult59
    (Bmult[2] => Cmult[59]) = 30276; // Bmult2 -> Cmult59
    (Amult[2] => Cmult[60]) = 32604; // Amult2 -> Cmult60
    (Bmult[2] => Cmult[60]) = 30839; // Bmult2 -> Cmult60
    (Amult[2] => Cmult[61]) = 32822; // Amult2 -> Cmult61
    (Bmult[2] => Cmult[61]) = 30847; // Bmult2 -> Cmult61
    (Amult[2] => Cmult[62]) = 33401; // Amult2 -> Cmult62
    (Bmult[2] => Cmult[62]) = 31633; // Bmult2 -> Cmult62
    (Amult[2] => Cmult[63]) = 34496; // Amult2 -> Cmult63
    (Bmult[2] => Cmult[63]) = 32727; // Bmult2 -> Cmult63
    (Amult[3] => Cmult[3]) = 5925; // Amult3 -> Cmult3
    (Bmult[3] => Cmult[3]) = 5396; // Bmult3 -> Cmult3
    (Amult[3] => Cmult[4]) = 6479; // Amult3 -> Cmult4
    (Bmult[3] => Cmult[4]) = 6192; // Bmult3 -> Cmult4
    (Amult[3] => Cmult[5]) = 7154; // Amult3 -> Cmult5
    (Bmult[3] => Cmult[5]) = 6995; // Bmult3 -> Cmult5
    (Amult[3] => Cmult[6]) = 7891; // Amult3 -> Cmult6
    (Bmult[3] => Cmult[6]) = 7689; // Bmult3 -> Cmult6
    (Amult[3] => Cmult[7]) = 8415; // Amult3 -> Cmult7
    (Bmult[3] => Cmult[7]) = 8126; // Bmult3 -> Cmult7
    (Amult[3] => Cmult[8]) = 9467; // Amult3 -> Cmult8
    (Bmult[3] => Cmult[8]) = 8923; // Bmult3 -> Cmult8
    (Amult[3] => Cmult[9]) = 9896; // Amult3 -> Cmult9
    (Bmult[3] => Cmult[9]) = 9424; // Bmult3 -> Cmult9
    (Amult[3] => Cmult[10]) = 10639; // Amult3 -> Cmult10
    (Bmult[3] => Cmult[10]) = 10109; // Bmult3 -> Cmult10
    (Amult[3] => Cmult[11]) = 11243; // Amult3 -> Cmult11
    (Bmult[3] => Cmult[11]) = 10541; // Bmult3 -> Cmult11
    (Amult[3] => Cmult[12]) = 11529; // Amult3 -> Cmult12
    (Bmult[3] => Cmult[12]) = 10832; // Bmult3 -> Cmult12
    (Amult[3] => Cmult[13]) = 12274; // Amult3 -> Cmult13
    (Bmult[3] => Cmult[13]) = 11563; // Bmult3 -> Cmult13
    (Amult[3] => Cmult[14]) = 12847; // Amult3 -> Cmult14
    (Bmult[3] => Cmult[14]) = 12034; // Bmult3 -> Cmult14
    (Amult[3] => Cmult[15]) = 14256; // Amult3 -> Cmult15
    (Bmult[3] => Cmult[15]) = 13354; // Bmult3 -> Cmult15
    (Amult[3] => Cmult[16]) = 14327; // Amult3 -> Cmult16
    (Bmult[3] => Cmult[16]) = 13528; // Bmult3 -> Cmult16
    (Amult[3] => Cmult[17]) = 14708; // Amult3 -> Cmult17
    (Bmult[3] => Cmult[17]) = 13909; // Bmult3 -> Cmult17
    (Amult[3] => Cmult[18]) = 14762; // Amult3 -> Cmult18
    (Bmult[3] => Cmult[18]) = 13668; // Bmult3 -> Cmult18
    (Amult[3] => Cmult[19]) = 15043; // Amult3 -> Cmult19
    (Bmult[3] => Cmult[19]) = 13994; // Bmult3 -> Cmult19
    (Amult[3] => Cmult[20]) = 15556; // Amult3 -> Cmult20
    (Bmult[3] => Cmult[20]) = 14417; // Bmult3 -> Cmult20
    (Amult[3] => Cmult[21]) = 15802; // Amult3 -> Cmult21
    (Bmult[3] => Cmult[21]) = 14737; // Bmult3 -> Cmult21
    (Amult[3] => Cmult[22]) = 16155; // Amult3 -> Cmult22
    (Bmult[3] => Cmult[22]) = 14992; // Bmult3 -> Cmult22
    (Amult[3] => Cmult[23]) = 16259; // Amult3 -> Cmult23
    (Bmult[3] => Cmult[23]) = 15205; // Bmult3 -> Cmult23
    (Amult[3] => Cmult[24]) = 16188; // Amult3 -> Cmult24
    (Bmult[3] => Cmult[24]) = 15228; // Bmult3 -> Cmult24
    (Amult[3] => Cmult[25]) = 16426; // Amult3 -> Cmult25
    (Bmult[3] => Cmult[25]) = 15631; // Bmult3 -> Cmult25
    (Amult[3] => Cmult[26]) = 17226; // Amult3 -> Cmult26
    (Bmult[3] => Cmult[26]) = 16073; // Bmult3 -> Cmult26
    (Amult[3] => Cmult[27]) = 17199; // Amult3 -> Cmult27
    (Bmult[3] => Cmult[27]) = 16298; // Bmult3 -> Cmult27
    (Amult[3] => Cmult[28]) = 17676; // Amult3 -> Cmult28
    (Bmult[3] => Cmult[28]) = 16822; // Bmult3 -> Cmult28
    (Amult[3] => Cmult[29]) = 18057; // Amult3 -> Cmult29
    (Bmult[3] => Cmult[29]) = 17260; // Bmult3 -> Cmult29
    (Amult[3] => Cmult[30]) = 18626; // Amult3 -> Cmult30
    (Bmult[3] => Cmult[30]) = 17826; // Bmult3 -> Cmult30
    (Amult[3] => Cmult[31]) = 19480; // Amult3 -> Cmult31
    (Bmult[3] => Cmult[31]) = 18637; // Bmult3 -> Cmult31
    (Amult[3] => Cmult[32]) = 24993; // Amult3 -> Cmult32
    (Bmult[3] => Cmult[32]) = 23648; // Bmult3 -> Cmult32
    (Amult[3] => Cmult[33]) = 25247; // Amult3 -> Cmult33
    (Bmult[3] => Cmult[33]) = 23901; // Bmult3 -> Cmult33
    (Amult[3] => Cmult[34]) = 25486; // Amult3 -> Cmult34
    (Bmult[3] => Cmult[34]) = 24179; // Bmult3 -> Cmult34
    (Amult[3] => Cmult[35]) = 25667; // Amult3 -> Cmult35
    (Bmult[3] => Cmult[35]) = 24332; // Bmult3 -> Cmult35
    (Amult[3] => Cmult[36]) = 25863; // Amult3 -> Cmult36
    (Bmult[3] => Cmult[36]) = 24517; // Bmult3 -> Cmult36
    (Amult[3] => Cmult[37]) = 25934; // Amult3 -> Cmult37
    (Bmult[3] => Cmult[37]) = 24661; // Bmult3 -> Cmult37
    (Amult[3] => Cmult[38]) = 26015; // Amult3 -> Cmult38
    (Bmult[3] => Cmult[38]) = 24991; // Bmult3 -> Cmult38
    (Amult[3] => Cmult[39]) = 26315; // Amult3 -> Cmult39
    (Bmult[3] => Cmult[39]) = 25293; // Bmult3 -> Cmult39
    (Amult[3] => Cmult[40]) = 26789; // Amult3 -> Cmult40
    (Bmult[3] => Cmult[40]) = 25510; // Bmult3 -> Cmult40
    (Amult[3] => Cmult[41]) = 26765; // Amult3 -> Cmult41
    (Bmult[3] => Cmult[41]) = 25737; // Bmult3 -> Cmult41
    (Amult[3] => Cmult[42]) = 26255; // Amult3 -> Cmult42
    (Bmult[3] => Cmult[42]) = 25154; // Bmult3 -> Cmult42
    (Amult[3] => Cmult[43]) = 26887; // Amult3 -> Cmult43
    (Bmult[3] => Cmult[43]) = 25813; // Bmult3 -> Cmult43
    (Amult[3] => Cmult[44]) = 27482; // Amult3 -> Cmult44
    (Bmult[3] => Cmult[44]) = 26333; // Bmult3 -> Cmult44
    (Amult[3] => Cmult[45]) = 27503; // Amult3 -> Cmult45
    (Bmult[3] => Cmult[45]) = 26428; // Bmult3 -> Cmult45
    (Amult[3] => Cmult[46]) = 26966; // Amult3 -> Cmult46
    (Bmult[3] => Cmult[46]) = 25818; // Bmult3 -> Cmult46
    (Amult[3] => Cmult[47]) = 26836; // Amult3 -> Cmult47
    (Bmult[3] => Cmult[47]) = 25801; // Bmult3 -> Cmult47
    (Amult[3] => Cmult[48]) = 27845; // Amult3 -> Cmult48
    (Bmult[3] => Cmult[48]) = 26740; // Bmult3 -> Cmult48
    (Amult[3] => Cmult[49]) = 27650; // Amult3 -> Cmult49
    (Bmult[3] => Cmult[49]) = 26606; // Bmult3 -> Cmult49
    (Amult[3] => Cmult[50]) = 28424; // Amult3 -> Cmult50
    (Bmult[3] => Cmult[50]) = 27362; // Bmult3 -> Cmult50
    (Amult[3] => Cmult[51]) = 28728; // Amult3 -> Cmult51
    (Bmult[3] => Cmult[51]) = 27591; // Bmult3 -> Cmult51
    (Amult[3] => Cmult[52]) = 29381; // Amult3 -> Cmult52
    (Bmult[3] => Cmult[52]) = 28208; // Bmult3 -> Cmult52
    (Amult[3] => Cmult[53]) = 29679; // Amult3 -> Cmult53
    (Bmult[3] => Cmult[53]) = 28543; // Bmult3 -> Cmult53
    (Amult[3] => Cmult[54]) = 29958; // Amult3 -> Cmult54
    (Bmult[3] => Cmult[54]) = 28865; // Bmult3 -> Cmult54
    (Amult[3] => Cmult[55]) = 30216; // Amult3 -> Cmult55
    (Bmult[3] => Cmult[55]) = 29080; // Bmult3 -> Cmult55
    (Amult[3] => Cmult[56]) = 30690; // Amult3 -> Cmult56
    (Bmult[3] => Cmult[56]) = 29546; // Bmult3 -> Cmult56
    (Amult[3] => Cmult[57]) = 30934; // Amult3 -> Cmult57
    (Bmult[3] => Cmult[57]) = 29831; // Bmult3 -> Cmult57
    (Amult[3] => Cmult[58]) = 31352; // Amult3 -> Cmult58
    (Bmult[3] => Cmult[58]) = 30289; // Bmult3 -> Cmult58
    (Amult[3] => Cmult[59]) = 31468; // Amult3 -> Cmult59
    (Bmult[3] => Cmult[59]) = 30358; // Bmult3 -> Cmult59
    (Amult[3] => Cmult[60]) = 31983; // Amult3 -> Cmult60
    (Bmult[3] => Cmult[60]) = 30920; // Bmult3 -> Cmult60
    (Amult[3] => Cmult[61]) = 32144; // Amult3 -> Cmult61
    (Bmult[3] => Cmult[61]) = 31007; // Bmult3 -> Cmult61
    (Amult[3] => Cmult[62]) = 32779; // Amult3 -> Cmult62
    (Bmult[3] => Cmult[62]) = 31715; // Bmult3 -> Cmult62
    (Amult[3] => Cmult[63]) = 33874; // Amult3 -> Cmult63
    (Bmult[3] => Cmult[63]) = 32809; // Bmult3 -> Cmult63
    (Amult[4] => Cmult[4]) = 5593; // Amult4 -> Cmult4
    (Bmult[4] => Cmult[4]) = 6450; // Bmult4 -> Cmult4
    (Amult[4] => Cmult[5]) = 6485; // Amult4 -> Cmult5
    (Bmult[4] => Cmult[5]) = 7435; // Bmult4 -> Cmult5
    (Amult[4] => Cmult[6]) = 7285; // Amult4 -> Cmult6
    (Bmult[4] => Cmult[6]) = 7941; // Bmult4 -> Cmult6
    (Amult[4] => Cmult[7]) = 7472; // Amult4 -> Cmult7
    (Bmult[4] => Cmult[7]) = 8716; // Bmult4 -> Cmult7
    (Amult[4] => Cmult[8]) = 8967; // Amult4 -> Cmult8
    (Bmult[4] => Cmult[8]) = 9462; // Bmult4 -> Cmult8
    (Amult[4] => Cmult[9]) = 9274; // Amult4 -> Cmult9
    (Bmult[4] => Cmult[9]) = 10044; // Bmult4 -> Cmult9
    (Amult[4] => Cmult[10]) = 9585; // Amult4 -> Cmult10
    (Bmult[4] => Cmult[10]) = 10590; // Bmult4 -> Cmult10
    (Amult[4] => Cmult[11]) = 10125; // Amult4 -> Cmult11
    (Bmult[4] => Cmult[11]) = 11075; // Bmult4 -> Cmult11
    (Amult[4] => Cmult[12]) = 10715; // Amult4 -> Cmult12
    (Bmult[4] => Cmult[12]) = 11403; // Bmult4 -> Cmult12
    (Amult[4] => Cmult[13]) = 11378; // Amult4 -> Cmult13
    (Bmult[4] => Cmult[13]) = 12069; // Bmult4 -> Cmult13
    (Amult[4] => Cmult[14]) = 11980; // Amult4 -> Cmult14
    (Bmult[4] => Cmult[14]) = 12595; // Bmult4 -> Cmult14
    (Amult[4] => Cmult[15]) = 13694; // Amult4 -> Cmult15
    (Bmult[4] => Cmult[15]) = 13875; // Bmult4 -> Cmult15
    (Amult[4] => Cmult[16]) = 13594; // Amult4 -> Cmult16
    (Bmult[4] => Cmult[16]) = 14048; // Bmult4 -> Cmult16
    (Amult[4] => Cmult[17]) = 13695; // Amult4 -> Cmult17
    (Bmult[4] => Cmult[17]) = 14429; // Bmult4 -> Cmult17
    (Amult[4] => Cmult[18]) = 13995; // Amult4 -> Cmult18
    (Bmult[4] => Cmult[18]) = 14037; // Bmult4 -> Cmult18
    (Amult[4] => Cmult[19]) = 14291; // Amult4 -> Cmult19
    (Bmult[4] => Cmult[19]) = 14230; // Bmult4 -> Cmult19
    (Amult[4] => Cmult[20]) = 14789; // Amult4 -> Cmult20
    (Bmult[4] => Cmult[20]) = 14653; // Bmult4 -> Cmult20
    (Amult[4] => Cmult[21]) = 15035; // Amult4 -> Cmult21
    (Bmult[4] => Cmult[21]) = 14973; // Bmult4 -> Cmult21
    (Amult[4] => Cmult[22]) = 15388; // Amult4 -> Cmult22
    (Bmult[4] => Cmult[22]) = 15228; // Bmult4 -> Cmult22
    (Amult[4] => Cmult[23]) = 15502; // Amult4 -> Cmult23
    (Bmult[4] => Cmult[23]) = 15441; // Bmult4 -> Cmult23
    (Amult[4] => Cmult[24]) = 15421; // Amult4 -> Cmult24
    (Bmult[4] => Cmult[24]) = 15820; // Bmult4 -> Cmult24
    (Amult[4] => Cmult[25]) = 15640; // Amult4 -> Cmult25
    (Bmult[4] => Cmult[25]) = 16224; // Bmult4 -> Cmult25
    (Amult[4] => Cmult[26]) = 16459; // Amult4 -> Cmult26
    (Bmult[4] => Cmult[26]) = 16502; // Bmult4 -> Cmult26
    (Amult[4] => Cmult[27]) = 16532; // Amult4 -> Cmult27
    (Bmult[4] => Cmult[27]) = 16890; // Bmult4 -> Cmult27
    (Amult[4] => Cmult[28]) = 16803; // Amult4 -> Cmult28
    (Bmult[4] => Cmult[28]) = 17414; // Bmult4 -> Cmult28
    (Amult[4] => Cmult[29]) = 17168; // Amult4 -> Cmult29
    (Bmult[4] => Cmult[29]) = 17852; // Bmult4 -> Cmult29
    (Amult[4] => Cmult[30]) = 17812; // Amult4 -> Cmult30
    (Bmult[4] => Cmult[30]) = 18419; // Bmult4 -> Cmult30
    (Amult[4] => Cmult[31]) = 18621; // Amult4 -> Cmult31
    (Bmult[4] => Cmult[31]) = 19229; // Bmult4 -> Cmult31
    (Amult[4] => Cmult[32]) = 24283; // Amult4 -> Cmult32
    (Bmult[4] => Cmult[32]) = 23688; // Bmult4 -> Cmult32
    (Amult[4] => Cmult[33]) = 24537; // Amult4 -> Cmult33
    (Bmult[4] => Cmult[33]) = 23968; // Bmult4 -> Cmult33
    (Amult[4] => Cmult[34]) = 24779; // Amult4 -> Cmult34
    (Bmult[4] => Cmult[34]) = 24258; // Bmult4 -> Cmult34
    (Amult[4] => Cmult[35]) = 24964; // Amult4 -> Cmult35
    (Bmult[4] => Cmult[35]) = 24489; // Bmult4 -> Cmult35
    (Amult[4] => Cmult[36]) = 25153; // Amult4 -> Cmult36
    (Bmult[4] => Cmult[36]) = 24810; // Bmult4 -> Cmult36
    (Amult[4] => Cmult[37]) = 25224; // Amult4 -> Cmult37
    (Bmult[4] => Cmult[37]) = 24851; // Bmult4 -> Cmult37
    (Amult[4] => Cmult[38]) = 25336; // Amult4 -> Cmult38
    (Bmult[4] => Cmult[38]) = 25287; // Bmult4 -> Cmult38
    (Amult[4] => Cmult[39]) = 25637; // Amult4 -> Cmult39
    (Bmult[4] => Cmult[39]) = 25589; // Bmult4 -> Cmult39
    (Amult[4] => Cmult[40]) = 26082; // Amult4 -> Cmult40
    (Bmult[4] => Cmult[40]) = 25793; // Bmult4 -> Cmult40
    (Amult[4] => Cmult[41]) = 26087; // Amult4 -> Cmult41
    (Bmult[4] => Cmult[41]) = 26033; // Bmult4 -> Cmult41
    (Amult[4] => Cmult[42]) = 25519; // Amult4 -> Cmult42
    (Bmult[4] => Cmult[42]) = 25419; // Bmult4 -> Cmult42
    (Amult[4] => Cmult[43]) = 26209; // Amult4 -> Cmult43
    (Bmult[4] => Cmult[43]) = 26109; // Bmult4 -> Cmult43
    (Amult[4] => Cmult[44]) = 26615; // Amult4 -> Cmult44
    (Bmult[4] => Cmult[44]) = 26532; // Bmult4 -> Cmult44
    (Amult[4] => Cmult[45]) = 26825; // Amult4 -> Cmult45
    (Bmult[4] => Cmult[45]) = 26724; // Bmult4 -> Cmult45
    (Amult[4] => Cmult[46]) = 26215; // Amult4 -> Cmult46
    (Bmult[4] => Cmult[46]) = 26114; // Bmult4 -> Cmult46
    (Amult[4] => Cmult[47]) = 26158; // Amult4 -> Cmult47
    (Bmult[4] => Cmult[47]) = 26097; // Bmult4 -> Cmult47
    (Amult[4] => Cmult[48]) = 27136; // Amult4 -> Cmult48
    (Bmult[4] => Cmult[48]) = 27036; // Bmult4 -> Cmult48
    (Amult[4] => Cmult[49]) = 26972; // Amult4 -> Cmult49
    (Bmult[4] => Cmult[49]) = 26902; // Bmult4 -> Cmult49
    (Amult[4] => Cmult[50]) = 27746; // Amult4 -> Cmult50
    (Bmult[4] => Cmult[50]) = 27658; // Bmult4 -> Cmult50
    (Amult[4] => Cmult[51]) = 27939; // Amult4 -> Cmult51
    (Bmult[4] => Cmult[51]) = 27850; // Bmult4 -> Cmult51
    (Amult[4] => Cmult[52]) = 28675; // Amult4 -> Cmult52
    (Bmult[4] => Cmult[52]) = 28504; // Bmult4 -> Cmult52
    (Amult[4] => Cmult[53]) = 28956; // Amult4 -> Cmult53
    (Bmult[4] => Cmult[53]) = 28735; // Bmult4 -> Cmult53
    (Amult[4] => Cmult[54]) = 29249; // Amult4 -> Cmult54
    (Bmult[4] => Cmult[54]) = 29161; // Bmult4 -> Cmult54
    (Amult[4] => Cmult[55]) = 29447; // Amult4 -> Cmult55
    (Bmult[4] => Cmult[55]) = 29272; // Bmult4 -> Cmult55
    (Amult[4] => Cmult[56]) = 29984; // Amult4 -> Cmult56
    (Bmult[4] => Cmult[56]) = 29842; // Bmult4 -> Cmult56
    (Amult[4] => Cmult[57]) = 30216; // Amult4 -> Cmult57
    (Bmult[4] => Cmult[57]) = 30127; // Bmult4 -> Cmult57
    (Amult[4] => Cmult[58]) = 30674; // Amult4 -> Cmult58
    (Bmult[4] => Cmult[58]) = 30585; // Bmult4 -> Cmult58
    (Amult[4] => Cmult[59]) = 30743; // Amult4 -> Cmult59
    (Bmult[4] => Cmult[59]) = 30654; // Bmult4 -> Cmult59
    (Amult[4] => Cmult[60]) = 31305; // Amult4 -> Cmult60
    (Bmult[4] => Cmult[60]) = 31216; // Bmult4 -> Cmult60
    (Amult[4] => Cmult[61]) = 31323; // Amult4 -> Cmult61
    (Bmult[4] => Cmult[61]) = 31196; // Bmult4 -> Cmult61
    (Amult[4] => Cmult[62]) = 32101; // Amult4 -> Cmult62
    (Bmult[4] => Cmult[62]) = 32011; // Bmult4 -> Cmult62
    (Amult[4] => Cmult[63]) = 33196; // Amult4 -> Cmult63
    (Bmult[4] => Cmult[63]) = 33105; // Bmult4 -> Cmult63
    (Amult[5] => Cmult[5]) = 5575; // Amult5 -> Cmult5
    (Bmult[5] => Cmult[5]) = 7227; // Bmult5 -> Cmult5
    (Amult[5] => Cmult[6]) = 6229; // Amult5 -> Cmult6
    (Bmult[5] => Cmult[6]) = 7987; // Bmult5 -> Cmult6
    (Amult[5] => Cmult[7]) = 6868; // Amult5 -> Cmult7
    (Bmult[5] => Cmult[7]) = 8586; // Bmult5 -> Cmult7
    (Amult[5] => Cmult[8]) = 7783; // Amult5 -> Cmult8
    (Bmult[5] => Cmult[8]) = 9381; // Bmult5 -> Cmult8
    (Amult[5] => Cmult[9]) = 8294; // Amult5 -> Cmult9
    (Bmult[5] => Cmult[9]) = 9912; // Bmult5 -> Cmult9
    (Amult[5] => Cmult[10]) = 8874; // Amult5 -> Cmult10
    (Bmult[5] => Cmult[10]) = 10580; // Bmult5 -> Cmult10
    (Amult[5] => Cmult[11]) = 9579; // Amult5 -> Cmult11
    (Bmult[5] => Cmult[11]) = 11027; // Bmult5 -> Cmult11
    (Amult[5] => Cmult[12]) = 9903; // Amult5 -> Cmult12
    (Bmult[5] => Cmult[12]) = 11344; // Bmult5 -> Cmult12
    (Amult[5] => Cmult[13]) = 10784; // Amult5 -> Cmult13
    (Bmult[5] => Cmult[13]) = 12049; // Bmult5 -> Cmult13
    (Amult[5] => Cmult[14]) = 11312; // Amult5 -> Cmult14
    (Bmult[5] => Cmult[14]) = 12538; // Bmult5 -> Cmult14
    (Amult[5] => Cmult[15]) = 12843; // Amult5 -> Cmult15
    (Bmult[5] => Cmult[15]) = 13905; // Bmult5 -> Cmult15
    (Amult[5] => Cmult[16]) = 12763; // Amult5 -> Cmult16
    (Bmult[5] => Cmult[16]) = 14079; // Bmult5 -> Cmult16
    (Amult[5] => Cmult[17]) = 13144; // Amult5 -> Cmult17
    (Bmult[5] => Cmult[17]) = 14460; // Bmult5 -> Cmult17
    (Amult[5] => Cmult[18]) = 13331; // Amult5 -> Cmult18
    (Bmult[5] => Cmult[18]) = 14179; // Bmult5 -> Cmult18
    (Amult[5] => Cmult[19]) = 13657; // Amult5 -> Cmult19
    (Bmult[5] => Cmult[19]) = 14505; // Bmult5 -> Cmult19
    (Amult[5] => Cmult[20]) = 14080; // Amult5 -> Cmult20
    (Bmult[5] => Cmult[20]) = 14928; // Bmult5 -> Cmult20
    (Amult[5] => Cmult[21]) = 14400; // Amult5 -> Cmult21
    (Bmult[5] => Cmult[21]) = 15248; // Bmult5 -> Cmult21
    (Amult[5] => Cmult[22]) = 14655; // Amult5 -> Cmult22
    (Bmult[5] => Cmult[22]) = 15503; // Bmult5 -> Cmult22
    (Amult[5] => Cmult[23]) = 14868; // Amult5 -> Cmult23
    (Bmult[5] => Cmult[23]) = 15716; // Bmult5 -> Cmult23
    (Amult[5] => Cmult[24]) = 14740; // Amult5 -> Cmult24
    (Bmult[5] => Cmult[24]) = 15779; // Bmult5 -> Cmult24
    (Amult[5] => Cmult[25]) = 15007; // Amult5 -> Cmult25
    (Bmult[5] => Cmult[25]) = 16182; // Bmult5 -> Cmult25
    (Amult[5] => Cmult[26]) = 15697; // Amult5 -> Cmult26
    (Bmult[5] => Cmult[26]) = 16553; // Bmult5 -> Cmult26
    (Amult[5] => Cmult[27]) = 15899; // Amult5 -> Cmult27
    (Bmult[5] => Cmult[27]) = 16849; // Bmult5 -> Cmult27
    (Amult[5] => Cmult[28]) = 16157; // Amult5 -> Cmult28
    (Bmult[5] => Cmult[28]) = 17373; // Bmult5 -> Cmult28
    (Amult[5] => Cmult[29]) = 16595; // Amult5 -> Cmult29
    (Bmult[5] => Cmult[29]) = 17811; // Bmult5 -> Cmult29
    (Amult[5] => Cmult[30]) = 17179; // Amult5 -> Cmult30
    (Bmult[5] => Cmult[30]) = 18377; // Bmult5 -> Cmult30
    (Amult[5] => Cmult[31]) = 17986; // Amult5 -> Cmult31
    (Bmult[5] => Cmult[31]) = 19188; // Bmult5 -> Cmult31
    (Amult[5] => Cmult[32]) = 23584; // Amult5 -> Cmult32
    (Bmult[5] => Cmult[32]) = 23933; // Bmult5 -> Cmult32
    (Amult[5] => Cmult[33]) = 23837; // Amult5 -> Cmult33
    (Bmult[5] => Cmult[33]) = 24220; // Bmult5 -> Cmult33
    (Amult[5] => Cmult[34]) = 24080; // Amult5 -> Cmult34
    (Bmult[5] => Cmult[34]) = 24566; // Bmult5 -> Cmult34
    (Amult[5] => Cmult[35]) = 24254; // Amult5 -> Cmult35
    (Bmult[5] => Cmult[35]) = 24741; // Bmult5 -> Cmult35
    (Amult[5] => Cmult[36]) = 24453; // Amult5 -> Cmult36
    (Bmult[5] => Cmult[36]) = 25188; // Bmult5 -> Cmult36
    (Amult[5] => Cmult[37]) = 24524; // Amult5 -> Cmult37
    (Bmult[5] => Cmult[37]) = 25344; // Bmult5 -> Cmult37
    (Amult[5] => Cmult[38]) = 24632; // Amult5 -> Cmult38
    (Bmult[5] => Cmult[38]) = 25666; // Bmult5 -> Cmult38
    (Amult[5] => Cmult[39]) = 24933; // Amult5 -> Cmult39
    (Bmult[5] => Cmult[39]) = 25967; // Bmult5 -> Cmult39
    (Amult[5] => Cmult[40]) = 25382; // Amult5 -> Cmult40
    (Bmult[5] => Cmult[40]) = 26178; // Bmult5 -> Cmult40
    (Amult[5] => Cmult[41]) = 25383; // Amult5 -> Cmult41
    (Bmult[5] => Cmult[41]) = 26411; // Bmult5 -> Cmult41
    (Amult[5] => Cmult[42]) = 24815; // Amult5 -> Cmult42
    (Bmult[5] => Cmult[42]) = 25826; // Bmult5 -> Cmult42
    (Amult[5] => Cmult[43]) = 25506; // Amult5 -> Cmult43
    (Bmult[5] => Cmult[43]) = 26497; // Bmult5 -> Cmult43
    (Amult[5] => Cmult[44]) = 25912; // Amult5 -> Cmult44
    (Bmult[5] => Cmult[44]) = 27012; // Bmult5 -> Cmult44
    (Amult[5] => Cmult[45]) = 26121; // Amult5 -> Cmult45
    (Bmult[5] => Cmult[45]) = 27113; // Bmult5 -> Cmult45
    (Amult[5] => Cmult[46]) = 25511; // Amult5 -> Cmult46
    (Bmult[5] => Cmult[46]) = 26503; // Bmult5 -> Cmult46
    (Amult[5] => Cmult[47]) = 25454; // Amult5 -> Cmult47
    (Bmult[5] => Cmult[47]) = 26480; // Bmult5 -> Cmult47
    (Amult[5] => Cmult[48]) = 26433; // Amult5 -> Cmult48
    (Bmult[5] => Cmult[48]) = 27425; // Bmult5 -> Cmult48
    (Amult[5] => Cmult[49]) = 26269; // Amult5 -> Cmult49
    (Bmult[5] => Cmult[49]) = 27286; // Bmult5 -> Cmult49
    (Amult[5] => Cmult[50]) = 27043; // Amult5 -> Cmult50
    (Bmult[5] => Cmult[50]) = 28036; // Bmult5 -> Cmult50
    (Amult[5] => Cmult[51]) = 27235; // Amult5 -> Cmult51
    (Bmult[5] => Cmult[51]) = 28259; // Bmult5 -> Cmult51
    (Amult[5] => Cmult[52]) = 27975; // Amult5 -> Cmult52
    (Bmult[5] => Cmult[52]) = 28882; // Bmult5 -> Cmult52
    (Amult[5] => Cmult[53]) = 28256; // Amult5 -> Cmult53
    (Bmult[5] => Cmult[53]) = 29211; // Bmult5 -> Cmult53
    (Amult[5] => Cmult[54]) = 28546; // Amult5 -> Cmult54
    (Bmult[5] => Cmult[54]) = 29540; // Bmult5 -> Cmult54
    (Amult[5] => Cmult[55]) = 28747; // Amult5 -> Cmult55
    (Bmult[5] => Cmult[55]) = 29748; // Bmult5 -> Cmult55
    (Amult[5] => Cmult[56]) = 29284; // Amult5 -> Cmult56
    (Bmult[5] => Cmult[56]) = 30220; // Bmult5 -> Cmult56
    (Amult[5] => Cmult[57]) = 29512; // Amult5 -> Cmult57
    (Bmult[5] => Cmult[57]) = 30506; // Bmult5 -> Cmult57
    (Amult[5] => Cmult[58]) = 29970; // Amult5 -> Cmult58
    (Bmult[5] => Cmult[58]) = 30964; // Bmult5 -> Cmult58
    (Amult[5] => Cmult[59]) = 30039; // Amult5 -> Cmult59
    (Bmult[5] => Cmult[59]) = 31032; // Bmult5 -> Cmult59
    (Amult[5] => Cmult[60]) = 30601; // Amult5 -> Cmult60
    (Bmult[5] => Cmult[60]) = 31595; // Bmult5 -> Cmult60
    (Amult[5] => Cmult[61]) = 30623; // Amult5 -> Cmult61
    (Bmult[5] => Cmult[61]) = 31675; // Bmult5 -> Cmult61
    (Amult[5] => Cmult[62]) = 31398; // Amult5 -> Cmult62
    (Bmult[5] => Cmult[62]) = 32389; // Bmult5 -> Cmult62
    (Amult[5] => Cmult[63]) = 32493; // Amult5 -> Cmult63
    (Bmult[5] => Cmult[63]) = 33483; // Bmult5 -> Cmult63
    (Amult[6] => Cmult[6]) = 5975; // Amult6 -> Cmult6
    (Bmult[6] => Cmult[6]) = 8357; // Bmult6 -> Cmult6
    (Amult[6] => Cmult[7]) = 5950; // Amult6 -> Cmult7
    (Bmult[6] => Cmult[7]) = 8739; // Bmult6 -> Cmult7
    (Amult[6] => Cmult[8]) = 7274; // Amult6 -> Cmult8
    (Bmult[6] => Cmult[8]) = 9901; // Bmult6 -> Cmult8
    (Amult[6] => Cmult[9]) = 7658; // Amult6 -> Cmult9
    (Bmult[6] => Cmult[9]) = 10232; // Bmult6 -> Cmult9
    (Amult[6] => Cmult[10]) = 7995; // Amult6 -> Cmult10
    (Bmult[6] => Cmult[10]) = 10833; // Bmult6 -> Cmult10
    (Amult[6] => Cmult[11]) = 8670; // Amult6 -> Cmult11
    (Bmult[6] => Cmult[11]) = 11280; // Bmult6 -> Cmult11
    (Amult[6] => Cmult[12]) = 9268; // Amult6 -> Cmult12
    (Bmult[6] => Cmult[12]) = 11649; // Bmult6 -> Cmult12
    (Amult[6] => Cmult[13]) = 9896; // Amult6 -> Cmult13
    (Bmult[6] => Cmult[13]) = 12301; // Bmult6 -> Cmult13
    (Amult[6] => Cmult[14]) = 10454; // Amult6 -> Cmult14
    (Bmult[6] => Cmult[14]) = 12787; // Bmult6 -> Cmult14
    (Amult[6] => Cmult[15]) = 12208; // Amult6 -> Cmult15
    (Bmult[6] => Cmult[15]) = 14369; // Bmult6 -> Cmult15
    (Amult[6] => Cmult[16]) = 12037; // Amult6 -> Cmult16
    (Bmult[6] => Cmult[16]) = 14157; // Bmult6 -> Cmult16
    (Amult[6] => Cmult[17]) = 12263; // Amult6 -> Cmult17
    (Bmult[6] => Cmult[17]) = 14526; // Bmult6 -> Cmult17
    (Amult[6] => Cmult[18]) = 12634; // Amult6 -> Cmult18
    (Bmult[6] => Cmult[18]) = 14806; // Bmult6 -> Cmult18
    (Amult[6] => Cmult[19]) = 12960; // Amult6 -> Cmult19
    (Bmult[6] => Cmult[19]) = 15132; // Bmult6 -> Cmult19
    (Amult[6] => Cmult[20]) = 13384; // Amult6 -> Cmult20
    (Bmult[6] => Cmult[20]) = 15555; // Bmult6 -> Cmult20
    (Amult[6] => Cmult[21]) = 13703; // Amult6 -> Cmult21
    (Bmult[6] => Cmult[21]) = 15875; // Bmult6 -> Cmult21
    (Amult[6] => Cmult[22]) = 13959; // Amult6 -> Cmult22
    (Bmult[6] => Cmult[22]) = 16130; // Bmult6 -> Cmult22
    (Amult[6] => Cmult[23]) = 14171; // Amult6 -> Cmult23
    (Bmult[6] => Cmult[23]) = 16343; // Bmult6 -> Cmult23
    (Amult[6] => Cmult[24]) = 14104; // Amult6 -> Cmult24
    (Bmult[6] => Cmult[24]) = 16264; // Bmult6 -> Cmult24
    (Amult[6] => Cmult[25]) = 14310; // Amult6 -> Cmult25
    (Bmult[6] => Cmult[25]) = 16481; // Bmult6 -> Cmult25
    (Amult[6] => Cmult[26]) = 15046; // Amult6 -> Cmult26
    (Bmult[6] => Cmult[26]) = 17207; // Bmult6 -> Cmult26
    (Amult[6] => Cmult[27]) = 15202; // Amult6 -> Cmult27
    (Bmult[6] => Cmult[27]) = 17373; // Bmult6 -> Cmult27
    (Amult[6] => Cmult[28]) = 15515; // Amult6 -> Cmult28
    (Bmult[6] => Cmult[28]) = 17676; // Bmult6 -> Cmult28
    (Amult[6] => Cmult[29]) = 15805; // Amult6 -> Cmult29
    (Bmult[6] => Cmult[29]) = 17976; // Bmult6 -> Cmult29
    (Amult[6] => Cmult[30]) = 16515; // Amult6 -> Cmult30
    (Bmult[6] => Cmult[30]) = 18676; // Bmult6 -> Cmult30
    (Amult[6] => Cmult[31]) = 17289; // Amult6 -> Cmult31
    (Bmult[6] => Cmult[31]) = 19461; // Bmult6 -> Cmult31
    (Amult[6] => Cmult[32]) = 22881; // Amult6 -> Cmult32
    (Bmult[6] => Cmult[32]) = 24381; // Bmult6 -> Cmult32
    (Amult[6] => Cmult[33]) = 23135; // Amult6 -> Cmult33
    (Bmult[6] => Cmult[33]) = 24722; // Bmult6 -> Cmult33
    (Amult[6] => Cmult[34]) = 23377; // Amult6 -> Cmult34
    (Bmult[6] => Cmult[34]) = 25012; // Bmult6 -> Cmult34
    (Amult[6] => Cmult[35]) = 23606; // Amult6 -> Cmult35
    (Bmult[6] => Cmult[35]) = 25243; // Bmult6 -> Cmult35
    (Amult[6] => Cmult[36]) = 23786; // Amult6 -> Cmult36
    (Bmult[6] => Cmult[36]) = 25453; // Bmult6 -> Cmult36
    (Amult[6] => Cmult[37]) = 23865; // Amult6 -> Cmult37
    (Bmult[6] => Cmult[37]) = 25660; // Bmult6 -> Cmult37
    (Amult[6] => Cmult[38]) = 24263; // Amult6 -> Cmult38
    (Bmult[6] => Cmult[38]) = 25903; // Bmult6 -> Cmult38
    (Amult[6] => Cmult[39]) = 24564; // Amult6 -> Cmult39
    (Bmult[6] => Cmult[39]) = 26140; // Bmult6 -> Cmult39
    (Amult[6] => Cmult[40]) = 24769; // Amult6 -> Cmult40
    (Bmult[6] => Cmult[40]) = 26493; // Bmult6 -> Cmult40
    (Amult[6] => Cmult[41]) = 25014; // Amult6 -> Cmult41
    (Bmult[6] => Cmult[41]) = 26590; // Bmult6 -> Cmult41
    (Amult[6] => Cmult[42]) = 24447; // Amult6 -> Cmult42
    (Bmult[6] => Cmult[42]) = 26142; // Bmult6 -> Cmult42
    (Amult[6] => Cmult[43]) = 25137; // Amult6 -> Cmult43
    (Bmult[6] => Cmult[43]) = 26675; // Bmult6 -> Cmult43
    (Amult[6] => Cmult[44]) = 25543; // Amult6 -> Cmult44
    (Bmult[6] => Cmult[44]) = 27369; // Bmult6 -> Cmult44
    (Amult[6] => Cmult[45]) = 25752; // Amult6 -> Cmult45
    (Bmult[6] => Cmult[45]) = 27296; // Bmult6 -> Cmult45
    (Amult[6] => Cmult[46]) = 25142; // Amult6 -> Cmult46
    (Bmult[6] => Cmult[46]) = 26853; // Bmult6 -> Cmult46
    (Amult[6] => Cmult[47]) = 25085; // Amult6 -> Cmult47
    (Bmult[6] => Cmult[47]) = 26663; // Bmult6 -> Cmult47
    (Amult[6] => Cmult[48]) = 26064; // Amult6 -> Cmult48
    (Bmult[6] => Cmult[48]) = 27725; // Bmult6 -> Cmult48
    (Amult[6] => Cmult[49]) = 25900; // Amult6 -> Cmult49
    (Bmult[6] => Cmult[49]) = 27526; // Bmult6 -> Cmult49
    (Amult[6] => Cmult[50]) = 26674; // Amult6 -> Cmult50
    (Bmult[6] => Cmult[50]) = 28263; // Bmult6 -> Cmult50
    (Amult[6] => Cmult[51]) = 26866; // Amult6 -> Cmult51
    (Bmult[6] => Cmult[51]) = 28614; // Bmult6 -> Cmult51
    (Amult[6] => Cmult[52]) = 27520; // Amult6 -> Cmult52
    (Bmult[6] => Cmult[52]) = 29076; // Bmult6 -> Cmult52
    (Amult[6] => Cmult[53]) = 27752; // Amult6 -> Cmult53
    (Bmult[6] => Cmult[53]) = 29566; // Bmult6 -> Cmult53
    (Amult[6] => Cmult[54]) = 28177; // Amult6 -> Cmult54
    (Bmult[6] => Cmult[54]) = 29844; // Bmult6 -> Cmult54
    (Amult[6] => Cmult[55]) = 28270; // Amult6 -> Cmult55
    (Bmult[6] => Cmult[55]) = 30103; // Bmult6 -> Cmult55
    (Amult[6] => Cmult[56]) = 28858; // Amult6 -> Cmult56
    (Bmult[6] => Cmult[56]) = 30377; // Bmult6 -> Cmult56
    (Amult[6] => Cmult[57]) = 29144; // Amult6 -> Cmult57
    (Bmult[6] => Cmult[57]) = 30820; // Bmult6 -> Cmult57
    (Amult[6] => Cmult[58]) = 29602; // Amult6 -> Cmult58
    (Bmult[6] => Cmult[58]) = 31184; // Bmult6 -> Cmult58
    (Amult[6] => Cmult[59]) = 29670; // Amult6 -> Cmult59
    (Bmult[6] => Cmult[59]) = 31354; // Bmult6 -> Cmult59
    (Amult[6] => Cmult[60]) = 30232; // Amult6 -> Cmult60
    (Bmult[6] => Cmult[60]) = 31777; // Bmult6 -> Cmult60
    (Amult[6] => Cmult[61]) = 30212; // Amult6 -> Cmult61
    (Bmult[6] => Cmult[61]) = 32030; // Bmult6 -> Cmult61
    (Amult[6] => Cmult[62]) = 31029; // Amult6 -> Cmult62
    (Bmult[6] => Cmult[62]) = 32511; // Bmult6 -> Cmult62
    (Amult[6] => Cmult[63]) = 32124; // Amult6 -> Cmult63
    (Bmult[6] => Cmult[63]) = 33655; // Bmult6 -> Cmult63
    (Amult[7] => Cmult[7]) = 5219; // Amult7 -> Cmult7
    (Bmult[7] => Cmult[7]) = 8540; // Bmult7 -> Cmult7
    (Amult[7] => Cmult[8]) = 6387; // Amult7 -> Cmult8
    (Bmult[7] => Cmult[8]) = 9822; // Bmult7 -> Cmult8
    (Amult[7] => Cmult[9]) = 6837; // Amult7 -> Cmult9
    (Bmult[7] => Cmult[9]) = 10129; // Bmult7 -> Cmult9
    (Amult[7] => Cmult[10]) = 7327; // Amult7 -> Cmult10
    (Bmult[7] => Cmult[10]) = 10816; // Bmult7 -> Cmult10
    (Amult[7] => Cmult[11]) = 7890; // Amult7 -> Cmult11
    (Bmult[7] => Cmult[11]) = 11262; // Bmult7 -> Cmult11
    (Amult[7] => Cmult[12]) = 8419; // Amult7 -> Cmult12
    (Bmult[7] => Cmult[12]) = 11585; // Bmult7 -> Cmult12
    (Amult[7] => Cmult[13]) = 9185; // Amult7 -> Cmult13
    (Bmult[7] => Cmult[13]) = 12284; // Bmult7 -> Cmult13
    (Amult[7] => Cmult[14]) = 9713; // Amult7 -> Cmult14
    (Bmult[7] => Cmult[14]) = 12779; // Bmult7 -> Cmult14
    (Amult[7] => Cmult[15]) = 11265; // Amult7 -> Cmult15
    (Bmult[7] => Cmult[15]) = 14190; // Bmult7 -> Cmult15
    (Amult[7] => Cmult[16]) = 11124; // Amult7 -> Cmult16
    (Bmult[7] => Cmult[16]) = 14320; // Bmult7 -> Cmult16
    (Amult[7] => Cmult[17]) = 11370; // Amult7 -> Cmult17
    (Bmult[7] => Cmult[17]) = 14701; // Bmult7 -> Cmult17
    (Amult[7] => Cmult[18]) = 11732; // Amult7 -> Cmult18
    (Bmult[7] => Cmult[18]) = 14491; // Bmult7 -> Cmult18
    (Amult[7] => Cmult[19]) = 12058; // Amult7 -> Cmult19
    (Bmult[7] => Cmult[19]) = 14771; // Bmult7 -> Cmult19
    (Amult[7] => Cmult[20]) = 12482; // Amult7 -> Cmult20
    (Bmult[7] => Cmult[20]) = 15284; // Bmult7 -> Cmult20
    (Amult[7] => Cmult[21]) = 12801; // Amult7 -> Cmult21
    (Bmult[7] => Cmult[21]) = 15531; // Bmult7 -> Cmult21
    (Amult[7] => Cmult[22]) = 13056; // Amult7 -> Cmult22
    (Bmult[7] => Cmult[22]) = 15884; // Bmult7 -> Cmult22
    (Amult[7] => Cmult[23]) = 13269; // Amult7 -> Cmult23
    (Bmult[7] => Cmult[23]) = 15988; // Bmult7 -> Cmult23
    (Amult[7] => Cmult[24]) = 13160; // Amult7 -> Cmult24
    (Bmult[7] => Cmult[24]) = 16020; // Bmult7 -> Cmult24
    (Amult[7] => Cmult[25]) = 13408; // Amult7 -> Cmult25
    (Bmult[7] => Cmult[25]) = 16423; // Bmult7 -> Cmult25
    (Amult[7] => Cmult[26]) = 14103; // Amult7 -> Cmult26
    (Bmult[7] => Cmult[26]) = 16955; // Bmult7 -> Cmult26
    (Amult[7] => Cmult[27]) = 14300; // Amult7 -> Cmult27
    (Bmult[7] => Cmult[27]) = 17090; // Bmult7 -> Cmult27
    (Amult[7] => Cmult[28]) = 14572; // Amult7 -> Cmult28
    (Bmult[7] => Cmult[28]) = 17614; // Bmult7 -> Cmult28
    (Amult[7] => Cmult[29]) = 14902; // Amult7 -> Cmult29
    (Bmult[7] => Cmult[29]) = 18052; // Bmult7 -> Cmult29
    (Amult[7] => Cmult[30]) = 15580; // Amult7 -> Cmult30
    (Bmult[7] => Cmult[30]) = 18618; // Bmult7 -> Cmult30
    (Amult[7] => Cmult[31]) = 16387; // Amult7 -> Cmult31
    (Bmult[7] => Cmult[31]) = 19429; // Bmult7 -> Cmult31
    (Amult[7] => Cmult[32]) = 22022; // Amult7 -> Cmult32
    (Bmult[7] => Cmult[32]) = 24216; // Bmult7 -> Cmult32
    (Amult[7] => Cmult[33]) = 22359; // Amult7 -> Cmult33
    (Bmult[7] => Cmult[33]) = 24400; // Bmult7 -> Cmult33
    (Amult[7] => Cmult[34]) = 22634; // Amult7 -> Cmult34
    (Bmult[7] => Cmult[34]) = 24904; // Bmult7 -> Cmult34
    (Amult[7] => Cmult[35]) = 22884; // Amult7 -> Cmult35
    (Bmult[7] => Cmult[35]) = 25019; // Bmult7 -> Cmult35
    (Amult[7] => Cmult[36]) = 22951; // Amult7 -> Cmult36
    (Bmult[7] => Cmult[36]) = 25526; // Bmult7 -> Cmult36
    (Amult[7] => Cmult[37]) = 23143; // Amult7 -> Cmult37
    (Bmult[7] => Cmult[37]) = 25620; // Bmult7 -> Cmult37
    (Amult[7] => Cmult[38]) = 23081; // Amult7 -> Cmult38
    (Bmult[7] => Cmult[38]) = 26004; // Bmult7 -> Cmult38
    (Amult[7] => Cmult[39]) = 23387; // Amult7 -> Cmult39
    (Bmult[7] => Cmult[39]) = 26305; // Bmult7 -> Cmult39
    (Amult[7] => Cmult[40]) = 23843; // Amult7 -> Cmult40
    (Bmult[7] => Cmult[40]) = 26509; // Bmult7 -> Cmult40
    (Amult[7] => Cmult[41]) = 23870; // Amult7 -> Cmult41
    (Bmult[7] => Cmult[41]) = 26755; // Bmult7 -> Cmult41
    (Amult[7] => Cmult[42]) = 23321; // Amult7 -> Cmult42
    (Bmult[7] => Cmult[42]) = 26187; // Bmult7 -> Cmult42
    (Amult[7] => Cmult[43]) = 23907; // Amult7 -> Cmult43
    (Bmult[7] => Cmult[43]) = 26877; // Bmult7 -> Cmult43
    (Amult[7] => Cmult[44]) = 24548; // Amult7 -> Cmult44
    (Bmult[7] => Cmult[44]) = 27329; // Bmult7 -> Cmult44
    (Amult[7] => Cmult[45]) = 24523; // Amult7 -> Cmult45
    (Bmult[7] => Cmult[45]) = 27493; // Bmult7 -> Cmult45
    (Amult[7] => Cmult[46]) = 24031; // Amult7 -> Cmult46
    (Bmult[7] => Cmult[46]) = 26882; // Bmult7 -> Cmult46
    (Amult[7] => Cmult[47]) = 23879; // Amult7 -> Cmult47
    (Bmult[7] => Cmult[47]) = 26818; // Bmult7 -> Cmult47
    (Amult[7] => Cmult[48]) = 24911; // Amult7 -> Cmult48
    (Bmult[7] => Cmult[48]) = 27804; // Bmult7 -> Cmult48
    (Amult[7] => Cmult[49]) = 24705; // Amult7 -> Cmult49
    (Bmult[7] => Cmult[49]) = 27623; // Bmult7 -> Cmult49
    (Amult[7] => Cmult[50]) = 25483; // Amult7 -> Cmult50
    (Bmult[7] => Cmult[50]) = 28413; // Bmult7 -> Cmult50
    (Amult[7] => Cmult[51]) = 25793; // Amult7 -> Cmult51
    (Bmult[7] => Cmult[51]) = 28606; // Bmult7 -> Cmult51
    (Amult[7] => Cmult[52]) = 26514; // Amult7 -> Cmult52
    (Bmult[7] => Cmult[52]) = 29259; // Bmult7 -> Cmult52
    (Amult[7] => Cmult[53]) = 26745; // Amult7 -> Cmult53
    (Bmult[7] => Cmult[53]) = 29526; // Bmult7 -> Cmult53
    (Amult[7] => Cmult[54]) = 27152; // Amult7 -> Cmult54
    (Bmult[7] => Cmult[54]) = 29917; // Bmult7 -> Cmult54
    (Amult[7] => Cmult[55]) = 27282; // Amult7 -> Cmult55
    (Bmult[7] => Cmult[55]) = 30062; // Bmult7 -> Cmult55
    (Amult[7] => Cmult[56]) = 27889; // Amult7 -> Cmult56
    (Bmult[7] => Cmult[56]) = 30598; // Bmult7 -> Cmult56
    (Amult[7] => Cmult[57]) = 28000; // Amult7 -> Cmult57
    (Bmult[7] => Cmult[57]) = 30883; // Bmult7 -> Cmult57
    (Amult[7] => Cmult[58]) = 28372; // Amult7 -> Cmult58
    (Bmult[7] => Cmult[58]) = 31341; // Bmult7 -> Cmult58
    (Amult[7] => Cmult[59]) = 28534; // Amult7 -> Cmult59
    (Bmult[7] => Cmult[59]) = 31409; // Bmult7 -> Cmult59
    (Amult[7] => Cmult[60]) = 29003; // Amult7 -> Cmult60
    (Bmult[7] => Cmult[60]) = 31972; // Bmult7 -> Cmult60
    (Amult[7] => Cmult[61]) = 29209; // Amult7 -> Cmult61
    (Bmult[7] => Cmult[61]) = 31990; // Bmult7 -> Cmult61
    (Amult[7] => Cmult[62]) = 29799; // Amult7 -> Cmult62
    (Bmult[7] => Cmult[62]) = 32767; // Bmult7 -> Cmult62
    (Amult[7] => Cmult[63]) = 30894; // Amult7 -> Cmult63
    (Bmult[7] => Cmult[63]) = 33861; // Bmult7 -> Cmult63
    (Amult[8] => Cmult[8]) = 5839; // Amult8 -> Cmult8
    (Bmult[8] => Cmult[8]) = 9916; // Bmult8 -> Cmult8
    (Amult[8] => Cmult[9]) = 6169; // Amult8 -> Cmult9
    (Bmult[8] => Cmult[9]) = 10611; // Bmult8 -> Cmult9
    (Amult[8] => Cmult[10]) = 6643; // Amult8 -> Cmult10
    (Bmult[8] => Cmult[10]) = 11341; // Bmult8 -> Cmult10
    (Amult[8] => Cmult[11]) = 7121; // Amult8 -> Cmult11
    (Bmult[8] => Cmult[11]) = 11788; // Bmult8 -> Cmult11
    (Amult[8] => Cmult[12]) = 7808; // Amult8 -> Cmult12
    (Bmult[8] => Cmult[12]) = 12078; // Bmult8 -> Cmult12
    (Amult[8] => Cmult[13]) = 8417; // Amult8 -> Cmult13
    (Bmult[8] => Cmult[13]) = 12809; // Bmult8 -> Cmult13
    (Amult[8] => Cmult[14]) = 8999; // Amult8 -> Cmult14
    (Bmult[8] => Cmult[14]) = 13281; // Bmult8 -> Cmult14
    (Amult[8] => Cmult[15]) = 10663; // Amult8 -> Cmult15
    (Bmult[8] => Cmult[15]) = 14543; // Bmult8 -> Cmult15
    (Amult[8] => Cmult[16]) = 10564; // Amult8 -> Cmult16
    (Bmult[8] => Cmult[16]) = 14716; // Bmult8 -> Cmult16
    (Amult[8] => Cmult[17]) = 10736; // Amult8 -> Cmult17
    (Bmult[8] => Cmult[17]) = 15098; // Bmult8 -> Cmult17
    (Amult[8] => Cmult[18]) = 11018; // Amult8 -> Cmult18
    (Bmult[8] => Cmult[18]) = 14705; // Bmult8 -> Cmult18
    (Amult[8] => Cmult[19]) = 11344; // Amult8 -> Cmult19
    (Bmult[8] => Cmult[19]) = 14974; // Bmult8 -> Cmult19
    (Amult[8] => Cmult[20]) = 11767; // Amult8 -> Cmult20
    (Bmult[8] => Cmult[20]) = 15398; // Bmult8 -> Cmult20
    (Amult[8] => Cmult[21]) = 12087; // Amult8 -> Cmult21
    (Bmult[8] => Cmult[21]) = 15717; // Bmult8 -> Cmult21
    (Amult[8] => Cmult[22]) = 12358; // Amult8 -> Cmult22
    (Bmult[8] => Cmult[22]) = 15972; // Bmult8 -> Cmult22
    (Amult[8] => Cmult[23]) = 12555; // Amult8 -> Cmult23
    (Bmult[8] => Cmult[23]) = 16185; // Bmult8 -> Cmult23
    (Amult[8] => Cmult[24]) = 12517; // Amult8 -> Cmult24
    (Bmult[8] => Cmult[24]) = 16455; // Bmult8 -> Cmult24
    (Amult[8] => Cmult[25]) = 12694; // Amult8 -> Cmult25
    (Bmult[8] => Cmult[25]) = 16859; // Bmult8 -> Cmult25
    (Amult[8] => Cmult[26]) = 13460; // Amult8 -> Cmult26
    (Bmult[8] => Cmult[26]) = 17142; // Bmult8 -> Cmult26
    (Amult[8] => Cmult[27]) = 13585; // Amult8 -> Cmult27
    (Bmult[8] => Cmult[27]) = 17525; // Bmult8 -> Cmult27
    (Amult[8] => Cmult[28]) = 13929; // Amult8 -> Cmult28
    (Bmult[8] => Cmult[28]) = 18049; // Bmult8 -> Cmult28
    (Amult[8] => Cmult[29]) = 14240; // Amult8 -> Cmult29
    (Bmult[8] => Cmult[29]) = 18487; // Bmult8 -> Cmult29
    (Amult[8] => Cmult[30]) = 14929; // Amult8 -> Cmult30
    (Bmult[8] => Cmult[30]) = 19053; // Bmult8 -> Cmult30
    (Amult[8] => Cmult[31]) = 15673; // Amult8 -> Cmult31
    (Bmult[8] => Cmult[31]) = 19864; // Bmult8 -> Cmult31
    (Amult[8] => Cmult[32]) = 21569; // Amult8 -> Cmult32
    (Bmult[8] => Cmult[32]) = 24239; // Bmult8 -> Cmult32
    (Amult[8] => Cmult[33]) = 21906; // Amult8 -> Cmult33
    (Bmult[8] => Cmult[33]) = 24463; // Bmult8 -> Cmult33
    (Amult[8] => Cmult[34]) = 22181; // Amult8 -> Cmult34
    (Bmult[8] => Cmult[34]) = 24966; // Bmult8 -> Cmult34
    (Amult[8] => Cmult[35]) = 22431; // Amult8 -> Cmult35
    (Bmult[8] => Cmult[35]) = 25082; // Bmult8 -> Cmult35
    (Amult[8] => Cmult[36]) = 22498; // Amult8 -> Cmult36
    (Bmult[8] => Cmult[36]) = 25589; // Bmult8 -> Cmult36
    (Amult[8] => Cmult[37]) = 22690; // Amult8 -> Cmult37
    (Bmult[8] => Cmult[37]) = 25630; // Bmult8 -> Cmult37
    (Amult[8] => Cmult[38]) = 22666; // Amult8 -> Cmult38
    (Bmult[8] => Cmult[38]) = 26067; // Bmult8 -> Cmult38
    (Amult[8] => Cmult[39]) = 22904; // Amult8 -> Cmult39
    (Bmult[8] => Cmult[39]) = 26368; // Bmult8 -> Cmult39
    (Amult[8] => Cmult[40]) = 23345; // Amult8 -> Cmult40
    (Bmult[8] => Cmult[40]) = 26572; // Bmult8 -> Cmult40
    (Amult[8] => Cmult[41]) = 23364; // Amult8 -> Cmult41
    (Bmult[8] => Cmult[41]) = 26818; // Bmult8 -> Cmult41
    (Amult[8] => Cmult[42]) = 22906; // Amult8 -> Cmult42
    (Bmult[8] => Cmult[42]) = 26250; // Bmult8 -> Cmult42
    (Amult[8] => Cmult[43]) = 23442; // Amult8 -> Cmult43
    (Bmult[8] => Cmult[43]) = 26940; // Bmult8 -> Cmult43
    (Amult[8] => Cmult[44]) = 24133; // Amult8 -> Cmult44
    (Bmult[8] => Cmult[44]) = 27346; // Bmult8 -> Cmult44
    (Amult[8] => Cmult[45]) = 24059; // Amult8 -> Cmult45
    (Bmult[8] => Cmult[45]) = 27555; // Bmult8 -> Cmult45
    (Amult[8] => Cmult[46]) = 23617; // Amult8 -> Cmult46
    (Bmult[8] => Cmult[46]) = 26945; // Bmult8 -> Cmult46
    (Amult[8] => Cmult[47]) = 23427; // Amult8 -> Cmult47
    (Bmult[8] => Cmult[47]) = 26881; // Bmult8 -> Cmult47
    (Amult[8] => Cmult[48]) = 24496; // Amult8 -> Cmult48
    (Bmult[8] => Cmult[48]) = 27867; // Bmult8 -> Cmult48
    (Amult[8] => Cmult[49]) = 24290; // Amult8 -> Cmult49
    (Bmult[8] => Cmult[49]) = 27686; // Bmult8 -> Cmult49
    (Amult[8] => Cmult[50]) = 25028; // Amult8 -> Cmult50
    (Bmult[8] => Cmult[50]) = 28476; // Bmult8 -> Cmult50
    (Amult[8] => Cmult[51]) = 25379; // Amult8 -> Cmult51
    (Bmult[8] => Cmult[51]) = 28668; // Bmult8 -> Cmult51
    (Amult[8] => Cmult[52]) = 26057; // Amult8 -> Cmult52
    (Bmult[8] => Cmult[52]) = 29322; // Bmult8 -> Cmult52
    (Amult[8] => Cmult[53]) = 26330; // Amult8 -> Cmult53
    (Bmult[8] => Cmult[53]) = 29554; // Bmult8 -> Cmult53
    (Amult[8] => Cmult[54]) = 26695; // Amult8 -> Cmult54
    (Bmult[8] => Cmult[54]) = 29979; // Bmult8 -> Cmult54
    (Amult[8] => Cmult[55]) = 26867; // Amult8 -> Cmult55
    (Bmult[8] => Cmult[55]) = 30072; // Bmult8 -> Cmult55
    (Amult[8] => Cmult[56]) = 27432; // Amult8 -> Cmult56
    (Bmult[8] => Cmult[56]) = 30660; // Bmult8 -> Cmult56
    (Amult[8] => Cmult[57]) = 27585; // Amult8 -> Cmult57
    (Bmult[8] => Cmult[57]) = 30946; // Bmult8 -> Cmult57
    (Amult[8] => Cmult[58]) = 27949; // Amult8 -> Cmult58
    (Bmult[8] => Cmult[58]) = 31404; // Bmult8 -> Cmult58
    (Amult[8] => Cmult[59]) = 28119; // Amult8 -> Cmult59
    (Bmult[8] => Cmult[59]) = 31472; // Bmult8 -> Cmult59
    (Amult[8] => Cmult[60]) = 28542; // Amult8 -> Cmult60
    (Bmult[8] => Cmult[60]) = 32035; // Bmult8 -> Cmult60
    (Amult[8] => Cmult[61]) = 28795; // Amult8 -> Cmult61
    (Bmult[8] => Cmult[61]) = 32014; // Bmult8 -> Cmult61
    (Amult[8] => Cmult[62]) = 29334; // Amult8 -> Cmult62
    (Bmult[8] => Cmult[62]) = 32829; // Bmult8 -> Cmult62
    (Amult[8] => Cmult[63]) = 30429; // Amult8 -> Cmult63
    (Bmult[8] => Cmult[63]) = 33923; // Bmult8 -> Cmult63
    (Amult[9] => Cmult[9]) = 5552; // Amult9 -> Cmult9
    (Bmult[9] => Cmult[9]) = 10553; // Bmult9 -> Cmult9
    (Amult[9] => Cmult[10]) = 5919; // Amult9 -> Cmult10
    (Bmult[9] => Cmult[10]) = 11339; // Bmult9 -> Cmult10
    (Amult[9] => Cmult[11]) = 6551; // Amult9 -> Cmult11
    (Bmult[9] => Cmult[11]) = 11833; // Bmult9 -> Cmult11
    (Amult[9] => Cmult[12]) = 7126; // Amult9 -> Cmult12
    (Bmult[9] => Cmult[12]) = 12183; // Bmult9 -> Cmult12
    (Amult[9] => Cmult[13]) = 7745; // Amult9 -> Cmult13
    (Bmult[9] => Cmult[13]) = 12844; // Bmult9 -> Cmult13
    (Amult[9] => Cmult[14]) = 8273; // Amult9 -> Cmult14
    (Bmult[9] => Cmult[14]) = 13481; // Bmult9 -> Cmult14
    (Amult[9] => Cmult[15]) = 9886; // Amult9 -> Cmult15
    (Bmult[9] => Cmult[15]) = 14861; // Bmult9 -> Cmult15
    (Amult[9] => Cmult[16]) = 9758; // Amult9 -> Cmult16
    (Bmult[9] => Cmult[16]) = 15034; // Bmult9 -> Cmult16
    (Amult[9] => Cmult[17]) = 10033; // Amult9 -> Cmult17
    (Bmult[9] => Cmult[17]) = 15416; // Bmult9 -> Cmult17
    (Amult[9] => Cmult[18]) = 10355; // Amult9 -> Cmult18
    (Bmult[9] => Cmult[18]) = 15042; // Bmult9 -> Cmult18
    (Amult[9] => Cmult[19]) = 10681; // Amult9 -> Cmult19
    (Bmult[9] => Cmult[19]) = 15369; // Bmult9 -> Cmult19
    (Amult[9] => Cmult[20]) = 11105; // Amult9 -> Cmult20
    (Bmult[9] => Cmult[20]) = 15792; // Bmult9 -> Cmult20
    (Amult[9] => Cmult[21]) = 11424; // Amult9 -> Cmult21
    (Bmult[9] => Cmult[21]) = 16111; // Bmult9 -> Cmult21
    (Amult[9] => Cmult[22]) = 11679; // Amult9 -> Cmult22
    (Bmult[9] => Cmult[22]) = 16367; // Bmult9 -> Cmult22
    (Amult[9] => Cmult[23]) = 11892; // Amult9 -> Cmult23
    (Bmult[9] => Cmult[23]) = 16579; // Bmult9 -> Cmult23
    (Amult[9] => Cmult[24]) = 11783; // Amult9 -> Cmult24
    (Bmult[9] => Cmult[24]) = 16730; // Bmult9 -> Cmult24
    (Amult[9] => Cmult[25]) = 12031; // Amult9 -> Cmult25
    (Bmult[9] => Cmult[25]) = 17133; // Bmult9 -> Cmult25
    (Amult[9] => Cmult[26]) = 12726; // Amult9 -> Cmult26
    (Bmult[9] => Cmult[26]) = 17411; // Bmult9 -> Cmult26
    (Amult[9] => Cmult[27]) = 12923; // Amult9 -> Cmult27
    (Bmult[9] => Cmult[27]) = 17800; // Bmult9 -> Cmult27
    (Amult[9] => Cmult[28]) = 13195; // Amult9 -> Cmult28
    (Bmult[9] => Cmult[28]) = 18324; // Bmult9 -> Cmult28
    (Amult[9] => Cmult[29]) = 13552; // Amult9 -> Cmult29
    (Bmult[9] => Cmult[29]) = 18762; // Bmult9 -> Cmult29
    (Amult[9] => Cmult[30]) = 14203; // Amult9 -> Cmult30
    (Bmult[9] => Cmult[30]) = 19328; // Bmult9 -> Cmult30
    (Amult[9] => Cmult[31]) = 15010; // Amult9 -> Cmult31
    (Bmult[9] => Cmult[31]) = 20139; // Bmult9 -> Cmult31
    (Amult[9] => Cmult[32]) = 20494; // Amult9 -> Cmult32
    (Bmult[9] => Cmult[32]) = 24348; // Bmult9 -> Cmult32
    (Amult[9] => Cmult[33]) = 20816; // Amult9 -> Cmult33
    (Bmult[9] => Cmult[33]) = 24534; // Bmult9 -> Cmult33
    (Amult[9] => Cmult[34]) = 21091; // Amult9 -> Cmult34
    (Bmult[9] => Cmult[34]) = 25024; // Bmult9 -> Cmult34
    (Amult[9] => Cmult[35]) = 21341; // Amult9 -> Cmult35
    (Bmult[9] => Cmult[35]) = 25140; // Bmult9 -> Cmult35
    (Amult[9] => Cmult[36]) = 21621; // Amult9 -> Cmult36
    (Bmult[9] => Cmult[36]) = 25647; // Bmult9 -> Cmult36
    (Amult[9] => Cmult[37]) = 21792; // Amult9 -> Cmult37
    (Bmult[9] => Cmult[37]) = 25752; // Bmult9 -> Cmult37
    (Amult[9] => Cmult[38]) = 22099; // Amult9 -> Cmult38
    (Bmult[9] => Cmult[38]) = 26124; // Bmult9 -> Cmult38
    (Amult[9] => Cmult[39]) = 22400; // Amult9 -> Cmult39
    (Bmult[9] => Cmult[39]) = 26425; // Bmult9 -> Cmult39
    (Amult[9] => Cmult[40]) = 22625; // Amult9 -> Cmult40
    (Bmult[9] => Cmult[40]) = 26630; // Bmult9 -> Cmult40
    (Amult[9] => Cmult[41]) = 22850; // Amult9 -> Cmult41
    (Bmult[9] => Cmult[41]) = 26875; // Bmult9 -> Cmult41
    (Amult[9] => Cmult[42]) = 22282; // Amult9 -> Cmult42
    (Bmult[9] => Cmult[42]) = 26308; // Bmult9 -> Cmult42
    (Amult[9] => Cmult[43]) = 22972; // Amult9 -> Cmult43
    (Bmult[9] => Cmult[43]) = 26998; // Bmult9 -> Cmult43
    (Amult[9] => Cmult[44]) = 23501; // Amult9 -> Cmult44
    (Bmult[9] => Cmult[44]) = 27461; // Bmult9 -> Cmult44
    (Amult[9] => Cmult[45]) = 23588; // Amult9 -> Cmult45
    (Bmult[9] => Cmult[45]) = 27613; // Bmult9 -> Cmult45
    (Amult[9] => Cmult[46]) = 22985; // Amult9 -> Cmult46
    (Bmult[9] => Cmult[46]) = 27003; // Bmult9 -> Cmult46
    (Amult[9] => Cmult[47]) = 22921; // Amult9 -> Cmult47
    (Bmult[9] => Cmult[47]) = 26946; // Bmult9 -> Cmult47
    (Amult[9] => Cmult[48]) = 23899; // Amult9 -> Cmult48
    (Bmult[9] => Cmult[48]) = 27925; // Bmult9 -> Cmult48
    (Amult[9] => Cmult[49]) = 23735; // Amult9 -> Cmult49
    (Bmult[9] => Cmult[49]) = 27752; // Bmult9 -> Cmult49
    (Amult[9] => Cmult[50]) = 24509; // Amult9 -> Cmult50
    (Bmult[9] => Cmult[50]) = 28534; // Bmult9 -> Cmult50
    (Amult[9] => Cmult[51]) = 24747; // Amult9 -> Cmult51
    (Bmult[9] => Cmult[51]) = 28726; // Bmult9 -> Cmult51
    (Amult[9] => Cmult[52]) = 25355; // Amult9 -> Cmult52
    (Bmult[9] => Cmult[52]) = 29380; // Bmult9 -> Cmult52
    (Amult[9] => Cmult[53]) = 25698; // Amult9 -> Cmult53
    (Bmult[9] => Cmult[53]) = 29658; // Bmult9 -> Cmult53
    (Amult[9] => Cmult[54]) = 26012; // Amult9 -> Cmult54
    (Bmult[9] => Cmult[54]) = 30037; // Bmult9 -> Cmult54
    (Amult[9] => Cmult[55]) = 26235; // Amult9 -> Cmult55
    (Bmult[9] => Cmult[55]) = 30195; // Bmult9 -> Cmult55
    (Amult[9] => Cmult[56]) = 26694; // Amult9 -> Cmult56
    (Bmult[9] => Cmult[56]) = 30718; // Bmult9 -> Cmult56
    (Amult[9] => Cmult[57]) = 26979; // Amult9 -> Cmult57
    (Bmult[9] => Cmult[57]) = 31003; // Bmult9 -> Cmult57
    (Amult[9] => Cmult[58]) = 27437; // Amult9 -> Cmult58
    (Bmult[9] => Cmult[58]) = 31462; // Bmult9 -> Cmult58
    (Amult[9] => Cmult[59]) = 27506; // Amult9 -> Cmult59
    (Bmult[9] => Cmult[59]) = 31530; // Bmult9 -> Cmult59
    (Amult[9] => Cmult[60]) = 28068; // Amult9 -> Cmult60
    (Bmult[9] => Cmult[60]) = 32092; // Bmult9 -> Cmult60
    (Amult[9] => Cmult[61]) = 28163; // Amult9 -> Cmult61
    (Bmult[9] => Cmult[61]) = 32122; // Bmult9 -> Cmult61
    (Amult[9] => Cmult[62]) = 28864; // Amult9 -> Cmult62
    (Bmult[9] => Cmult[62]) = 32887; // Bmult9 -> Cmult62
    (Amult[9] => Cmult[63]) = 29959; // Amult9 -> Cmult63
    (Bmult[9] => Cmult[63]) = 33981; // Bmult9 -> Cmult63
    (Amult[10] => Cmult[1]) = 5408; // Amult10 -> Cmult1
    (Bmult[10] => Cmult[1]) = 5012; // Bmult10 -> Cmult1
    (Amult[10] => Cmult[2]) = 6490; // Amult10 -> Cmult2
    (Bmult[10] => Cmult[2]) = 5998; // Bmult10 -> Cmult2
    (Amult[10] => Cmult[3]) = 6767; // Amult10 -> Cmult3
    (Bmult[10] => Cmult[3]) = 6258; // Bmult10 -> Cmult3
    (Amult[10] => Cmult[4]) = 7470; // Amult10 -> Cmult4
    (Bmult[10] => Cmult[4]) = 6721; // Bmult10 -> Cmult4
    (Amult[10] => Cmult[5]) = 8398; // Amult10 -> Cmult5
    (Bmult[10] => Cmult[5]) = 7383; // Bmult10 -> Cmult5
    (Amult[10] => Cmult[6]) = 9281; // Amult10 -> Cmult6
    (Bmult[10] => Cmult[6]) = 7827; // Bmult10 -> Cmult6
    (Amult[10] => Cmult[7]) = 9472; // Amult10 -> Cmult7
    (Bmult[10] => Cmult[7]) = 8516; // Bmult10 -> Cmult7
    (Amult[10] => Cmult[8]) = 10829; // Amult10 -> Cmult8
    (Bmult[10] => Cmult[8]) = 9292; // Bmult10 -> Cmult8
    (Amult[10] => Cmult[9]) = 11136; // Amult10 -> Cmult9
    (Bmult[10] => Cmult[9]) = 9817; // Bmult10 -> Cmult9
    (Amult[10] => Cmult[10]) = 11561; // Amult10 -> Cmult10
    (Bmult[10] => Cmult[10]) = 11196; // Bmult10 -> Cmult10
    (Amult[10] => Cmult[11]) = 12105; // Amult10 -> Cmult11
    (Bmult[10] => Cmult[11]) = 11861; // Bmult10 -> Cmult11
    (Amult[10] => Cmult[12]) = 12679; // Amult10 -> Cmult12
    (Bmult[10] => Cmult[12]) = 12185; // Bmult10 -> Cmult12
    (Amult[10] => Cmult[13]) = 13520; // Amult10 -> Cmult13
    (Bmult[10] => Cmult[13]) = 12862; // Bmult10 -> Cmult13
    (Amult[10] => Cmult[14]) = 14048; // Amult10 -> Cmult14
    (Bmult[10] => Cmult[14]) = 13431; // Bmult10 -> Cmult14
    (Amult[10] => Cmult[15]) = 15613; // Amult10 -> Cmult15
    (Bmult[10] => Cmult[15]) = 14811; // Bmult10 -> Cmult15
    (Amult[10] => Cmult[16]) = 15514; // Amult10 -> Cmult16
    (Bmult[10] => Cmult[16]) = 14985; // Bmult10 -> Cmult16
    (Amult[10] => Cmult[17]) = 15705; // Amult10 -> Cmult17
    (Bmult[10] => Cmult[17]) = 15366; // Bmult10 -> Cmult17
    (Amult[10] => Cmult[18]) = 16067; // Amult10 -> Cmult18
    (Bmult[10] => Cmult[18]) = 15123; // Bmult10 -> Cmult18
    (Amult[10] => Cmult[19]) = 16393; // Amult10 -> Cmult19
    (Bmult[10] => Cmult[19]) = 15449; // Bmult10 -> Cmult19
    (Amult[10] => Cmult[20]) = 16816; // Amult10 -> Cmult20
    (Bmult[10] => Cmult[20]) = 15873; // Bmult10 -> Cmult20
    (Amult[10] => Cmult[21]) = 17136; // Amult10 -> Cmult21
    (Bmult[10] => Cmult[21]) = 16192; // Bmult10 -> Cmult21
    (Amult[10] => Cmult[22]) = 17391; // Amult10 -> Cmult22
    (Bmult[10] => Cmult[22]) = 16447; // Bmult10 -> Cmult22
    (Amult[10] => Cmult[23]) = 17604; // Amult10 -> Cmult23
    (Bmult[10] => Cmult[23]) = 16660; // Bmult10 -> Cmult23
    (Amult[10] => Cmult[24]) = 17476; // Amult10 -> Cmult24
    (Bmult[10] => Cmult[24]) = 16680; // Bmult10 -> Cmult24
    (Amult[10] => Cmult[25]) = 17743; // Amult10 -> Cmult25
    (Bmult[10] => Cmult[25]) = 17083; // Bmult10 -> Cmult25
    (Amult[10] => Cmult[26]) = 18433; // Amult10 -> Cmult26
    (Bmult[10] => Cmult[26]) = 17489; // Bmult10 -> Cmult26
    (Amult[10] => Cmult[27]) = 18635; // Amult10 -> Cmult27
    (Bmult[10] => Cmult[27]) = 17750; // Bmult10 -> Cmult27
    (Amult[10] => Cmult[28]) = 18893; // Amult10 -> Cmult28
    (Bmult[10] => Cmult[28]) = 18274; // Bmult10 -> Cmult28
    (Amult[10] => Cmult[29]) = 19237; // Amult10 -> Cmult29
    (Bmult[10] => Cmult[29]) = 18712; // Bmult10 -> Cmult29
    (Amult[10] => Cmult[30]) = 19915; // Amult10 -> Cmult30
    (Bmult[10] => Cmult[30]) = 19279; // Bmult10 -> Cmult30
    (Amult[10] => Cmult[31]) = 20722; // Amult10 -> Cmult31
    (Bmult[10] => Cmult[31]) = 20089; // Bmult10 -> Cmult31
    (Amult[10] => Cmult[32]) = 26095; // Amult10 -> Cmult32
    (Bmult[10] => Cmult[32]) = 24403; // Bmult10 -> Cmult32
    (Amult[10] => Cmult[33]) = 26417; // Amult10 -> Cmult33
    (Bmult[10] => Cmult[33]) = 24636; // Bmult10 -> Cmult33
    (Amult[10] => Cmult[34]) = 26691; // Amult10 -> Cmult34
    (Bmult[10] => Cmult[34]) = 25131; // Bmult10 -> Cmult34
    (Amult[10] => Cmult[35]) = 26942; // Amult10 -> Cmult35
    (Bmult[10] => Cmult[35]) = 25247; // Bmult10 -> Cmult35
    (Amult[10] => Cmult[36]) = 27112; // Amult10 -> Cmult36
    (Bmult[10] => Cmult[36]) = 25754; // Bmult10 -> Cmult36
    (Amult[10] => Cmult[37]) = 27211; // Amult10 -> Cmult37
    (Bmult[10] => Cmult[37]) = 25802; // Bmult10 -> Cmult37
    (Amult[10] => Cmult[38]) = 27590; // Amult10 -> Cmult38
    (Bmult[10] => Cmult[38]) = 26231; // Bmult10 -> Cmult38
    (Amult[10] => Cmult[39]) = 27891; // Amult10 -> Cmult39
    (Bmult[10] => Cmult[39]) = 26533; // Bmult10 -> Cmult39
    (Amult[10] => Cmult[40]) = 28095; // Amult10 -> Cmult40
    (Bmult[10] => Cmult[40]) = 26737; // Bmult10 -> Cmult40
    (Amult[10] => Cmult[41]) = 28341; // Amult10 -> Cmult41
    (Bmult[10] => Cmult[41]) = 26982; // Bmult10 -> Cmult41
    (Amult[10] => Cmult[42]) = 27773; // Amult10 -> Cmult42
    (Bmult[10] => Cmult[42]) = 26415; // Bmult10 -> Cmult42
    (Amult[10] => Cmult[43]) = 28463; // Amult10 -> Cmult43
    (Bmult[10] => Cmult[43]) = 27105; // Bmult10 -> Cmult43
    (Amult[10] => Cmult[44]) = 28921; // Amult10 -> Cmult44
    (Bmult[10] => Cmult[44]) = 27512; // Bmult10 -> Cmult44
    (Amult[10] => Cmult[45]) = 29079; // Amult10 -> Cmult45
    (Bmult[10] => Cmult[45]) = 27720; // Bmult10 -> Cmult45
    (Amult[10] => Cmult[46]) = 28469; // Amult10 -> Cmult46
    (Bmult[10] => Cmult[46]) = 27110; // Bmult10 -> Cmult46
    (Amult[10] => Cmult[47]) = 28411; // Amult10 -> Cmult47
    (Bmult[10] => Cmult[47]) = 27053; // Bmult10 -> Cmult47
    (Amult[10] => Cmult[48]) = 29390; // Amult10 -> Cmult48
    (Bmult[10] => Cmult[48]) = 28032; // Bmult10 -> Cmult48
    (Amult[10] => Cmult[49]) = 29226; // Amult10 -> Cmult49
    (Bmult[10] => Cmult[49]) = 27859; // Bmult10 -> Cmult49
    (Amult[10] => Cmult[50]) = 30000; // Amult10 -> Cmult50
    (Bmult[10] => Cmult[50]) = 28641; // Bmult10 -> Cmult50
    (Amult[10] => Cmult[51]) = 30193; // Amult10 -> Cmult51
    (Bmult[10] => Cmult[51]) = 28833; // Bmult10 -> Cmult51
    (Amult[10] => Cmult[52]) = 30846; // Amult10 -> Cmult52
    (Bmult[10] => Cmult[52]) = 29487; // Bmult10 -> Cmult52
    (Amult[10] => Cmult[53]) = 31118; // Amult10 -> Cmult53
    (Bmult[10] => Cmult[53]) = 29719; // Bmult10 -> Cmult53
    (Amult[10] => Cmult[54]) = 31503; // Amult10 -> Cmult54
    (Bmult[10] => Cmult[54]) = 30144; // Bmult10 -> Cmult54
    (Amult[10] => Cmult[55]) = 31655; // Amult10 -> Cmult55
    (Bmult[10] => Cmult[55]) = 30245; // Bmult10 -> Cmult55
    (Amult[10] => Cmult[56]) = 32184; // Amult10 -> Cmult56
    (Bmult[10] => Cmult[56]) = 30825; // Bmult10 -> Cmult56
    (Amult[10] => Cmult[57]) = 32470; // Amult10 -> Cmult57
    (Bmult[10] => Cmult[57]) = 31110; // Bmult10 -> Cmult57
    (Amult[10] => Cmult[58]) = 32928; // Amult10 -> Cmult58
    (Bmult[10] => Cmult[58]) = 31569; // Bmult10 -> Cmult58
    (Amult[10] => Cmult[59]) = 32997; // Amult10 -> Cmult59
    (Bmult[10] => Cmult[59]) = 31637; // Bmult10 -> Cmult59
    (Amult[10] => Cmult[60]) = 33559; // Amult10 -> Cmult60
    (Bmult[10] => Cmult[60]) = 32200; // Bmult10 -> Cmult60
    (Amult[10] => Cmult[61]) = 33582; // Amult10 -> Cmult61
    (Bmult[10] => Cmult[61]) = 32179; // Bmult10 -> Cmult61
    (Amult[10] => Cmult[62]) = 34355; // Amult10 -> Cmult62
    (Bmult[10] => Cmult[62]) = 32994; // Bmult10 -> Cmult62
    (Amult[10] => Cmult[63]) = 35450; // Amult10 -> Cmult63
    (Bmult[10] => Cmult[63]) = 34088; // Bmult10 -> Cmult63
    (Amult[11] => Cmult[1]) = 5408; // Amult11 -> Cmult1
    (Bmult[11] => Cmult[1]) = 5012; // Bmult11 -> Cmult1
    (Amult[11] => Cmult[2]) = 6490; // Amult11 -> Cmult2
    (Bmult[11] => Cmult[2]) = 5998; // Bmult11 -> Cmult2
    (Amult[11] => Cmult[3]) = 6767; // Amult11 -> Cmult3
    (Bmult[11] => Cmult[3]) = 6258; // Bmult11 -> Cmult3
    (Amult[11] => Cmult[4]) = 7470; // Amult11 -> Cmult4
    (Bmult[11] => Cmult[4]) = 6721; // Bmult11 -> Cmult4
    (Amult[11] => Cmult[5]) = 8398; // Amult11 -> Cmult5
    (Bmult[11] => Cmult[5]) = 7383; // Bmult11 -> Cmult5
    (Amult[11] => Cmult[6]) = 9281; // Amult11 -> Cmult6
    (Bmult[11] => Cmult[6]) = 7827; // Bmult11 -> Cmult6
    (Amult[11] => Cmult[7]) = 9472; // Amult11 -> Cmult7
    (Bmult[11] => Cmult[7]) = 8516; // Bmult11 -> Cmult7
    (Amult[11] => Cmult[8]) = 10829; // Amult11 -> Cmult8
    (Bmult[11] => Cmult[8]) = 9292; // Bmult11 -> Cmult8
    (Amult[11] => Cmult[9]) = 11136; // Amult11 -> Cmult9
    (Bmult[11] => Cmult[9]) = 9817; // Bmult11 -> Cmult9
    (Amult[11] => Cmult[10]) = 11561; // Amult11 -> Cmult10
    (Bmult[11] => Cmult[10]) = 10465; // Bmult11 -> Cmult10
    (Amult[11] => Cmult[11]) = 12105; // Amult11 -> Cmult11
    (Bmult[11] => Cmult[11]) = 11584; // Bmult11 -> Cmult11
    (Amult[11] => Cmult[12]) = 12679; // Amult11 -> Cmult12
    (Bmult[11] => Cmult[12]) = 11933; // Bmult11 -> Cmult12
    (Amult[11] => Cmult[13]) = 13520; // Amult11 -> Cmult13
    (Bmult[11] => Cmult[13]) = 12739; // Bmult11 -> Cmult13
    (Amult[11] => Cmult[14]) = 14048; // Amult11 -> Cmult14
    (Bmult[11] => Cmult[14]) = 13402; // Bmult11 -> Cmult14
    (Amult[11] => Cmult[15]) = 15613; // Amult11 -> Cmult15
    (Bmult[11] => Cmult[15]) = 14781; // Bmult11 -> Cmult15
    (Amult[11] => Cmult[16]) = 15514; // Amult11 -> Cmult16
    (Bmult[11] => Cmult[16]) = 14955; // Bmult11 -> Cmult16
    (Amult[11] => Cmult[17]) = 15705; // Amult11 -> Cmult17
    (Bmult[11] => Cmult[17]) = 15336; // Bmult11 -> Cmult17
    (Amult[11] => Cmult[18]) = 16067; // Amult11 -> Cmult18
    (Bmult[11] => Cmult[18]) = 15001; // Bmult11 -> Cmult18
    (Amult[11] => Cmult[19]) = 16393; // Amult11 -> Cmult19
    (Bmult[11] => Cmult[19]) = 15327; // Bmult11 -> Cmult19
    (Amult[11] => Cmult[20]) = 16816; // Amult11 -> Cmult20
    (Bmult[11] => Cmult[20]) = 15751; // Bmult11 -> Cmult20
    (Amult[11] => Cmult[21]) = 17136; // Amult11 -> Cmult21
    (Bmult[11] => Cmult[21]) = 16070; // Bmult11 -> Cmult21
    (Amult[11] => Cmult[22]) = 17391; // Amult11 -> Cmult22
    (Bmult[11] => Cmult[22]) = 16325; // Bmult11 -> Cmult22
    (Amult[11] => Cmult[23]) = 17604; // Amult11 -> Cmult23
    (Bmult[11] => Cmult[23]) = 16538; // Bmult11 -> Cmult23
    (Amult[11] => Cmult[24]) = 17476; // Amult11 -> Cmult24
    (Bmult[11] => Cmult[24]) = 16650; // Bmult11 -> Cmult24
    (Amult[11] => Cmult[25]) = 17743; // Amult11 -> Cmult25
    (Bmult[11] => Cmult[25]) = 17054; // Bmult11 -> Cmult25
    (Amult[11] => Cmult[26]) = 18433; // Amult11 -> Cmult26
    (Bmult[11] => Cmult[26]) = 17367; // Bmult11 -> Cmult26
    (Amult[11] => Cmult[27]) = 18635; // Amult11 -> Cmult27
    (Bmult[11] => Cmult[27]) = 17721; // Bmult11 -> Cmult27
    (Amult[11] => Cmult[28]) = 18893; // Amult11 -> Cmult28
    (Bmult[11] => Cmult[28]) = 18245; // Bmult11 -> Cmult28
    (Amult[11] => Cmult[29]) = 19237; // Amult11 -> Cmult29
    (Bmult[11] => Cmult[29]) = 18683; // Bmult11 -> Cmult29
    (Amult[11] => Cmult[30]) = 19915; // Amult11 -> Cmult30
    (Bmult[11] => Cmult[30]) = 19249; // Bmult11 -> Cmult30
    (Amult[11] => Cmult[31]) = 20722; // Amult11 -> Cmult31
    (Bmult[11] => Cmult[31]) = 20060; // Bmult11 -> Cmult31
    (Amult[11] => Cmult[32]) = 26095; // Amult11 -> Cmult32
    (Bmult[11] => Cmult[32]) = 24459; // Bmult11 -> Cmult32
    (Amult[11] => Cmult[33]) = 26417; // Amult11 -> Cmult33
    (Bmult[11] => Cmult[33]) = 24711; // Bmult11 -> Cmult33
    (Amult[11] => Cmult[34]) = 26691; // Amult11 -> Cmult34
    (Bmult[11] => Cmult[34]) = 25187; // Bmult11 -> Cmult34
    (Amult[11] => Cmult[35]) = 26942; // Amult11 -> Cmult35
    (Bmult[11] => Cmult[35]) = 25302; // Bmult11 -> Cmult35
    (Amult[11] => Cmult[36]) = 27112; // Amult11 -> Cmult36
    (Bmult[11] => Cmult[36]) = 25809; // Bmult11 -> Cmult36
    (Amult[11] => Cmult[37]) = 27211; // Amult11 -> Cmult37
    (Bmult[11] => Cmult[37]) = 25850; // Bmult11 -> Cmult37
    (Amult[11] => Cmult[38]) = 27590; // Amult11 -> Cmult38
    (Bmult[11] => Cmult[38]) = 26287; // Bmult11 -> Cmult38
    (Amult[11] => Cmult[39]) = 27891; // Amult11 -> Cmult39
    (Bmult[11] => Cmult[39]) = 26588; // Bmult11 -> Cmult39
    (Amult[11] => Cmult[40]) = 28095; // Amult11 -> Cmult40
    (Bmult[11] => Cmult[40]) = 26792; // Bmult11 -> Cmult40
    (Amult[11] => Cmult[41]) = 28341; // Amult11 -> Cmult41
    (Bmult[11] => Cmult[41]) = 27038; // Bmult11 -> Cmult41
    (Amult[11] => Cmult[42]) = 27773; // Amult11 -> Cmult42
    (Bmult[11] => Cmult[42]) = 26470; // Bmult11 -> Cmult42
    (Amult[11] => Cmult[43]) = 28463; // Amult11 -> Cmult43
    (Bmult[11] => Cmult[43]) = 27160; // Bmult11 -> Cmult43
    (Amult[11] => Cmult[44]) = 28921; // Amult11 -> Cmult44
    (Bmult[11] => Cmult[44]) = 27567; // Bmult11 -> Cmult44
    (Amult[11] => Cmult[45]) = 29079; // Amult11 -> Cmult45
    (Bmult[11] => Cmult[45]) = 27776; // Bmult11 -> Cmult45
    (Amult[11] => Cmult[46]) = 28469; // Amult11 -> Cmult46
    (Bmult[11] => Cmult[46]) = 27165; // Bmult11 -> Cmult46
    (Amult[11] => Cmult[47]) = 28411; // Amult11 -> Cmult47
    (Bmult[11] => Cmult[47]) = 27108; // Bmult11 -> Cmult47
    (Amult[11] => Cmult[48]) = 29390; // Amult11 -> Cmult48
    (Bmult[11] => Cmult[48]) = 28087; // Bmult11 -> Cmult48
    (Amult[11] => Cmult[49]) = 29226; // Amult11 -> Cmult49
    (Bmult[11] => Cmult[49]) = 27914; // Bmult11 -> Cmult49
    (Amult[11] => Cmult[50]) = 30000; // Amult11 -> Cmult50
    (Bmult[11] => Cmult[50]) = 28696; // Bmult11 -> Cmult50
    (Amult[11] => Cmult[51]) = 30193; // Amult11 -> Cmult51
    (Bmult[11] => Cmult[51]) = 28889; // Bmult11 -> Cmult51
    (Amult[11] => Cmult[52]) = 30846; // Amult11 -> Cmult52
    (Bmult[11] => Cmult[52]) = 29543; // Bmult11 -> Cmult52
    (Amult[11] => Cmult[53]) = 31118; // Amult11 -> Cmult53
    (Bmult[11] => Cmult[53]) = 29774; // Bmult11 -> Cmult53
    (Amult[11] => Cmult[54]) = 31503; // Amult11 -> Cmult54
    (Bmult[11] => Cmult[54]) = 30200; // Bmult11 -> Cmult54
    (Amult[11] => Cmult[55]) = 31655; // Amult11 -> Cmult55
    (Bmult[11] => Cmult[55]) = 30292; // Bmult11 -> Cmult55
    (Amult[11] => Cmult[56]) = 32184; // Amult11 -> Cmult56
    (Bmult[11] => Cmult[56]) = 30881; // Bmult11 -> Cmult56
    (Amult[11] => Cmult[57]) = 32470; // Amult11 -> Cmult57
    (Bmult[11] => Cmult[57]) = 31166; // Bmult11 -> Cmult57
    (Amult[11] => Cmult[58]) = 32928; // Amult11 -> Cmult58
    (Bmult[11] => Cmult[58]) = 31624; // Bmult11 -> Cmult58
    (Amult[11] => Cmult[59]) = 32997; // Amult11 -> Cmult59
    (Bmult[11] => Cmult[59]) = 31692; // Bmult11 -> Cmult59
    (Amult[11] => Cmult[60]) = 33559; // Amult11 -> Cmult60
    (Bmult[11] => Cmult[60]) = 32255; // Bmult11 -> Cmult60
    (Amult[11] => Cmult[61]) = 33582; // Amult11 -> Cmult61
    (Bmult[11] => Cmult[61]) = 32234; // Bmult11 -> Cmult61
    (Amult[11] => Cmult[62]) = 34355; // Amult11 -> Cmult62
    (Bmult[11] => Cmult[62]) = 33050; // Bmult11 -> Cmult62
    (Amult[11] => Cmult[63]) = 35450; // Amult11 -> Cmult63
    (Bmult[11] => Cmult[63]) = 34144; // Bmult11 -> Cmult63
    (Amult[12] => Cmult[1]) = 5408; // Amult12 -> Cmult1
    (Bmult[12] => Cmult[1]) = 5012; // Bmult12 -> Cmult1
    (Amult[12] => Cmult[2]) = 6490; // Amult12 -> Cmult2
    (Bmult[12] => Cmult[2]) = 5998; // Bmult12 -> Cmult2
    (Amult[12] => Cmult[3]) = 6767; // Amult12 -> Cmult3
    (Bmult[12] => Cmult[3]) = 6258; // Bmult12 -> Cmult3
    (Amult[12] => Cmult[4]) = 7470; // Amult12 -> Cmult4
    (Bmult[12] => Cmult[4]) = 6721; // Bmult12 -> Cmult4
    (Amult[12] => Cmult[5]) = 8398; // Amult12 -> Cmult5
    (Bmult[12] => Cmult[5]) = 7383; // Bmult12 -> Cmult5
    (Amult[12] => Cmult[6]) = 9281; // Amult12 -> Cmult6
    (Bmult[12] => Cmult[6]) = 7827; // Bmult12 -> Cmult6
    (Amult[12] => Cmult[7]) = 9472; // Amult12 -> Cmult7
    (Bmult[12] => Cmult[7]) = 8516; // Bmult12 -> Cmult7
    (Amult[12] => Cmult[8]) = 10829; // Amult12 -> Cmult8
    (Bmult[12] => Cmult[8]) = 9292; // Bmult12 -> Cmult8
    (Amult[12] => Cmult[9]) = 11136; // Amult12 -> Cmult9
    (Bmult[12] => Cmult[9]) = 9817; // Bmult12 -> Cmult9
    (Amult[12] => Cmult[10]) = 11561; // Amult12 -> Cmult10
    (Bmult[12] => Cmult[10]) = 10465; // Bmult12 -> Cmult10
    (Amult[12] => Cmult[11]) = 12105; // Amult12 -> Cmult11
    (Bmult[12] => Cmult[11]) = 10895; // Bmult12 -> Cmult11
    (Amult[12] => Cmult[12]) = 12679; // Amult12 -> Cmult12
    (Bmult[12] => Cmult[12]) = 11924; // Bmult12 -> Cmult12
    (Amult[12] => Cmult[13]) = 13520; // Amult12 -> Cmult13
    (Bmult[12] => Cmult[13]) = 12756; // Bmult12 -> Cmult13
    (Amult[12] => Cmult[14]) = 14048; // Amult12 -> Cmult14
    (Bmult[12] => Cmult[14]) = 13403; // Bmult12 -> Cmult14
    (Amult[12] => Cmult[15]) = 15613; // Amult12 -> Cmult15
    (Bmult[12] => Cmult[15]) = 14783; // Bmult12 -> Cmult15
    (Amult[12] => Cmult[16]) = 15514; // Amult12 -> Cmult16
    (Bmult[12] => Cmult[16]) = 14957; // Bmult12 -> Cmult16
    (Amult[12] => Cmult[17]) = 15705; // Amult12 -> Cmult17
    (Bmult[12] => Cmult[17]) = 15338; // Bmult12 -> Cmult17
    (Amult[12] => Cmult[18]) = 16067; // Amult12 -> Cmult18
    (Bmult[12] => Cmult[18]) = 14945; // Bmult12 -> Cmult18
    (Amult[12] => Cmult[19]) = 16393; // Amult12 -> Cmult19
    (Bmult[12] => Cmult[19]) = 15162; // Bmult12 -> Cmult19
    (Amult[12] => Cmult[20]) = 16816; // Amult12 -> Cmult20
    (Bmult[12] => Cmult[20]) = 15585; // Bmult12 -> Cmult20
    (Amult[12] => Cmult[21]) = 17136; // Amult12 -> Cmult21
    (Bmult[12] => Cmult[21]) = 15905; // Bmult12 -> Cmult21
    (Amult[12] => Cmult[22]) = 17391; // Amult12 -> Cmult22
    (Bmult[12] => Cmult[22]) = 16160; // Bmult12 -> Cmult22
    (Amult[12] => Cmult[23]) = 17604; // Amult12 -> Cmult23
    (Bmult[12] => Cmult[23]) = 16373; // Bmult12 -> Cmult23
    (Amult[12] => Cmult[24]) = 17476; // Amult12 -> Cmult24
    (Bmult[12] => Cmult[24]) = 16652; // Bmult12 -> Cmult24
    (Amult[12] => Cmult[25]) = 17743; // Amult12 -> Cmult25
    (Bmult[12] => Cmult[25]) = 17056; // Bmult12 -> Cmult25
    (Amult[12] => Cmult[26]) = 18433; // Amult12 -> Cmult26
    (Bmult[12] => Cmult[26]) = 17334; // Bmult12 -> Cmult26
    (Amult[12] => Cmult[27]) = 18635; // Amult12 -> Cmult27
    (Bmult[12] => Cmult[27]) = 17722; // Bmult12 -> Cmult27
    (Amult[12] => Cmult[28]) = 18893; // Amult12 -> Cmult28
    (Bmult[12] => Cmult[28]) = 18246; // Bmult12 -> Cmult28
    (Amult[12] => Cmult[29]) = 19237; // Amult12 -> Cmult29
    (Bmult[12] => Cmult[29]) = 18685; // Bmult12 -> Cmult29
    (Amult[12] => Cmult[30]) = 19915; // Amult12 -> Cmult30
    (Bmult[12] => Cmult[30]) = 19251; // Bmult12 -> Cmult30
    (Amult[12] => Cmult[31]) = 20722; // Amult12 -> Cmult31
    (Bmult[12] => Cmult[31]) = 20061; // Bmult12 -> Cmult31
    (Amult[12] => Cmult[32]) = 26095; // Amult12 -> Cmult32
    (Bmult[12] => Cmult[32]) = 24528; // Bmult12 -> Cmult32
    (Amult[12] => Cmult[33]) = 26417; // Amult12 -> Cmult33
    (Bmult[12] => Cmult[33]) = 24852; // Bmult12 -> Cmult33
    (Amult[12] => Cmult[34]) = 26691; // Amult12 -> Cmult34
    (Bmult[12] => Cmult[34]) = 25256; // Bmult12 -> Cmult34
    (Amult[12] => Cmult[35]) = 26942; // Amult12 -> Cmult35
    (Bmult[12] => Cmult[35]) = 25373; // Bmult12 -> Cmult35
    (Amult[12] => Cmult[36]) = 27112; // Amult12 -> Cmult36
    (Bmult[12] => Cmult[36]) = 25879; // Bmult12 -> Cmult36
    (Amult[12] => Cmult[37]) = 27211; // Amult12 -> Cmult37
    (Bmult[12] => Cmult[37]) = 25920; // Bmult12 -> Cmult37
    (Amult[12] => Cmult[38]) = 27590; // Amult12 -> Cmult38
    (Bmult[12] => Cmult[38]) = 26356; // Bmult12 -> Cmult38
    (Amult[12] => Cmult[39]) = 27891; // Amult12 -> Cmult39
    (Bmult[12] => Cmult[39]) = 26657; // Bmult12 -> Cmult39
    (Amult[12] => Cmult[40]) = 28095; // Amult12 -> Cmult40
    (Bmult[12] => Cmult[40]) = 26861; // Bmult12 -> Cmult40
    (Amult[12] => Cmult[41]) = 28341; // Amult12 -> Cmult41
    (Bmult[12] => Cmult[41]) = 27107; // Bmult12 -> Cmult41
    (Amult[12] => Cmult[42]) = 27773; // Amult12 -> Cmult42
    (Bmult[12] => Cmult[42]) = 26539; // Bmult12 -> Cmult42
    (Amult[12] => Cmult[43]) = 28463; // Amult12 -> Cmult43
    (Bmult[12] => Cmult[43]) = 27229; // Bmult12 -> Cmult43
    (Amult[12] => Cmult[44]) = 28921; // Amult12 -> Cmult44
    (Bmult[12] => Cmult[44]) = 27636; // Bmult12 -> Cmult44
    (Amult[12] => Cmult[45]) = 29079; // Amult12 -> Cmult45
    (Bmult[12] => Cmult[45]) = 27845; // Bmult12 -> Cmult45
    (Amult[12] => Cmult[46]) = 28469; // Amult12 -> Cmult46
    (Bmult[12] => Cmult[46]) = 27234; // Bmult12 -> Cmult46
    (Amult[12] => Cmult[47]) = 28411; // Amult12 -> Cmult47
    (Bmult[12] => Cmult[47]) = 27178; // Bmult12 -> Cmult47
    (Amult[12] => Cmult[48]) = 29390; // Amult12 -> Cmult48
    (Bmult[12] => Cmult[48]) = 28157; // Bmult12 -> Cmult48
    (Amult[12] => Cmult[49]) = 29226; // Amult12 -> Cmult49
    (Bmult[12] => Cmult[49]) = 27983; // Bmult12 -> Cmult49
    (Amult[12] => Cmult[50]) = 30000; // Amult12 -> Cmult50
    (Bmult[12] => Cmult[50]) = 28765; // Bmult12 -> Cmult50
    (Amult[12] => Cmult[51]) = 30193; // Amult12 -> Cmult51
    (Bmult[12] => Cmult[51]) = 28958; // Bmult12 -> Cmult51
    (Amult[12] => Cmult[52]) = 30846; // Amult12 -> Cmult52
    (Bmult[12] => Cmult[52]) = 29612; // Bmult12 -> Cmult52
    (Amult[12] => Cmult[53]) = 31118; // Amult12 -> Cmult53
    (Bmult[12] => Cmult[53]) = 29843; // Bmult12 -> Cmult53
    (Amult[12] => Cmult[54]) = 31503; // Amult12 -> Cmult54
    (Bmult[12] => Cmult[54]) = 30269; // Bmult12 -> Cmult54
    (Amult[12] => Cmult[55]) = 31655; // Amult12 -> Cmult55
    (Bmult[12] => Cmult[55]) = 30361; // Bmult12 -> Cmult55
    (Amult[12] => Cmult[56]) = 32184; // Amult12 -> Cmult56
    (Bmult[12] => Cmult[56]) = 30950; // Bmult12 -> Cmult56
    (Amult[12] => Cmult[57]) = 32470; // Amult12 -> Cmult57
    (Bmult[12] => Cmult[57]) = 31235; // Bmult12 -> Cmult57
    (Amult[12] => Cmult[58]) = 32928; // Amult12 -> Cmult58
    (Bmult[12] => Cmult[58]) = 31693; // Bmult12 -> Cmult58
    (Amult[12] => Cmult[59]) = 32997; // Amult12 -> Cmult59
    (Bmult[12] => Cmult[59]) = 31762; // Bmult12 -> Cmult59
    (Amult[12] => Cmult[60]) = 33559; // Amult12 -> Cmult60
    (Bmult[12] => Cmult[60]) = 32324; // Bmult12 -> Cmult60
    (Amult[12] => Cmult[61]) = 33582; // Amult12 -> Cmult61
    (Bmult[12] => Cmult[61]) = 32303; // Bmult12 -> Cmult61
    (Amult[12] => Cmult[62]) = 34355; // Amult12 -> Cmult62
    (Bmult[12] => Cmult[62]) = 33119; // Bmult12 -> Cmult62
    (Amult[12] => Cmult[63]) = 35450; // Amult12 -> Cmult63
    (Bmult[12] => Cmult[63]) = 34213; // Bmult12 -> Cmult63
    (Amult[13] => Cmult[1]) = 5408; // Amult13 -> Cmult1
    (Bmult[13] => Cmult[1]) = 5012; // Bmult13 -> Cmult1
    (Amult[13] => Cmult[2]) = 6490; // Amult13 -> Cmult2
    (Bmult[13] => Cmult[2]) = 5998; // Bmult13 -> Cmult2
    (Amult[13] => Cmult[3]) = 6767; // Amult13 -> Cmult3
    (Bmult[13] => Cmult[3]) = 6258; // Bmult13 -> Cmult3
    (Amult[13] => Cmult[4]) = 7470; // Amult13 -> Cmult4
    (Bmult[13] => Cmult[4]) = 6721; // Bmult13 -> Cmult4
    (Amult[13] => Cmult[5]) = 8398; // Amult13 -> Cmult5
    (Bmult[13] => Cmult[5]) = 7383; // Bmult13 -> Cmult5
    (Amult[13] => Cmult[6]) = 9281; // Amult13 -> Cmult6
    (Bmult[13] => Cmult[6]) = 7827; // Bmult13 -> Cmult6
    (Amult[13] => Cmult[7]) = 9472; // Amult13 -> Cmult7
    (Bmult[13] => Cmult[7]) = 8516; // Bmult13 -> Cmult7
    (Amult[13] => Cmult[8]) = 10829; // Amult13 -> Cmult8
    (Bmult[13] => Cmult[8]) = 9292; // Bmult13 -> Cmult8
    (Amult[13] => Cmult[9]) = 11136; // Amult13 -> Cmult9
    (Bmult[13] => Cmult[9]) = 9817; // Bmult13 -> Cmult9
    (Amult[13] => Cmult[10]) = 11561; // Amult13 -> Cmult10
    (Bmult[13] => Cmult[10]) = 10465; // Bmult13 -> Cmult10
    (Amult[13] => Cmult[11]) = 12105; // Amult13 -> Cmult11
    (Bmult[13] => Cmult[11]) = 10895; // Bmult13 -> Cmult11
    (Amult[13] => Cmult[12]) = 12679; // Amult13 -> Cmult12
    (Bmult[13] => Cmult[12]) = 11145; // Bmult13 -> Cmult12
    (Amult[13] => Cmult[13]) = 13520; // Amult13 -> Cmult13
    (Bmult[13] => Cmult[13]) = 12604; // Bmult13 -> Cmult13
    (Amult[13] => Cmult[14]) = 14048; // Amult13 -> Cmult14
    (Bmult[13] => Cmult[14]) = 13140; // Bmult13 -> Cmult14
    (Amult[13] => Cmult[15]) = 15613; // Amult13 -> Cmult15
    (Bmult[13] => Cmult[15]) = 14575; // Bmult13 -> Cmult15
    (Amult[13] => Cmult[16]) = 15514; // Amult13 -> Cmult16
    (Bmult[13] => Cmult[16]) = 14748; // Bmult13 -> Cmult16
    (Amult[13] => Cmult[17]) = 15705; // Amult13 -> Cmult17
    (Bmult[13] => Cmult[17]) = 15129; // Bmult13 -> Cmult17
    (Amult[13] => Cmult[18]) = 16067; // Amult13 -> Cmult18
    (Bmult[13] => Cmult[18]) = 14805; // Bmult13 -> Cmult18
    (Amult[13] => Cmult[19]) = 16393; // Amult13 -> Cmult19
    (Bmult[13] => Cmult[19]) = 15131; // Bmult13 -> Cmult19
    (Amult[13] => Cmult[20]) = 16816; // Amult13 -> Cmult20
    (Bmult[13] => Cmult[20]) = 15554; // Bmult13 -> Cmult20
    (Amult[13] => Cmult[21]) = 17136; // Amult13 -> Cmult21
    (Bmult[13] => Cmult[21]) = 15874; // Bmult13 -> Cmult21
    (Amult[13] => Cmult[22]) = 17391; // Amult13 -> Cmult22
    (Bmult[13] => Cmult[22]) = 16129; // Bmult13 -> Cmult22
    (Amult[13] => Cmult[23]) = 17604; // Amult13 -> Cmult23
    (Bmult[13] => Cmult[23]) = 16342; // Bmult13 -> Cmult23
    (Amult[13] => Cmult[24]) = 17476; // Amult13 -> Cmult24
    (Bmult[13] => Cmult[24]) = 16488; // Bmult13 -> Cmult24
    (Amult[13] => Cmult[25]) = 17743; // Amult13 -> Cmult25
    (Bmult[13] => Cmult[25]) = 16891; // Bmult13 -> Cmult25
    (Amult[13] => Cmult[26]) = 18433; // Amult13 -> Cmult26
    (Bmult[13] => Cmult[26]) = 17202; // Bmult13 -> Cmult26
    (Amult[13] => Cmult[27]) = 18635; // Amult13 -> Cmult27
    (Bmult[13] => Cmult[27]) = 17558; // Bmult13 -> Cmult27
    (Amult[13] => Cmult[28]) = 18893; // Amult13 -> Cmult28
    (Bmult[13] => Cmult[28]) = 18082; // Bmult13 -> Cmult28
    (Amult[13] => Cmult[29]) = 19237; // Amult13 -> Cmult29
    (Bmult[13] => Cmult[29]) = 18520; // Bmult13 -> Cmult29
    (Amult[13] => Cmult[30]) = 19915; // Amult13 -> Cmult30
    (Bmult[13] => Cmult[30]) = 19086; // Bmult13 -> Cmult30
    (Amult[13] => Cmult[31]) = 20722; // Amult13 -> Cmult31
    (Bmult[13] => Cmult[31]) = 19897; // Bmult13 -> Cmult31
    (Amult[13] => Cmult[32]) = 26095; // Amult13 -> Cmult32
    (Bmult[13] => Cmult[32]) = 24884; // Bmult13 -> Cmult32
    (Amult[13] => Cmult[33]) = 26417; // Amult13 -> Cmult33
    (Bmult[13] => Cmult[33]) = 25138; // Bmult13 -> Cmult33
    (Amult[13] => Cmult[34]) = 26691; // Amult13 -> Cmult34
    (Bmult[13] => Cmult[34]) = 25406; // Bmult13 -> Cmult34
    (Amult[13] => Cmult[35]) = 26942; // Amult13 -> Cmult35
    (Bmult[13] => Cmult[35]) = 25624; // Bmult13 -> Cmult35
    (Amult[13] => Cmult[36]) = 27112; // Amult13 -> Cmult36
    (Bmult[13] => Cmult[36]) = 26029; // Bmult13 -> Cmult36
    (Amult[13] => Cmult[37]) = 27211; // Amult13 -> Cmult37
    (Bmult[13] => Cmult[37]) = 26070; // Bmult13 -> Cmult37
    (Amult[13] => Cmult[38]) = 27590; // Amult13 -> Cmult38
    (Bmult[13] => Cmult[38]) = 26506; // Bmult13 -> Cmult38
    (Amult[13] => Cmult[39]) = 27891; // Amult13 -> Cmult39
    (Bmult[13] => Cmult[39]) = 26808; // Bmult13 -> Cmult39
    (Amult[13] => Cmult[40]) = 28095; // Amult13 -> Cmult40
    (Bmult[13] => Cmult[40]) = 27012; // Bmult13 -> Cmult40
    (Amult[13] => Cmult[41]) = 28341; // Amult13 -> Cmult41
    (Bmult[13] => Cmult[41]) = 27258; // Bmult13 -> Cmult41
    (Amult[13] => Cmult[42]) = 27773; // Amult13 -> Cmult42
    (Bmult[13] => Cmult[42]) = 26690; // Bmult13 -> Cmult42
    (Amult[13] => Cmult[43]) = 28463; // Amult13 -> Cmult43
    (Bmult[13] => Cmult[43]) = 27380; // Bmult13 -> Cmult43
    (Amult[13] => Cmult[44]) = 28921; // Amult13 -> Cmult44
    (Bmult[13] => Cmult[44]) = 27786; // Bmult13 -> Cmult44
    (Amult[13] => Cmult[45]) = 29079; // Amult13 -> Cmult45
    (Bmult[13] => Cmult[45]) = 27996; // Bmult13 -> Cmult45
    (Amult[13] => Cmult[46]) = 28469; // Amult13 -> Cmult46
    (Bmult[13] => Cmult[46]) = 27386; // Bmult13 -> Cmult46
    (Amult[13] => Cmult[47]) = 28411; // Amult13 -> Cmult47
    (Bmult[13] => Cmult[47]) = 27328; // Bmult13 -> Cmult47
    (Amult[13] => Cmult[48]) = 29390; // Amult13 -> Cmult48
    (Bmult[13] => Cmult[48]) = 28307; // Bmult13 -> Cmult48
    (Amult[13] => Cmult[49]) = 29226; // Amult13 -> Cmult49
    (Bmult[13] => Cmult[49]) = 28134; // Bmult13 -> Cmult49
    (Amult[13] => Cmult[50]) = 30000; // Amult13 -> Cmult50
    (Bmult[13] => Cmult[50]) = 28917; // Bmult13 -> Cmult50
    (Amult[13] => Cmult[51]) = 30193; // Amult13 -> Cmult51
    (Bmult[13] => Cmult[51]) = 29109; // Bmult13 -> Cmult51
    (Amult[13] => Cmult[52]) = 30846; // Amult13 -> Cmult52
    (Bmult[13] => Cmult[52]) = 29763; // Bmult13 -> Cmult52
    (Amult[13] => Cmult[53]) = 31118; // Amult13 -> Cmult53
    (Bmult[13] => Cmult[53]) = 29995; // Bmult13 -> Cmult53
    (Amult[13] => Cmult[54]) = 31503; // Amult13 -> Cmult54
    (Bmult[13] => Cmult[54]) = 30420; // Bmult13 -> Cmult54
    (Amult[13] => Cmult[55]) = 31655; // Amult13 -> Cmult55
    (Bmult[13] => Cmult[55]) = 30512; // Bmult13 -> Cmult55
    (Amult[13] => Cmult[56]) = 32184; // Amult13 -> Cmult56
    (Bmult[13] => Cmult[56]) = 31101; // Bmult13 -> Cmult56
    (Amult[13] => Cmult[57]) = 32470; // Amult13 -> Cmult57
    (Bmult[13] => Cmult[57]) = 31386; // Bmult13 -> Cmult57
    (Amult[13] => Cmult[58]) = 32928; // Amult13 -> Cmult58
    (Bmult[13] => Cmult[58]) = 31845; // Bmult13 -> Cmult58
    (Amult[13] => Cmult[59]) = 32997; // Amult13 -> Cmult59
    (Bmult[13] => Cmult[59]) = 31913; // Bmult13 -> Cmult59
    (Amult[13] => Cmult[60]) = 33559; // Amult13 -> Cmult60
    (Bmult[13] => Cmult[60]) = 32475; // Bmult13 -> Cmult60
    (Amult[13] => Cmult[61]) = 33582; // Amult13 -> Cmult61
    (Bmult[13] => Cmult[61]) = 32455; // Bmult13 -> Cmult61
    (Amult[13] => Cmult[62]) = 34355; // Amult13 -> Cmult62
    (Bmult[13] => Cmult[62]) = 33270; // Bmult13 -> Cmult62
    (Amult[13] => Cmult[63]) = 35450; // Amult13 -> Cmult63
    (Bmult[13] => Cmult[63]) = 34364; // Bmult13 -> Cmult63
    (Amult[14] => Cmult[1]) = 5408; // Amult14 -> Cmult1
    (Bmult[14] => Cmult[1]) = 5012; // Bmult14 -> Cmult1
    (Amult[14] => Cmult[2]) = 6490; // Amult14 -> Cmult2
    (Bmult[14] => Cmult[2]) = 5998; // Bmult14 -> Cmult2
    (Amult[14] => Cmult[3]) = 6767; // Amult14 -> Cmult3
    (Bmult[14] => Cmult[3]) = 6258; // Bmult14 -> Cmult3
    (Amult[14] => Cmult[4]) = 7470; // Amult14 -> Cmult4
    (Bmult[14] => Cmult[4]) = 6721; // Bmult14 -> Cmult4
    (Amult[14] => Cmult[5]) = 8398; // Amult14 -> Cmult5
    (Bmult[14] => Cmult[5]) = 7383; // Bmult14 -> Cmult5
    (Amult[14] => Cmult[6]) = 9281; // Amult14 -> Cmult6
    (Bmult[14] => Cmult[6]) = 7827; // Bmult14 -> Cmult6
    (Amult[14] => Cmult[7]) = 9472; // Amult14 -> Cmult7
    (Bmult[14] => Cmult[7]) = 8516; // Bmult14 -> Cmult7
    (Amult[14] => Cmult[8]) = 10829; // Amult14 -> Cmult8
    (Bmult[14] => Cmult[8]) = 9292; // Bmult14 -> Cmult8
    (Amult[14] => Cmult[9]) = 11136; // Amult14 -> Cmult9
    (Bmult[14] => Cmult[9]) = 9817; // Bmult14 -> Cmult9
    (Amult[14] => Cmult[10]) = 11561; // Amult14 -> Cmult10
    (Bmult[14] => Cmult[10]) = 10465; // Bmult14 -> Cmult10
    (Amult[14] => Cmult[11]) = 12105; // Amult14 -> Cmult11
    (Bmult[14] => Cmult[11]) = 10895; // Bmult14 -> Cmult11
    (Amult[14] => Cmult[12]) = 12679; // Amult14 -> Cmult12
    (Bmult[14] => Cmult[12]) = 11145; // Bmult14 -> Cmult12
    (Amult[14] => Cmult[13]) = 13520; // Amult14 -> Cmult13
    (Bmult[14] => Cmult[13]) = 11832; // Bmult14 -> Cmult13
    (Amult[14] => Cmult[14]) = 14048; // Amult14 -> Cmult14
    (Bmult[14] => Cmult[14]) = 13248; // Bmult14 -> Cmult14
    (Amult[14] => Cmult[15]) = 15613; // Amult14 -> Cmult15
    (Bmult[14] => Cmult[15]) = 14718; // Bmult14 -> Cmult15
    (Amult[14] => Cmult[16]) = 15514; // Amult14 -> Cmult16
    (Bmult[14] => Cmult[16]) = 14891; // Bmult14 -> Cmult16
    (Amult[14] => Cmult[17]) = 15705; // Amult14 -> Cmult17
    (Bmult[14] => Cmult[17]) = 15272; // Bmult14 -> Cmult17
    (Amult[14] => Cmult[18]) = 16067; // Amult14 -> Cmult18
    (Bmult[14] => Cmult[18]) = 14880; // Bmult14 -> Cmult18
    (Amult[14] => Cmult[19]) = 16393; // Amult14 -> Cmult19
    (Bmult[14] => Cmult[19]) = 15129; // Bmult14 -> Cmult19
    (Amult[14] => Cmult[20]) = 16816; // Amult14 -> Cmult20
    (Bmult[14] => Cmult[20]) = 15553; // Bmult14 -> Cmult20
    (Amult[14] => Cmult[21]) = 17136; // Amult14 -> Cmult21
    (Bmult[14] => Cmult[21]) = 15872; // Bmult14 -> Cmult21
    (Amult[14] => Cmult[22]) = 17391; // Amult14 -> Cmult22
    (Bmult[14] => Cmult[22]) = 16128; // Bmult14 -> Cmult22
    (Amult[14] => Cmult[23]) = 17604; // Amult14 -> Cmult23
    (Bmult[14] => Cmult[23]) = 16340; // Bmult14 -> Cmult23
    (Amult[14] => Cmult[24]) = 17476; // Amult14 -> Cmult24
    (Bmult[14] => Cmult[24]) = 16712; // Bmult14 -> Cmult24
    (Amult[14] => Cmult[25]) = 17743; // Amult14 -> Cmult25
    (Bmult[14] => Cmult[25]) = 17115; // Bmult14 -> Cmult25
    (Amult[14] => Cmult[26]) = 18433; // Amult14 -> Cmult26
    (Bmult[14] => Cmult[26]) = 17393; // Bmult14 -> Cmult26
    (Amult[14] => Cmult[27]) = 18635; // Amult14 -> Cmult27
    (Bmult[14] => Cmult[27]) = 17782; // Bmult14 -> Cmult27
    (Amult[14] => Cmult[28]) = 18893; // Amult14 -> Cmult28
    (Bmult[14] => Cmult[28]) = 18306; // Bmult14 -> Cmult28
    (Amult[14] => Cmult[29]) = 19237; // Amult14 -> Cmult29
    (Bmult[14] => Cmult[29]) = 18744; // Bmult14 -> Cmult29
    (Amult[14] => Cmult[30]) = 19915; // Amult14 -> Cmult30
    (Bmult[14] => Cmult[30]) = 19310; // Bmult14 -> Cmult30
    (Amult[14] => Cmult[31]) = 20722; // Amult14 -> Cmult31
    (Bmult[14] => Cmult[31]) = 20121; // Bmult14 -> Cmult31
    (Amult[14] => Cmult[32]) = 26095; // Amult14 -> Cmult32
    (Bmult[14] => Cmult[32]) = 24907; // Bmult14 -> Cmult32
    (Amult[14] => Cmult[33]) = 26417; // Amult14 -> Cmult33
    (Bmult[14] => Cmult[33]) = 25189; // Bmult14 -> Cmult33
    (Amult[14] => Cmult[34]) = 26691; // Amult14 -> Cmult34
    (Bmult[14] => Cmult[34]) = 25635; // Bmult14 -> Cmult34
    (Amult[14] => Cmult[35]) = 26942; // Amult14 -> Cmult35
    (Bmult[14] => Cmult[35]) = 25751; // Bmult14 -> Cmult35
    (Amult[14] => Cmult[36]) = 27112; // Amult14 -> Cmult36
    (Bmult[14] => Cmult[36]) = 26258; // Bmult14 -> Cmult36
    (Amult[14] => Cmult[37]) = 27211; // Amult14 -> Cmult37
    (Bmult[14] => Cmult[37]) = 26299; // Bmult14 -> Cmult37
    (Amult[14] => Cmult[38]) = 27590; // Amult14 -> Cmult38
    (Bmult[14] => Cmult[38]) = 26735; // Bmult14 -> Cmult38
    (Amult[14] => Cmult[39]) = 27891; // Amult14 -> Cmult39
    (Bmult[14] => Cmult[39]) = 27036; // Bmult14 -> Cmult39
    (Amult[14] => Cmult[40]) = 28095; // Amult14 -> Cmult40
    (Bmult[14] => Cmult[40]) = 27241; // Bmult14 -> Cmult40
    (Amult[14] => Cmult[41]) = 28341; // Amult14 -> Cmult41
    (Bmult[14] => Cmult[41]) = 27486; // Bmult14 -> Cmult41
    (Amult[14] => Cmult[42]) = 27773; // Amult14 -> Cmult42
    (Bmult[14] => Cmult[42]) = 26918; // Bmult14 -> Cmult42
    (Amult[14] => Cmult[43]) = 28463; // Amult14 -> Cmult43
    (Bmult[14] => Cmult[43]) = 27609; // Bmult14 -> Cmult43
    (Amult[14] => Cmult[44]) = 28921; // Amult14 -> Cmult44
    (Bmult[14] => Cmult[44]) = 28015; // Bmult14 -> Cmult44
    (Amult[14] => Cmult[45]) = 29079; // Amult14 -> Cmult45
    (Bmult[14] => Cmult[45]) = 28224; // Bmult14 -> Cmult45
    (Amult[14] => Cmult[46]) = 28469; // Amult14 -> Cmult46
    (Bmult[14] => Cmult[46]) = 27614; // Bmult14 -> Cmult46
    (Amult[14] => Cmult[47]) = 28411; // Amult14 -> Cmult47
    (Bmult[14] => Cmult[47]) = 27557; // Bmult14 -> Cmult47
    (Amult[14] => Cmult[48]) = 29390; // Amult14 -> Cmult48
    (Bmult[14] => Cmult[48]) = 28536; // Bmult14 -> Cmult48
    (Amult[14] => Cmult[49]) = 29226; // Amult14 -> Cmult49
    (Bmult[14] => Cmult[49]) = 28363; // Bmult14 -> Cmult49
    (Amult[14] => Cmult[50]) = 30000; // Amult14 -> Cmult50
    (Bmult[14] => Cmult[50]) = 29145; // Bmult14 -> Cmult50
    (Amult[14] => Cmult[51]) = 30193; // Amult14 -> Cmult51
    (Bmult[14] => Cmult[51]) = 29338; // Bmult14 -> Cmult51
    (Amult[14] => Cmult[52]) = 30846; // Amult14 -> Cmult52
    (Bmult[14] => Cmult[52]) = 29992; // Bmult14 -> Cmult52
    (Amult[14] => Cmult[53]) = 31118; // Amult14 -> Cmult53
    (Bmult[14] => Cmult[53]) = 30223; // Bmult14 -> Cmult53
    (Amult[14] => Cmult[54]) = 31503; // Amult14 -> Cmult54
    (Bmult[14] => Cmult[54]) = 30649; // Bmult14 -> Cmult54
    (Amult[14] => Cmult[55]) = 31655; // Amult14 -> Cmult55
    (Bmult[14] => Cmult[55]) = 30741; // Bmult14 -> Cmult55
    (Amult[14] => Cmult[56]) = 32184; // Amult14 -> Cmult56
    (Bmult[14] => Cmult[56]) = 31330; // Bmult14 -> Cmult56
    (Amult[14] => Cmult[57]) = 32470; // Amult14 -> Cmult57
    (Bmult[14] => Cmult[57]) = 31615; // Bmult14 -> Cmult57
    (Amult[14] => Cmult[58]) = 32928; // Amult14 -> Cmult58
    (Bmult[14] => Cmult[58]) = 32073; // Bmult14 -> Cmult58
    (Amult[14] => Cmult[59]) = 32997; // Amult14 -> Cmult59
    (Bmult[14] => Cmult[59]) = 32142; // Bmult14 -> Cmult59
    (Amult[14] => Cmult[60]) = 33559; // Amult14 -> Cmult60
    (Bmult[14] => Cmult[60]) = 32704; // Bmult14 -> Cmult60
    (Amult[14] => Cmult[61]) = 33582; // Amult14 -> Cmult61
    (Bmult[14] => Cmult[61]) = 32684; // Bmult14 -> Cmult61
    (Amult[14] => Cmult[62]) = 34355; // Amult14 -> Cmult62
    (Bmult[14] => Cmult[62]) = 33499; // Bmult14 -> Cmult62
    (Amult[14] => Cmult[63]) = 35450; // Amult14 -> Cmult63
    (Bmult[14] => Cmult[63]) = 34593; // Bmult14 -> Cmult63
    (Amult[15] => Cmult[1]) = 5408; // Amult15 -> Cmult1
    (Bmult[15] => Cmult[1]) = 5012; // Bmult15 -> Cmult1
    (Amult[15] => Cmult[2]) = 6490; // Amult15 -> Cmult2
    (Bmult[15] => Cmult[2]) = 5998; // Bmult15 -> Cmult2
    (Amult[15] => Cmult[3]) = 6767; // Amult15 -> Cmult3
    (Bmult[15] => Cmult[3]) = 6258; // Bmult15 -> Cmult3
    (Amult[15] => Cmult[4]) = 7470; // Amult15 -> Cmult4
    (Bmult[15] => Cmult[4]) = 6721; // Bmult15 -> Cmult4
    (Amult[15] => Cmult[5]) = 8398; // Amult15 -> Cmult5
    (Bmult[15] => Cmult[5]) = 7383; // Bmult15 -> Cmult5
    (Amult[15] => Cmult[6]) = 9281; // Amult15 -> Cmult6
    (Bmult[15] => Cmult[6]) = 7827; // Bmult15 -> Cmult6
    (Amult[15] => Cmult[7]) = 9472; // Amult15 -> Cmult7
    (Bmult[15] => Cmult[7]) = 8516; // Bmult15 -> Cmult7
    (Amult[15] => Cmult[8]) = 10829; // Amult15 -> Cmult8
    (Bmult[15] => Cmult[8]) = 9292; // Bmult15 -> Cmult8
    (Amult[15] => Cmult[9]) = 11136; // Amult15 -> Cmult9
    (Bmult[15] => Cmult[9]) = 9817; // Bmult15 -> Cmult9
    (Amult[15] => Cmult[10]) = 11561; // Amult15 -> Cmult10
    (Bmult[15] => Cmult[10]) = 10465; // Bmult15 -> Cmult10
    (Amult[15] => Cmult[11]) = 12105; // Amult15 -> Cmult11
    (Bmult[15] => Cmult[11]) = 10895; // Bmult15 -> Cmult11
    (Amult[15] => Cmult[12]) = 12679; // Amult15 -> Cmult12
    (Bmult[15] => Cmult[12]) = 11145; // Bmult15 -> Cmult12
    (Amult[15] => Cmult[13]) = 13520; // Amult15 -> Cmult13
    (Bmult[15] => Cmult[13]) = 11832; // Bmult15 -> Cmult13
    (Amult[15] => Cmult[14]) = 14048; // Amult15 -> Cmult14
    (Bmult[15] => Cmult[14]) = 12260; // Bmult15 -> Cmult14
    (Amult[15] => Cmult[15]) = 15613; // Amult15 -> Cmult15
    (Bmult[15] => Cmult[15]) = 14645; // Bmult15 -> Cmult15
    (Amult[15] => Cmult[16]) = 15514; // Amult15 -> Cmult16
    (Bmult[15] => Cmult[16]) = 14819; // Bmult15 -> Cmult16
    (Amult[15] => Cmult[17]) = 15705; // Amult15 -> Cmult17
    (Bmult[15] => Cmult[17]) = 15200; // Bmult15 -> Cmult17
    (Amult[15] => Cmult[18]) = 16067; // Amult15 -> Cmult18
    (Bmult[15] => Cmult[18]) = 14952; // Bmult15 -> Cmult18
    (Amult[15] => Cmult[19]) = 16393; // Amult15 -> Cmult19
    (Bmult[15] => Cmult[19]) = 15278; // Bmult15 -> Cmult19
    (Amult[15] => Cmult[20]) = 16816; // Amult15 -> Cmult20
    (Bmult[15] => Cmult[20]) = 15702; // Bmult15 -> Cmult20
    (Amult[15] => Cmult[21]) = 17136; // Amult15 -> Cmult21
    (Bmult[15] => Cmult[21]) = 16021; // Bmult15 -> Cmult21
    (Amult[15] => Cmult[22]) = 17391; // Amult15 -> Cmult22
    (Bmult[15] => Cmult[22]) = 16286; // Bmult15 -> Cmult22
    (Amult[15] => Cmult[23]) = 17604; // Amult15 -> Cmult23
    (Bmult[15] => Cmult[23]) = 16489; // Bmult15 -> Cmult23
    (Amult[15] => Cmult[24]) = 17476; // Amult15 -> Cmult24
    (Bmult[15] => Cmult[24]) = 16679; // Bmult15 -> Cmult24
    (Amult[15] => Cmult[25]) = 17743; // Amult15 -> Cmult25
    (Bmult[15] => Cmult[25]) = 17083; // Bmult15 -> Cmult25
    (Amult[15] => Cmult[26]) = 18433; // Amult15 -> Cmult26
    (Bmult[15] => Cmult[26]) = 17361; // Bmult15 -> Cmult26
    (Amult[15] => Cmult[27]) = 18635; // Amult15 -> Cmult27
    (Bmult[15] => Cmult[27]) = 17750; // Bmult15 -> Cmult27
    (Amult[15] => Cmult[28]) = 18893; // Amult15 -> Cmult28
    (Bmult[15] => Cmult[28]) = 18274; // Bmult15 -> Cmult28
    (Amult[15] => Cmult[29]) = 19237; // Amult15 -> Cmult29
    (Bmult[15] => Cmult[29]) = 18712; // Bmult15 -> Cmult29
    (Amult[15] => Cmult[30]) = 19915; // Amult15 -> Cmult30
    (Bmult[15] => Cmult[30]) = 19278; // Bmult15 -> Cmult30
    (Amult[15] => Cmult[31]) = 20722; // Amult15 -> Cmult31
    (Bmult[15] => Cmult[31]) = 20089; // Bmult15 -> Cmult31
    (Amult[15] => Cmult[32]) = 26095; // Amult15 -> Cmult32
    (Bmult[15] => Cmult[32]) = 25395; // Bmult15 -> Cmult32
    (Amult[15] => Cmult[33]) = 26417; // Amult15 -> Cmult33
    (Bmult[15] => Cmult[33]) = 25732; // Bmult15 -> Cmult33
    (Amult[15] => Cmult[34]) = 26691; // Amult15 -> Cmult34
    (Bmult[15] => Cmult[34]) = 26007; // Bmult15 -> Cmult34
    (Amult[15] => Cmult[35]) = 26942; // Amult15 -> Cmult35
    (Bmult[15] => Cmult[35]) = 26257; // Bmult15 -> Cmult35
    (Amult[15] => Cmult[36]) = 27112; // Amult15 -> Cmult36
    (Bmult[15] => Cmult[36]) = 26323; // Bmult15 -> Cmult36
    (Amult[15] => Cmult[37]) = 27211; // Amult15 -> Cmult37
    (Bmult[15] => Cmult[37]) = 26516; // Bmult15 -> Cmult37
    (Amult[15] => Cmult[38]) = 27590; // Amult15 -> Cmult38
    (Bmult[15] => Cmult[38]) = 26391; // Bmult15 -> Cmult38
    (Amult[15] => Cmult[39]) = 27891; // Amult15 -> Cmult39
    (Bmult[15] => Cmult[39]) = 26669; // Bmult15 -> Cmult39
    (Amult[15] => Cmult[40]) = 28095; // Amult15 -> Cmult40
    (Bmult[15] => Cmult[40]) = 27187; // Bmult15 -> Cmult40
    (Amult[15] => Cmult[41]) = 28341; // Amult15 -> Cmult41
    (Bmult[15] => Cmult[41]) = 27119; // Bmult15 -> Cmult41
    (Amult[15] => Cmult[42]) = 27773; // Amult15 -> Cmult42
    (Bmult[15] => Cmult[42]) = 26673; // Bmult15 -> Cmult42
    (Amult[15] => Cmult[43]) = 28463; // Amult15 -> Cmult43
    (Bmult[15] => Cmult[43]) = 27241; // Bmult15 -> Cmult43
    (Amult[15] => Cmult[44]) = 28921; // Amult15 -> Cmult44
    (Bmult[15] => Cmult[44]) = 27837; // Bmult15 -> Cmult44
    (Amult[15] => Cmult[45]) = 29079; // Amult15 -> Cmult45
    (Bmult[15] => Cmult[45]) = 27857; // Bmult15 -> Cmult45
    (Amult[15] => Cmult[46]) = 28469; // Amult15 -> Cmult46
    (Bmult[15] => Cmult[46]) = 27320; // Bmult15 -> Cmult46
    (Amult[15] => Cmult[47]) = 28411; // Amult15 -> Cmult47
    (Bmult[15] => Cmult[47]) = 27189; // Bmult15 -> Cmult47
    (Amult[15] => Cmult[48]) = 29390; // Amult15 -> Cmult48
    (Bmult[15] => Cmult[48]) = 28200; // Bmult15 -> Cmult48
    (Amult[15] => Cmult[49]) = 29226; // Amult15 -> Cmult49
    (Bmult[15] => Cmult[49]) = 28004; // Bmult15 -> Cmult49
    (Amult[15] => Cmult[50]) = 30000; // Amult15 -> Cmult50
    (Bmult[15] => Cmult[50]) = 28850; // Bmult15 -> Cmult50
    (Amult[15] => Cmult[51]) = 30193; // Amult15 -> Cmult51
    (Bmult[15] => Cmult[51]) = 29082; // Bmult15 -> Cmult51
    (Amult[15] => Cmult[52]) = 30846; // Amult15 -> Cmult52
    (Bmult[15] => Cmult[52]) = 29882; // Bmult15 -> Cmult52
    (Amult[15] => Cmult[53]) = 31118; // Amult15 -> Cmult53
    (Bmult[15] => Cmult[53]) = 30054; // Bmult15 -> Cmult53
    (Amult[15] => Cmult[54]) = 31503; // Amult15 -> Cmult54
    (Bmult[15] => Cmult[54]) = 30519; // Bmult15 -> Cmult54
    (Amult[15] => Cmult[55]) = 31655; // Amult15 -> Cmult55
    (Bmult[15] => Cmult[55]) = 30611; // Bmult15 -> Cmult55
    (Amult[15] => Cmult[56]) = 32184; // Amult15 -> Cmult56
    (Bmult[15] => Cmult[56]) = 31257; // Bmult15 -> Cmult56
    (Amult[15] => Cmult[57]) = 32470; // Amult15 -> Cmult57
    (Bmult[15] => Cmult[57]) = 31348; // Bmult15 -> Cmult57
    (Amult[15] => Cmult[58]) = 32928; // Amult15 -> Cmult58
    (Bmult[15] => Cmult[58]) = 31722; // Bmult15 -> Cmult58
    (Amult[15] => Cmult[59]) = 32997; // Amult15 -> Cmult59
    (Bmult[15] => Cmult[59]) = 31872; // Bmult15 -> Cmult59
    (Amult[15] => Cmult[60]) = 33559; // Amult15 -> Cmult60
    (Bmult[15] => Cmult[60]) = 32337; // Bmult15 -> Cmult60
    (Amult[15] => Cmult[61]) = 33582; // Amult15 -> Cmult61
    (Bmult[15] => Cmult[61]) = 32498; // Bmult15 -> Cmult61
    (Amult[15] => Cmult[62]) = 34355; // Amult15 -> Cmult62
    (Bmult[15] => Cmult[62]) = 33131; // Bmult15 -> Cmult62
    (Amult[15] => Cmult[63]) = 35450; // Amult15 -> Cmult63
    (Bmult[15] => Cmult[63]) = 34225; // Bmult15 -> Cmult63
    (Amult[16] => Cmult[1]) = 5408; // Amult16 -> Cmult1
    (Bmult[16] => Cmult[1]) = 5012; // Bmult16 -> Cmult1
    (Amult[16] => Cmult[2]) = 6490; // Amult16 -> Cmult2
    (Bmult[16] => Cmult[2]) = 5998; // Bmult16 -> Cmult2
    (Amult[16] => Cmult[3]) = 6767; // Amult16 -> Cmult3
    (Bmult[16] => Cmult[3]) = 6258; // Bmult16 -> Cmult3
    (Amult[16] => Cmult[4]) = 7470; // Amult16 -> Cmult4
    (Bmult[16] => Cmult[4]) = 6721; // Bmult16 -> Cmult4
    (Amult[16] => Cmult[5]) = 8398; // Amult16 -> Cmult5
    (Bmult[16] => Cmult[5]) = 7383; // Bmult16 -> Cmult5
    (Amult[16] => Cmult[6]) = 9281; // Amult16 -> Cmult6
    (Bmult[16] => Cmult[6]) = 7827; // Bmult16 -> Cmult6
    (Amult[16] => Cmult[7]) = 9472; // Amult16 -> Cmult7
    (Bmult[16] => Cmult[7]) = 8516; // Bmult16 -> Cmult7
    (Amult[16] => Cmult[8]) = 10829; // Amult16 -> Cmult8
    (Bmult[16] => Cmult[8]) = 9292; // Bmult16 -> Cmult8
    (Amult[16] => Cmult[9]) = 11136; // Amult16 -> Cmult9
    (Bmult[16] => Cmult[9]) = 9817; // Bmult16 -> Cmult9
    (Amult[16] => Cmult[10]) = 11561; // Amult16 -> Cmult10
    (Bmult[16] => Cmult[10]) = 10465; // Bmult16 -> Cmult10
    (Amult[16] => Cmult[11]) = 12105; // Amult16 -> Cmult11
    (Bmult[16] => Cmult[11]) = 10895; // Bmult16 -> Cmult11
    (Amult[16] => Cmult[12]) = 12679; // Amult16 -> Cmult12
    (Bmult[16] => Cmult[12]) = 11145; // Bmult16 -> Cmult12
    (Amult[16] => Cmult[13]) = 13520; // Amult16 -> Cmult13
    (Bmult[16] => Cmult[13]) = 11832; // Bmult16 -> Cmult13
    (Amult[16] => Cmult[14]) = 14048; // Amult16 -> Cmult14
    (Bmult[16] => Cmult[14]) = 12260; // Bmult16 -> Cmult14
    (Amult[16] => Cmult[15]) = 15613; // Amult16 -> Cmult15
    (Bmult[16] => Cmult[15]) = 13605; // Bmult16 -> Cmult15
    (Amult[16] => Cmult[16]) = 15514; // Amult16 -> Cmult16
    (Bmult[16] => Cmult[16]) = 15246; // Bmult16 -> Cmult16
    (Amult[16] => Cmult[17]) = 15705; // Amult16 -> Cmult17
    (Bmult[16] => Cmult[17]) = 15987; // Bmult16 -> Cmult17
    (Amult[16] => Cmult[18]) = 16067; // Amult16 -> Cmult18
    (Bmult[16] => Cmult[18]) = 16011; // Bmult16 -> Cmult18
    (Amult[16] => Cmult[19]) = 16393; // Amult16 -> Cmult19
    (Bmult[16] => Cmult[19]) = 16662; // Bmult16 -> Cmult19
    (Amult[16] => Cmult[20]) = 16816; // Amult16 -> Cmult20
    (Bmult[16] => Cmult[20]) = 17379; // Bmult16 -> Cmult20
    (Amult[16] => Cmult[21]) = 17136; // Amult16 -> Cmult21
    (Bmult[16] => Cmult[21]) = 18022; // Bmult16 -> Cmult21
    (Amult[16] => Cmult[22]) = 17391; // Amult16 -> Cmult22
    (Bmult[16] => Cmult[22]) = 18579; // Bmult16 -> Cmult22
    (Amult[16] => Cmult[23]) = 17604; // Amult16 -> Cmult23
    (Bmult[16] => Cmult[23]) = 19247; // Bmult16 -> Cmult23
    (Amult[16] => Cmult[24]) = 17476; // Amult16 -> Cmult24
    (Bmult[16] => Cmult[24]) = 19747; // Bmult16 -> Cmult24
    (Amult[16] => Cmult[25]) = 17743; // Amult16 -> Cmult25
    (Bmult[16] => Cmult[25]) = 20289; // Bmult16 -> Cmult25
    (Amult[16] => Cmult[26]) = 18433; // Amult16 -> Cmult26
    (Bmult[16] => Cmult[26]) = 21129; // Bmult16 -> Cmult26
    (Amult[16] => Cmult[27]) = 18635; // Amult16 -> Cmult27
    (Bmult[16] => Cmult[27]) = 21703; // Bmult16 -> Cmult27
    (Amult[16] => Cmult[28]) = 18893; // Amult16 -> Cmult28
    (Bmult[16] => Cmult[28]) = 22292; // Bmult16 -> Cmult28
    (Amult[16] => Cmult[29]) = 19237; // Amult16 -> Cmult29
    (Bmult[16] => Cmult[29]) = 23011; // Bmult16 -> Cmult29
    (Amult[16] => Cmult[30]) = 19915; // Amult16 -> Cmult30
    (Bmult[16] => Cmult[30]) = 23475; // Bmult16 -> Cmult30
    (Amult[16] => Cmult[31]) = 20722; // Amult16 -> Cmult31
    (Bmult[16] => Cmult[31]) = 25028; // Bmult16 -> Cmult31
    (Amult[16] => Cmult[32]) = 26095; // Amult16 -> Cmult32
    (Bmult[16] => Cmult[32]) = 23108; // Bmult16 -> Cmult32
    (Amult[16] => Cmult[33]) = 26417; // Amult16 -> Cmult33
    (Bmult[16] => Cmult[33]) = 23361; // Bmult16 -> Cmult33
    (Amult[16] => Cmult[34]) = 26691; // Amult16 -> Cmult34
    (Bmult[16] => Cmult[34]) = 23626; // Bmult16 -> Cmult34
    (Amult[16] => Cmult[35]) = 26942; // Amult16 -> Cmult35
    (Bmult[16] => Cmult[35]) = 23778; // Bmult16 -> Cmult35
    (Amult[16] => Cmult[36]) = 27112; // Amult16 -> Cmult36
    (Bmult[16] => Cmult[36]) = 24040; // Bmult16 -> Cmult36
    (Amult[16] => Cmult[37]) = 27211; // Amult16 -> Cmult37
    (Bmult[16] => Cmult[37]) = 24187; // Bmult16 -> Cmult37
    (Amult[16] => Cmult[38]) = 27590; // Amult16 -> Cmult38
    (Bmult[16] => Cmult[38]) = 24565; // Bmult16 -> Cmult38
    (Amult[16] => Cmult[39]) = 27891; // Amult16 -> Cmult39
    (Bmult[16] => Cmult[39]) = 24817; // Bmult16 -> Cmult39
    (Amult[16] => Cmult[40]) = 28095; // Amult16 -> Cmult40
    (Bmult[16] => Cmult[40]) = 25096; // Bmult16 -> Cmult40
    (Amult[16] => Cmult[41]) = 28341; // Amult16 -> Cmult41
    (Bmult[16] => Cmult[41]) = 25261; // Bmult16 -> Cmult41
    (Amult[16] => Cmult[42]) = 27773; // Amult16 -> Cmult42
    (Bmult[16] => Cmult[42]) = 24783; // Bmult16 -> Cmult42
    (Amult[16] => Cmult[43]) = 28463; // Amult16 -> Cmult43
    (Bmult[16] => Cmult[43]) = 25472; // Bmult16 -> Cmult43
    (Amult[16] => Cmult[44]) = 28921; // Amult16 -> Cmult44
    (Bmult[16] => Cmult[44]) = 25989; // Bmult16 -> Cmult44
    (Amult[16] => Cmult[45]) = 29079; // Amult16 -> Cmult45
    (Bmult[16] => Cmult[45]) = 26088; // Bmult16 -> Cmult45
    (Amult[16] => Cmult[46]) = 28469; // Amult16 -> Cmult46
    (Bmult[16] => Cmult[46]) = 25478; // Bmult16 -> Cmult46
    (Amult[16] => Cmult[47]) = 28411; // Amult16 -> Cmult47
    (Bmult[16] => Cmult[47]) = 25325; // Bmult16 -> Cmult47
    (Amult[16] => Cmult[48]) = 29390; // Amult16 -> Cmult48
    (Bmult[16] => Cmult[48]) = 26400; // Bmult16 -> Cmult48
    (Amult[16] => Cmult[49]) = 29226; // Amult16 -> Cmult49
    (Bmult[16] => Cmult[49]) = 26146; // Bmult16 -> Cmult49
    (Amult[16] => Cmult[50]) = 30000; // Amult16 -> Cmult50
    (Bmult[16] => Cmult[50]) = 27022; // Bmult16 -> Cmult50
    (Amult[16] => Cmult[51]) = 30193; // Amult16 -> Cmult51
    (Bmult[16] => Cmult[51]) = 27247; // Bmult16 -> Cmult51
    (Amult[16] => Cmult[52]) = 30846; // Amult16 -> Cmult52
    (Bmult[16] => Cmult[52]) = 27868; // Bmult16 -> Cmult52
    (Amult[16] => Cmult[53]) = 31118; // Amult16 -> Cmult53
    (Bmult[16] => Cmult[53]) = 28199; // Bmult16 -> Cmult53
    (Amult[16] => Cmult[54]) = 31503; // Amult16 -> Cmult54
    (Bmult[16] => Cmult[54]) = 28525; // Bmult16 -> Cmult54
    (Amult[16] => Cmult[55]) = 31655; // Amult16 -> Cmult55
    (Bmult[16] => Cmult[55]) = 28736; // Bmult16 -> Cmult55
    (Amult[16] => Cmult[56]) = 32184; // Amult16 -> Cmult56
    (Bmult[16] => Cmult[56]) = 29206; // Bmult16 -> Cmult56
    (Amult[16] => Cmult[57]) = 32470; // Amult16 -> Cmult57
    (Bmult[16] => Cmult[57]) = 29491; // Bmult16 -> Cmult57
    (Amult[16] => Cmult[58]) = 32928; // Amult16 -> Cmult58
    (Bmult[16] => Cmult[58]) = 29949; // Bmult16 -> Cmult58
    (Amult[16] => Cmult[59]) = 32997; // Amult16 -> Cmult59
    (Bmult[16] => Cmult[59]) = 30018; // Bmult16 -> Cmult59
    (Amult[16] => Cmult[60]) = 33559; // Amult16 -> Cmult60
    (Bmult[16] => Cmult[60]) = 30580; // Bmult16 -> Cmult60
    (Amult[16] => Cmult[61]) = 33582; // Amult16 -> Cmult61
    (Bmult[16] => Cmult[61]) = 30663; // Bmult16 -> Cmult61
    (Amult[16] => Cmult[62]) = 34355; // Amult16 -> Cmult62
    (Bmult[16] => Cmult[62]) = 31375; // Bmult16 -> Cmult62
    (Amult[16] => Cmult[63]) = 35450; // Amult16 -> Cmult63
    (Bmult[16] => Cmult[63]) = 32469; // Bmult16 -> Cmult63
    (Amult[17] => Cmult[1]) = 5408; // Amult17 -> Cmult1
    (Bmult[17] => Cmult[1]) = 5012; // Bmult17 -> Cmult1
    (Amult[17] => Cmult[2]) = 6490; // Amult17 -> Cmult2
    (Bmult[17] => Cmult[2]) = 5998; // Bmult17 -> Cmult2
    (Amult[17] => Cmult[3]) = 6767; // Amult17 -> Cmult3
    (Bmult[17] => Cmult[3]) = 6258; // Bmult17 -> Cmult3
    (Amult[17] => Cmult[4]) = 7470; // Amult17 -> Cmult4
    (Bmult[17] => Cmult[4]) = 6721; // Bmult17 -> Cmult4
    (Amult[17] => Cmult[5]) = 8398; // Amult17 -> Cmult5
    (Bmult[17] => Cmult[5]) = 7383; // Bmult17 -> Cmult5
    (Amult[17] => Cmult[6]) = 9281; // Amult17 -> Cmult6
    (Bmult[17] => Cmult[6]) = 7827; // Bmult17 -> Cmult6
    (Amult[17] => Cmult[7]) = 9472; // Amult17 -> Cmult7
    (Bmult[17] => Cmult[7]) = 8516; // Bmult17 -> Cmult7
    (Amult[17] => Cmult[8]) = 10829; // Amult17 -> Cmult8
    (Bmult[17] => Cmult[8]) = 9292; // Bmult17 -> Cmult8
    (Amult[17] => Cmult[9]) = 11136; // Amult17 -> Cmult9
    (Bmult[17] => Cmult[9]) = 9817; // Bmult17 -> Cmult9
    (Amult[17] => Cmult[10]) = 11561; // Amult17 -> Cmult10
    (Bmult[17] => Cmult[10]) = 10465; // Bmult17 -> Cmult10
    (Amult[17] => Cmult[11]) = 12105; // Amult17 -> Cmult11
    (Bmult[17] => Cmult[11]) = 10895; // Bmult17 -> Cmult11
    (Amult[17] => Cmult[12]) = 12679; // Amult17 -> Cmult12
    (Bmult[17] => Cmult[12]) = 11145; // Bmult17 -> Cmult12
    (Amult[17] => Cmult[13]) = 13520; // Amult17 -> Cmult13
    (Bmult[17] => Cmult[13]) = 11832; // Bmult17 -> Cmult13
    (Amult[17] => Cmult[14]) = 14048; // Amult17 -> Cmult14
    (Bmult[17] => Cmult[14]) = 12260; // Bmult17 -> Cmult14
    (Amult[17] => Cmult[15]) = 15613; // Amult17 -> Cmult15
    (Bmult[17] => Cmult[15]) = 13605; // Bmult17 -> Cmult15
    (Amult[17] => Cmult[16]) = 15514; // Amult17 -> Cmult16
    (Bmult[17] => Cmult[16]) = 13779; // Bmult17 -> Cmult16
    (Amult[17] => Cmult[17]) = 15705; // Amult17 -> Cmult17
    (Bmult[17] => Cmult[17]) = 15557; // Bmult17 -> Cmult17
    (Amult[17] => Cmult[18]) = 16067; // Amult17 -> Cmult18
    (Bmult[17] => Cmult[18]) = 16348; // Bmult17 -> Cmult18
    (Amult[17] => Cmult[19]) = 16393; // Amult17 -> Cmult19
    (Bmult[17] => Cmult[19]) = 17038; // Bmult17 -> Cmult19
    (Amult[17] => Cmult[20]) = 16816; // Amult17 -> Cmult20
    (Bmult[17] => Cmult[20]) = 17610; // Bmult17 -> Cmult20
    (Amult[17] => Cmult[21]) = 17136; // Amult17 -> Cmult21
    (Bmult[17] => Cmult[21]) = 18157; // Bmult17 -> Cmult21
    (Amult[17] => Cmult[22]) = 17391; // Amult17 -> Cmult22
    (Bmult[17] => Cmult[22]) = 18920; // Bmult17 -> Cmult22
    (Amult[17] => Cmult[23]) = 17604; // Amult17 -> Cmult23
    (Bmult[17] => Cmult[23]) = 19660; // Bmult17 -> Cmult23
    (Amult[17] => Cmult[24]) = 17476; // Amult17 -> Cmult24
    (Bmult[17] => Cmult[24]) = 19949; // Bmult17 -> Cmult24
    (Amult[17] => Cmult[25]) = 17743; // Amult17 -> Cmult25
    (Bmult[17] => Cmult[25]) = 20515; // Bmult17 -> Cmult25
    (Amult[17] => Cmult[26]) = 18433; // Amult17 -> Cmult26
    (Bmult[17] => Cmult[26]) = 21542; // Bmult17 -> Cmult26
    (Amult[17] => Cmult[27]) = 18635; // Amult17 -> Cmult27
    (Bmult[17] => Cmult[27]) = 22115; // Bmult17 -> Cmult27
    (Amult[17] => Cmult[28]) = 18893; // Amult17 -> Cmult28
    (Bmult[17] => Cmult[28]) = 22539; // Bmult17 -> Cmult28
    (Amult[17] => Cmult[29]) = 19237; // Amult17 -> Cmult29
    (Bmult[17] => Cmult[29]) = 23317; // Bmult17 -> Cmult29
    (Amult[17] => Cmult[30]) = 19915; // Amult17 -> Cmult30
    (Bmult[17] => Cmult[30]) = 23837; // Bmult17 -> Cmult30
    (Amult[17] => Cmult[31]) = 20722; // Amult17 -> Cmult31
    (Bmult[17] => Cmult[31]) = 25163; // Bmult17 -> Cmult31
    (Amult[17] => Cmult[32]) = 26095; // Amult17 -> Cmult32
    (Bmult[17] => Cmult[32]) = 25528; // Bmult17 -> Cmult32
    (Amult[17] => Cmult[33]) = 26417; // Amult17 -> Cmult33
    (Bmult[17] => Cmult[33]) = 23361; // Bmult17 -> Cmult33
    (Amult[17] => Cmult[34]) = 26691; // Amult17 -> Cmult34
    (Bmult[17] => Cmult[34]) = 23626; // Bmult17 -> Cmult34
    (Amult[17] => Cmult[35]) = 26942; // Amult17 -> Cmult35
    (Bmult[17] => Cmult[35]) = 23778; // Bmult17 -> Cmult35
    (Amult[17] => Cmult[36]) = 27112; // Amult17 -> Cmult36
    (Bmult[17] => Cmult[36]) = 24040; // Bmult17 -> Cmult36
    (Amult[17] => Cmult[37]) = 27211; // Amult17 -> Cmult37
    (Bmult[17] => Cmult[37]) = 24187; // Bmult17 -> Cmult37
    (Amult[17] => Cmult[38]) = 27590; // Amult17 -> Cmult38
    (Bmult[17] => Cmult[38]) = 24565; // Bmult17 -> Cmult38
    (Amult[17] => Cmult[39]) = 27891; // Amult17 -> Cmult39
    (Bmult[17] => Cmult[39]) = 24817; // Bmult17 -> Cmult39
    (Amult[17] => Cmult[40]) = 28095; // Amult17 -> Cmult40
    (Bmult[17] => Cmult[40]) = 25096; // Bmult17 -> Cmult40
    (Amult[17] => Cmult[41]) = 28341; // Amult17 -> Cmult41
    (Bmult[17] => Cmult[41]) = 25261; // Bmult17 -> Cmult41
    (Amult[17] => Cmult[42]) = 27773; // Amult17 -> Cmult42
    (Bmult[17] => Cmult[42]) = 24783; // Bmult17 -> Cmult42
    (Amult[17] => Cmult[43]) = 28463; // Amult17 -> Cmult43
    (Bmult[17] => Cmult[43]) = 25472; // Bmult17 -> Cmult43
    (Amult[17] => Cmult[44]) = 28921; // Amult17 -> Cmult44
    (Bmult[17] => Cmult[44]) = 25989; // Bmult17 -> Cmult44
    (Amult[17] => Cmult[45]) = 29079; // Amult17 -> Cmult45
    (Bmult[17] => Cmult[45]) = 26088; // Bmult17 -> Cmult45
    (Amult[17] => Cmult[46]) = 28469; // Amult17 -> Cmult46
    (Bmult[17] => Cmult[46]) = 25478; // Bmult17 -> Cmult46
    (Amult[17] => Cmult[47]) = 28411; // Amult17 -> Cmult47
    (Bmult[17] => Cmult[47]) = 25325; // Bmult17 -> Cmult47
    (Amult[17] => Cmult[48]) = 29390; // Amult17 -> Cmult48
    (Bmult[17] => Cmult[48]) = 26400; // Bmult17 -> Cmult48
    (Amult[17] => Cmult[49]) = 29226; // Amult17 -> Cmult49
    (Bmult[17] => Cmult[49]) = 26146; // Bmult17 -> Cmult49
    (Amult[17] => Cmult[50]) = 30000; // Amult17 -> Cmult50
    (Bmult[17] => Cmult[50]) = 27022; // Bmult17 -> Cmult50
    (Amult[17] => Cmult[51]) = 30193; // Amult17 -> Cmult51
    (Bmult[17] => Cmult[51]) = 27247; // Bmult17 -> Cmult51
    (Amult[17] => Cmult[52]) = 30846; // Amult17 -> Cmult52
    (Bmult[17] => Cmult[52]) = 27868; // Bmult17 -> Cmult52
    (Amult[17] => Cmult[53]) = 31118; // Amult17 -> Cmult53
    (Bmult[17] => Cmult[53]) = 28199; // Bmult17 -> Cmult53
    (Amult[17] => Cmult[54]) = 31503; // Amult17 -> Cmult54
    (Bmult[17] => Cmult[54]) = 28525; // Bmult17 -> Cmult54
    (Amult[17] => Cmult[55]) = 31655; // Amult17 -> Cmult55
    (Bmult[17] => Cmult[55]) = 28736; // Bmult17 -> Cmult55
    (Amult[17] => Cmult[56]) = 32184; // Amult17 -> Cmult56
    (Bmult[17] => Cmult[56]) = 29206; // Bmult17 -> Cmult56
    (Amult[17] => Cmult[57]) = 32470; // Amult17 -> Cmult57
    (Bmult[17] => Cmult[57]) = 29491; // Bmult17 -> Cmult57
    (Amult[17] => Cmult[58]) = 32928; // Amult17 -> Cmult58
    (Bmult[17] => Cmult[58]) = 29949; // Bmult17 -> Cmult58
    (Amult[17] => Cmult[59]) = 32997; // Amult17 -> Cmult59
    (Bmult[17] => Cmult[59]) = 30018; // Bmult17 -> Cmult59
    (Amult[17] => Cmult[60]) = 33559; // Amult17 -> Cmult60
    (Bmult[17] => Cmult[60]) = 30580; // Bmult17 -> Cmult60
    (Amult[17] => Cmult[61]) = 33582; // Amult17 -> Cmult61
    (Bmult[17] => Cmult[61]) = 30663; // Bmult17 -> Cmult61
    (Amult[17] => Cmult[62]) = 34355; // Amult17 -> Cmult62
    (Bmult[17] => Cmult[62]) = 31375; // Bmult17 -> Cmult62
    (Amult[17] => Cmult[63]) = 35450; // Amult17 -> Cmult63
    (Bmult[17] => Cmult[63]) = 32469; // Bmult17 -> Cmult63
    (Amult[18] => Cmult[1]) = 5408; // Amult18 -> Cmult1
    (Bmult[18] => Cmult[1]) = 5012; // Bmult18 -> Cmult1
    (Amult[18] => Cmult[2]) = 6490; // Amult18 -> Cmult2
    (Bmult[18] => Cmult[2]) = 5998; // Bmult18 -> Cmult2
    (Amult[18] => Cmult[3]) = 6767; // Amult18 -> Cmult3
    (Bmult[18] => Cmult[3]) = 6258; // Bmult18 -> Cmult3
    (Amult[18] => Cmult[4]) = 7470; // Amult18 -> Cmult4
    (Bmult[18] => Cmult[4]) = 6721; // Bmult18 -> Cmult4
    (Amult[18] => Cmult[5]) = 8398; // Amult18 -> Cmult5
    (Bmult[18] => Cmult[5]) = 7383; // Bmult18 -> Cmult5
    (Amult[18] => Cmult[6]) = 9281; // Amult18 -> Cmult6
    (Bmult[18] => Cmult[6]) = 7827; // Bmult18 -> Cmult6
    (Amult[18] => Cmult[7]) = 9472; // Amult18 -> Cmult7
    (Bmult[18] => Cmult[7]) = 8516; // Bmult18 -> Cmult7
    (Amult[18] => Cmult[8]) = 10829; // Amult18 -> Cmult8
    (Bmult[18] => Cmult[8]) = 9292; // Bmult18 -> Cmult8
    (Amult[18] => Cmult[9]) = 11136; // Amult18 -> Cmult9
    (Bmult[18] => Cmult[9]) = 9817; // Bmult18 -> Cmult9
    (Amult[18] => Cmult[10]) = 11561; // Amult18 -> Cmult10
    (Bmult[18] => Cmult[10]) = 10465; // Bmult18 -> Cmult10
    (Amult[18] => Cmult[11]) = 12105; // Amult18 -> Cmult11
    (Bmult[18] => Cmult[11]) = 10895; // Bmult18 -> Cmult11
    (Amult[18] => Cmult[12]) = 12679; // Amult18 -> Cmult12
    (Bmult[18] => Cmult[12]) = 11145; // Bmult18 -> Cmult12
    (Amult[18] => Cmult[13]) = 13520; // Amult18 -> Cmult13
    (Bmult[18] => Cmult[13]) = 11832; // Bmult18 -> Cmult13
    (Amult[18] => Cmult[14]) = 14048; // Amult18 -> Cmult14
    (Bmult[18] => Cmult[14]) = 12260; // Bmult18 -> Cmult14
    (Amult[18] => Cmult[15]) = 15613; // Amult18 -> Cmult15
    (Bmult[18] => Cmult[15]) = 13605; // Bmult18 -> Cmult15
    (Amult[18] => Cmult[16]) = 15514; // Amult18 -> Cmult16
    (Bmult[18] => Cmult[16]) = 13779; // Bmult18 -> Cmult16
    (Amult[18] => Cmult[17]) = 15705; // Amult18 -> Cmult17
    (Bmult[18] => Cmult[17]) = 14160; // Bmult18 -> Cmult17
    (Amult[18] => Cmult[18]) = 16067; // Amult18 -> Cmult18
    (Bmult[18] => Cmult[18]) = 15297; // Bmult18 -> Cmult18
    (Amult[18] => Cmult[19]) = 16393; // Amult18 -> Cmult19
    (Bmult[18] => Cmult[19]) = 16346; // Bmult18 -> Cmult19
    (Amult[18] => Cmult[20]) = 16816; // Amult18 -> Cmult20
    (Bmult[18] => Cmult[20]) = 16968; // Bmult18 -> Cmult20
    (Amult[18] => Cmult[21]) = 17136; // Amult18 -> Cmult21
    (Bmult[18] => Cmult[21]) = 17632; // Bmult18 -> Cmult21
    (Amult[18] => Cmult[22]) = 17391; // Amult18 -> Cmult22
    (Bmult[18] => Cmult[22]) = 18277; // Bmult18 -> Cmult22
    (Amult[18] => Cmult[23]) = 17604; // Amult18 -> Cmult23
    (Bmult[18] => Cmult[23]) = 19017; // Bmult18 -> Cmult23
    (Amult[18] => Cmult[24]) = 17476; // Amult18 -> Cmult24
    (Bmult[18] => Cmult[24]) = 19357; // Bmult18 -> Cmult24
    (Amult[18] => Cmult[25]) = 17743; // Amult18 -> Cmult25
    (Bmult[18] => Cmult[25]) = 19899; // Bmult18 -> Cmult25
    (Amult[18] => Cmult[26]) = 18433; // Amult18 -> Cmult26
    (Bmult[18] => Cmult[26]) = 20925; // Bmult18 -> Cmult26
    (Amult[18] => Cmult[27]) = 18635; // Amult18 -> Cmult27
    (Bmult[18] => Cmult[27]) = 21476; // Bmult18 -> Cmult27
    (Amult[18] => Cmult[28]) = 18893; // Amult18 -> Cmult28
    (Bmult[18] => Cmult[28]) = 21978; // Bmult18 -> Cmult28
    (Amult[18] => Cmult[29]) = 19237; // Amult18 -> Cmult29
    (Bmult[18] => Cmult[29]) = 22707; // Bmult18 -> Cmult29
    (Amult[18] => Cmult[30]) = 19915; // Amult18 -> Cmult30
    (Bmult[18] => Cmult[30]) = 23212; // Bmult18 -> Cmult30
    (Amult[18] => Cmult[31]) = 20722; // Amult18 -> Cmult31
    (Bmult[18] => Cmult[31]) = 24656; // Bmult18 -> Cmult31
    (Amult[18] => Cmult[32]) = 26095; // Amult18 -> Cmult32
    (Bmult[18] => Cmult[32]) = 24918; // Bmult18 -> Cmult32
    (Amult[18] => Cmult[33]) = 26417; // Amult18 -> Cmult33
    (Bmult[18] => Cmult[33]) = 25261; // Bmult18 -> Cmult33
    (Amult[18] => Cmult[34]) = 26691; // Amult18 -> Cmult34
    (Bmult[18] => Cmult[34]) = 23626; // Bmult18 -> Cmult34
    (Amult[18] => Cmult[35]) = 26942; // Amult18 -> Cmult35
    (Bmult[18] => Cmult[35]) = 23778; // Bmult18 -> Cmult35
    (Amult[18] => Cmult[36]) = 27112; // Amult18 -> Cmult36
    (Bmult[18] => Cmult[36]) = 24040; // Bmult18 -> Cmult36
    (Amult[18] => Cmult[37]) = 27211; // Amult18 -> Cmult37
    (Bmult[18] => Cmult[37]) = 24187; // Bmult18 -> Cmult37
    (Amult[18] => Cmult[38]) = 27590; // Amult18 -> Cmult38
    (Bmult[18] => Cmult[38]) = 24565; // Bmult18 -> Cmult38
    (Amult[18] => Cmult[39]) = 27891; // Amult18 -> Cmult39
    (Bmult[18] => Cmult[39]) = 24817; // Bmult18 -> Cmult39
    (Amult[18] => Cmult[40]) = 28095; // Amult18 -> Cmult40
    (Bmult[18] => Cmult[40]) = 25096; // Bmult18 -> Cmult40
    (Amult[18] => Cmult[41]) = 28341; // Amult18 -> Cmult41
    (Bmult[18] => Cmult[41]) = 25261; // Bmult18 -> Cmult41
    (Amult[18] => Cmult[42]) = 27773; // Amult18 -> Cmult42
    (Bmult[18] => Cmult[42]) = 24783; // Bmult18 -> Cmult42
    (Amult[18] => Cmult[43]) = 28463; // Amult18 -> Cmult43
    (Bmult[18] => Cmult[43]) = 25472; // Bmult18 -> Cmult43
    (Amult[18] => Cmult[44]) = 28921; // Amult18 -> Cmult44
    (Bmult[18] => Cmult[44]) = 25989; // Bmult18 -> Cmult44
    (Amult[18] => Cmult[45]) = 29079; // Amult18 -> Cmult45
    (Bmult[18] => Cmult[45]) = 26088; // Bmult18 -> Cmult45
    (Amult[18] => Cmult[46]) = 28469; // Amult18 -> Cmult46
    (Bmult[18] => Cmult[46]) = 25478; // Bmult18 -> Cmult46
    (Amult[18] => Cmult[47]) = 28411; // Amult18 -> Cmult47
    (Bmult[18] => Cmult[47]) = 25325; // Bmult18 -> Cmult47
    (Amult[18] => Cmult[48]) = 29390; // Amult18 -> Cmult48
    (Bmult[18] => Cmult[48]) = 26400; // Bmult18 -> Cmult48
    (Amult[18] => Cmult[49]) = 29226; // Amult18 -> Cmult49
    (Bmult[18] => Cmult[49]) = 26146; // Bmult18 -> Cmult49
    (Amult[18] => Cmult[50]) = 30000; // Amult18 -> Cmult50
    (Bmult[18] => Cmult[50]) = 27022; // Bmult18 -> Cmult50
    (Amult[18] => Cmult[51]) = 30193; // Amult18 -> Cmult51
    (Bmult[18] => Cmult[51]) = 27247; // Bmult18 -> Cmult51
    (Amult[18] => Cmult[52]) = 30846; // Amult18 -> Cmult52
    (Bmult[18] => Cmult[52]) = 27868; // Bmult18 -> Cmult52
    (Amult[18] => Cmult[53]) = 31118; // Amult18 -> Cmult53
    (Bmult[18] => Cmult[53]) = 28199; // Bmult18 -> Cmult53
    (Amult[18] => Cmult[54]) = 31503; // Amult18 -> Cmult54
    (Bmult[18] => Cmult[54]) = 28525; // Bmult18 -> Cmult54
    (Amult[18] => Cmult[55]) = 31655; // Amult18 -> Cmult55
    (Bmult[18] => Cmult[55]) = 28736; // Bmult18 -> Cmult55
    (Amult[18] => Cmult[56]) = 32184; // Amult18 -> Cmult56
    (Bmult[18] => Cmult[56]) = 29206; // Bmult18 -> Cmult56
    (Amult[18] => Cmult[57]) = 32470; // Amult18 -> Cmult57
    (Bmult[18] => Cmult[57]) = 29491; // Bmult18 -> Cmult57
    (Amult[18] => Cmult[58]) = 32928; // Amult18 -> Cmult58
    (Bmult[18] => Cmult[58]) = 29949; // Bmult18 -> Cmult58
    (Amult[18] => Cmult[59]) = 32997; // Amult18 -> Cmult59
    (Bmult[18] => Cmult[59]) = 30018; // Bmult18 -> Cmult59
    (Amult[18] => Cmult[60]) = 33559; // Amult18 -> Cmult60
    (Bmult[18] => Cmult[60]) = 30580; // Bmult18 -> Cmult60
    (Amult[18] => Cmult[61]) = 33582; // Amult18 -> Cmult61
    (Bmult[18] => Cmult[61]) = 30663; // Bmult18 -> Cmult61
    (Amult[18] => Cmult[62]) = 34355; // Amult18 -> Cmult62
    (Bmult[18] => Cmult[62]) = 31375; // Bmult18 -> Cmult62
    (Amult[18] => Cmult[63]) = 35450; // Amult18 -> Cmult63
    (Bmult[18] => Cmult[63]) = 32469; // Bmult18 -> Cmult63
    (Amult[19] => Cmult[1]) = 5408; // Amult19 -> Cmult1
    (Bmult[19] => Cmult[1]) = 5012; // Bmult19 -> Cmult1
    (Amult[19] => Cmult[2]) = 6490; // Amult19 -> Cmult2
    (Bmult[19] => Cmult[2]) = 5998; // Bmult19 -> Cmult2
    (Amult[19] => Cmult[3]) = 6767; // Amult19 -> Cmult3
    (Bmult[19] => Cmult[3]) = 6258; // Bmult19 -> Cmult3
    (Amult[19] => Cmult[4]) = 7470; // Amult19 -> Cmult4
    (Bmult[19] => Cmult[4]) = 6721; // Bmult19 -> Cmult4
    (Amult[19] => Cmult[5]) = 8398; // Amult19 -> Cmult5
    (Bmult[19] => Cmult[5]) = 7383; // Bmult19 -> Cmult5
    (Amult[19] => Cmult[6]) = 9281; // Amult19 -> Cmult6
    (Bmult[19] => Cmult[6]) = 7827; // Bmult19 -> Cmult6
    (Amult[19] => Cmult[7]) = 9472; // Amult19 -> Cmult7
    (Bmult[19] => Cmult[7]) = 8516; // Bmult19 -> Cmult7
    (Amult[19] => Cmult[8]) = 10829; // Amult19 -> Cmult8
    (Bmult[19] => Cmult[8]) = 9292; // Bmult19 -> Cmult8
    (Amult[19] => Cmult[9]) = 11136; // Amult19 -> Cmult9
    (Bmult[19] => Cmult[9]) = 9817; // Bmult19 -> Cmult9
    (Amult[19] => Cmult[10]) = 11561; // Amult19 -> Cmult10
    (Bmult[19] => Cmult[10]) = 10465; // Bmult19 -> Cmult10
    (Amult[19] => Cmult[11]) = 12105; // Amult19 -> Cmult11
    (Bmult[19] => Cmult[11]) = 10895; // Bmult19 -> Cmult11
    (Amult[19] => Cmult[12]) = 12679; // Amult19 -> Cmult12
    (Bmult[19] => Cmult[12]) = 11145; // Bmult19 -> Cmult12
    (Amult[19] => Cmult[13]) = 13520; // Amult19 -> Cmult13
    (Bmult[19] => Cmult[13]) = 11832; // Bmult19 -> Cmult13
    (Amult[19] => Cmult[14]) = 14048; // Amult19 -> Cmult14
    (Bmult[19] => Cmult[14]) = 12260; // Bmult19 -> Cmult14
    (Amult[19] => Cmult[15]) = 15613; // Amult19 -> Cmult15
    (Bmult[19] => Cmult[15]) = 13605; // Bmult19 -> Cmult15
    (Amult[19] => Cmult[16]) = 15514; // Amult19 -> Cmult16
    (Bmult[19] => Cmult[16]) = 13779; // Bmult19 -> Cmult16
    (Amult[19] => Cmult[17]) = 15705; // Amult19 -> Cmult17
    (Bmult[19] => Cmult[17]) = 14160; // Bmult19 -> Cmult17
    (Amult[19] => Cmult[18]) = 16067; // Amult19 -> Cmult18
    (Bmult[19] => Cmult[18]) = 13767; // Bmult19 -> Cmult18
    (Amult[19] => Cmult[19]) = 16393; // Amult19 -> Cmult19
    (Bmult[19] => Cmult[19]) = 16267; // Bmult19 -> Cmult19
    (Amult[19] => Cmult[20]) = 16816; // Amult19 -> Cmult20
    (Bmult[19] => Cmult[20]) = 16990; // Bmult19 -> Cmult20
    (Amult[19] => Cmult[21]) = 17136; // Amult19 -> Cmult21
    (Bmult[19] => Cmult[21]) = 17903; // Bmult19 -> Cmult21
    (Amult[19] => Cmult[22]) = 17391; // Amult19 -> Cmult22
    (Bmult[19] => Cmult[22]) = 18479; // Bmult19 -> Cmult22
    (Amult[19] => Cmult[23]) = 17604; // Amult19 -> Cmult23
    (Bmult[19] => Cmult[23]) = 19219; // Bmult19 -> Cmult23
    (Amult[19] => Cmult[24]) = 17476; // Amult19 -> Cmult24
    (Bmult[19] => Cmult[24]) = 19629; // Bmult19 -> Cmult24
    (Amult[19] => Cmult[25]) = 17743; // Amult19 -> Cmult25
    (Bmult[19] => Cmult[25]) = 20170; // Bmult19 -> Cmult25
    (Amult[19] => Cmult[26]) = 18433; // Amult19 -> Cmult26
    (Bmult[19] => Cmult[26]) = 21101; // Bmult19 -> Cmult26
    (Amult[19] => Cmult[27]) = 18635; // Amult19 -> Cmult27
    (Bmult[19] => Cmult[27]) = 21675; // Bmult19 -> Cmult27
    (Amult[19] => Cmult[28]) = 18893; // Amult19 -> Cmult28
    (Bmult[19] => Cmult[28]) = 22267; // Bmult19 -> Cmult28
    (Amult[19] => Cmult[29]) = 19237; // Amult19 -> Cmult29
    (Bmult[19] => Cmult[29]) = 22997; // Bmult19 -> Cmult29
    (Amult[19] => Cmult[30]) = 19915; // Amult19 -> Cmult30
    (Bmult[19] => Cmult[30]) = 23501; // Bmult19 -> Cmult30
    (Amult[19] => Cmult[31]) = 20722; // Amult19 -> Cmult31
    (Bmult[19] => Cmult[31]) = 24945; // Bmult19 -> Cmult31
    (Amult[19] => Cmult[32]) = 26095; // Amult19 -> Cmult32
    (Bmult[19] => Cmult[32]) = 25139; // Bmult19 -> Cmult32
    (Amult[19] => Cmult[33]) = 26417; // Amult19 -> Cmult33
    (Bmult[19] => Cmult[33]) = 25424; // Bmult19 -> Cmult33
    (Amult[19] => Cmult[34]) = 26691; // Amult19 -> Cmult34
    (Bmult[19] => Cmult[34]) = 25866; // Bmult19 -> Cmult34
    (Amult[19] => Cmult[35]) = 26942; // Amult19 -> Cmult35
    (Bmult[19] => Cmult[35]) = 23778; // Bmult19 -> Cmult35
    (Amult[19] => Cmult[36]) = 27112; // Amult19 -> Cmult36
    (Bmult[19] => Cmult[36]) = 24040; // Bmult19 -> Cmult36
    (Amult[19] => Cmult[37]) = 27211; // Amult19 -> Cmult37
    (Bmult[19] => Cmult[37]) = 24187; // Bmult19 -> Cmult37
    (Amult[19] => Cmult[38]) = 27590; // Amult19 -> Cmult38
    (Bmult[19] => Cmult[38]) = 24565; // Bmult19 -> Cmult38
    (Amult[19] => Cmult[39]) = 27891; // Amult19 -> Cmult39
    (Bmult[19] => Cmult[39]) = 24817; // Bmult19 -> Cmult39
    (Amult[19] => Cmult[40]) = 28095; // Amult19 -> Cmult40
    (Bmult[19] => Cmult[40]) = 25096; // Bmult19 -> Cmult40
    (Amult[19] => Cmult[41]) = 28341; // Amult19 -> Cmult41
    (Bmult[19] => Cmult[41]) = 25261; // Bmult19 -> Cmult41
    (Amult[19] => Cmult[42]) = 27773; // Amult19 -> Cmult42
    (Bmult[19] => Cmult[42]) = 24783; // Bmult19 -> Cmult42
    (Amult[19] => Cmult[43]) = 28463; // Amult19 -> Cmult43
    (Bmult[19] => Cmult[43]) = 25472; // Bmult19 -> Cmult43
    (Amult[19] => Cmult[44]) = 28921; // Amult19 -> Cmult44
    (Bmult[19] => Cmult[44]) = 25989; // Bmult19 -> Cmult44
    (Amult[19] => Cmult[45]) = 29079; // Amult19 -> Cmult45
    (Bmult[19] => Cmult[45]) = 26088; // Bmult19 -> Cmult45
    (Amult[19] => Cmult[46]) = 28469; // Amult19 -> Cmult46
    (Bmult[19] => Cmult[46]) = 25478; // Bmult19 -> Cmult46
    (Amult[19] => Cmult[47]) = 28411; // Amult19 -> Cmult47
    (Bmult[19] => Cmult[47]) = 25325; // Bmult19 -> Cmult47
    (Amult[19] => Cmult[48]) = 29390; // Amult19 -> Cmult48
    (Bmult[19] => Cmult[48]) = 26400; // Bmult19 -> Cmult48
    (Amult[19] => Cmult[49]) = 29226; // Amult19 -> Cmult49
    (Bmult[19] => Cmult[49]) = 26146; // Bmult19 -> Cmult49
    (Amult[19] => Cmult[50]) = 30000; // Amult19 -> Cmult50
    (Bmult[19] => Cmult[50]) = 27022; // Bmult19 -> Cmult50
    (Amult[19] => Cmult[51]) = 30193; // Amult19 -> Cmult51
    (Bmult[19] => Cmult[51]) = 27247; // Bmult19 -> Cmult51
    (Amult[19] => Cmult[52]) = 30846; // Amult19 -> Cmult52
    (Bmult[19] => Cmult[52]) = 27868; // Bmult19 -> Cmult52
    (Amult[19] => Cmult[53]) = 31118; // Amult19 -> Cmult53
    (Bmult[19] => Cmult[53]) = 28199; // Bmult19 -> Cmult53
    (Amult[19] => Cmult[54]) = 31503; // Amult19 -> Cmult54
    (Bmult[19] => Cmult[54]) = 28525; // Bmult19 -> Cmult54
    (Amult[19] => Cmult[55]) = 31655; // Amult19 -> Cmult55
    (Bmult[19] => Cmult[55]) = 28736; // Bmult19 -> Cmult55
    (Amult[19] => Cmult[56]) = 32184; // Amult19 -> Cmult56
    (Bmult[19] => Cmult[56]) = 29206; // Bmult19 -> Cmult56
    (Amult[19] => Cmult[57]) = 32470; // Amult19 -> Cmult57
    (Bmult[19] => Cmult[57]) = 29491; // Bmult19 -> Cmult57
    (Amult[19] => Cmult[58]) = 32928; // Amult19 -> Cmult58
    (Bmult[19] => Cmult[58]) = 29949; // Bmult19 -> Cmult58
    (Amult[19] => Cmult[59]) = 32997; // Amult19 -> Cmult59
    (Bmult[19] => Cmult[59]) = 30018; // Bmult19 -> Cmult59
    (Amult[19] => Cmult[60]) = 33559; // Amult19 -> Cmult60
    (Bmult[19] => Cmult[60]) = 30580; // Bmult19 -> Cmult60
    (Amult[19] => Cmult[61]) = 33582; // Amult19 -> Cmult61
    (Bmult[19] => Cmult[61]) = 30663; // Bmult19 -> Cmult61
    (Amult[19] => Cmult[62]) = 34355; // Amult19 -> Cmult62
    (Bmult[19] => Cmult[62]) = 31375; // Bmult19 -> Cmult62
    (Amult[19] => Cmult[63]) = 35450; // Amult19 -> Cmult63
    (Bmult[19] => Cmult[63]) = 32469; // Bmult19 -> Cmult63
    (Amult[20] => Cmult[2]) = 6007; // Amult20 -> Cmult2
    (Bmult[20] => Cmult[2]) = 6032; // Bmult20 -> Cmult2
    (Amult[20] => Cmult[3]) = 6209; // Amult20 -> Cmult3
    (Bmult[20] => Cmult[3]) = 6377; // Bmult20 -> Cmult3
    (Amult[20] => Cmult[4]) = 6895; // Amult20 -> Cmult4
    (Bmult[20] => Cmult[4]) = 6848; // Bmult20 -> Cmult4
    (Amult[20] => Cmult[5]) = 7784; // Amult20 -> Cmult5
    (Bmult[20] => Cmult[5]) = 7568; // Bmult20 -> Cmult5
    (Amult[20] => Cmult[6]) = 8701; // Amult20 -> Cmult6
    (Bmult[20] => Cmult[6]) = 8023; // Bmult20 -> Cmult6
    (Amult[20] => Cmult[7]) = 8892; // Amult20 -> Cmult7
    (Bmult[20] => Cmult[7]) = 8770; // Bmult20 -> Cmult7
    (Amult[20] => Cmult[8]) = 10272; // Amult20 -> Cmult8
    (Bmult[20] => Cmult[8]) = 9515; // Bmult20 -> Cmult8
    (Amult[20] => Cmult[9]) = 10730; // Amult20 -> Cmult9
    (Bmult[20] => Cmult[9]) = 10069; // Bmult20 -> Cmult9
    (Amult[20] => Cmult[10]) = 11045; // Amult20 -> Cmult10
    (Bmult[20] => Cmult[10]) = 10591; // Bmult20 -> Cmult10
    (Amult[20] => Cmult[11]) = 11666; // Amult20 -> Cmult11
    (Bmult[20] => Cmult[11]) = 11080; // Bmult20 -> Cmult11
    (Amult[20] => Cmult[12]) = 12256; // Amult20 -> Cmult12
    (Bmult[20] => Cmult[12]) = 11409; // Bmult20 -> Cmult12
    (Amult[20] => Cmult[13]) = 12759; // Amult20 -> Cmult13
    (Bmult[20] => Cmult[13]) = 12074; // Bmult20 -> Cmult13
    (Amult[20] => Cmult[14]) = 13409; // Amult20 -> Cmult14
    (Bmult[20] => Cmult[14]) = 12600; // Bmult20 -> Cmult14
    (Amult[20] => Cmult[15]) = 15103; // Amult20 -> Cmult15
    (Bmult[20] => Cmult[15]) = 13797; // Bmult20 -> Cmult15
    (Amult[20] => Cmult[16]) = 15003; // Amult20 -> Cmult16
    (Bmult[20] => Cmult[16]) = 13970; // Bmult20 -> Cmult16
    (Amult[20] => Cmult[17]) = 15095; // Amult20 -> Cmult17
    (Bmult[20] => Cmult[17]) = 14352; // Bmult20 -> Cmult17
    (Amult[20] => Cmult[18]) = 15429; // Amult20 -> Cmult18
    (Bmult[20] => Cmult[18]) = 13959; // Bmult20 -> Cmult18
    (Amult[20] => Cmult[19]) = 15755; // Amult20 -> Cmult19
    (Bmult[20] => Cmult[19]) = 14200; // Bmult20 -> Cmult19
    (Amult[20] => Cmult[20]) = 16197; // Amult20 -> Cmult20
    (Bmult[20] => Cmult[20]) = 16985; // Bmult20 -> Cmult20
    (Amult[20] => Cmult[21]) = 16498; // Amult20 -> Cmult21
    (Bmult[20] => Cmult[21]) = 17980; // Bmult20 -> Cmult21
    (Amult[20] => Cmult[22]) = 16797; // Amult20 -> Cmult22
    (Bmult[20] => Cmult[22]) = 18607; // Bmult20 -> Cmult22
    (Amult[20] => Cmult[23]) = 16966; // Amult20 -> Cmult23
    (Bmult[20] => Cmult[23]) = 19347; // Bmult20 -> Cmult23
    (Amult[20] => Cmult[24]) = 16849; // Amult20 -> Cmult24
    (Bmult[20] => Cmult[24]) = 19705; // Bmult20 -> Cmult24
    (Amult[20] => Cmult[25]) = 17105; // Amult20 -> Cmult25
    (Bmult[20] => Cmult[25]) = 20262; // Bmult20 -> Cmult25
    (Amult[20] => Cmult[26]) = 17868; // Amult20 -> Cmult26
    (Bmult[20] => Cmult[26]) = 21304; // Bmult20 -> Cmult26
    (Amult[20] => Cmult[27]) = 17997; // Amult20 -> Cmult27
    (Bmult[20] => Cmult[27]) = 21878; // Bmult20 -> Cmult27
    (Amult[20] => Cmult[28]) = 18261; // Amult20 -> Cmult28
    (Bmult[20] => Cmult[28]) = 22344; // Bmult20 -> Cmult28
    (Amult[20] => Cmult[29]) = 18599; // Amult20 -> Cmult29
    (Bmult[20] => Cmult[29]) = 23081; // Bmult20 -> Cmult29
    (Amult[20] => Cmult[30]) = 19277; // Amult20 -> Cmult30
    (Bmult[20] => Cmult[30]) = 23601; // Bmult20 -> Cmult30
    (Amult[20] => Cmult[31]) = 20084; // Amult20 -> Cmult31
    (Bmult[20] => Cmult[31]) = 25022; // Bmult20 -> Cmult31
    (Amult[20] => Cmult[32]) = 25227; // Amult20 -> Cmult32
    (Bmult[20] => Cmult[32]) = 25320; // Bmult20 -> Cmult32
    (Amult[20] => Cmult[33]) = 25481; // Amult20 -> Cmult33
    (Bmult[20] => Cmult[33]) = 25663; // Bmult20 -> Cmult33
    (Amult[20] => Cmult[34]) = 25723; // Amult20 -> Cmult34
    (Bmult[20] => Cmult[34]) = 25953; // Bmult20 -> Cmult34
    (Amult[20] => Cmult[35]) = 25898; // Amult20 -> Cmult35
    (Bmult[20] => Cmult[35]) = 26182; // Bmult20 -> Cmult35
    (Amult[20] => Cmult[36]) = 26243; // Amult20 -> Cmult36
    (Bmult[20] => Cmult[36]) = 24366; // Bmult20 -> Cmult36
    (Amult[20] => Cmult[37]) = 26451; // Amult20 -> Cmult37
    (Bmult[20] => Cmult[37]) = 24481; // Bmult20 -> Cmult37
    (Amult[20] => Cmult[38]) = 26693; // Amult20 -> Cmult38
    (Bmult[20] => Cmult[38]) = 24843; // Bmult20 -> Cmult38
    (Amult[20] => Cmult[39]) = 26936; // Amult20 -> Cmult39
    (Bmult[20] => Cmult[39]) = 25144; // Bmult20 -> Cmult39
    (Amult[20] => Cmult[40]) = 27284; // Amult20 -> Cmult40
    (Bmult[20] => Cmult[40]) = 25354; // Bmult20 -> Cmult40
    (Amult[20] => Cmult[41]) = 27386; // Amult20 -> Cmult41
    (Bmult[20] => Cmult[41]) = 25588; // Bmult20 -> Cmult41
    (Amult[20] => Cmult[42]) = 26933; // Amult20 -> Cmult42
    (Bmult[20] => Cmult[42]) = 25041; // Bmult20 -> Cmult42
    (Amult[20] => Cmult[43]) = 27508; // Amult20 -> Cmult43
    (Bmult[20] => Cmult[43]) = 25731; // Bmult20 -> Cmult43
    (Amult[20] => Cmult[44]) = 28160; // Amult20 -> Cmult44
    (Bmult[20] => Cmult[44]) = 26173; // Bmult20 -> Cmult44
    (Amult[20] => Cmult[45]) = 28124; // Amult20 -> Cmult45
    (Bmult[20] => Cmult[45]) = 26347; // Bmult20 -> Cmult45
    (Amult[20] => Cmult[46]) = 27644; // Amult20 -> Cmult46
    (Bmult[20] => Cmult[46]) = 25736; // Bmult20 -> Cmult46
    (Amult[20] => Cmult[47]) = 27457; // Amult20 -> Cmult47
    (Bmult[20] => Cmult[47]) = 25652; // Bmult20 -> Cmult47
    (Amult[20] => Cmult[48]) = 28523; // Amult20 -> Cmult48
    (Bmult[20] => Cmult[48]) = 26658; // Bmult20 -> Cmult48
    (Amult[20] => Cmult[49]) = 28317; // Amult20 -> Cmult49
    (Bmult[20] => Cmult[49]) = 26458; // Bmult20 -> Cmult49
    (Amult[20] => Cmult[50]) = 29055; // Amult20 -> Cmult50
    (Bmult[20] => Cmult[50]) = 27280; // Bmult20 -> Cmult50
    (Amult[20] => Cmult[51]) = 29406; // Amult20 -> Cmult51
    (Bmult[20] => Cmult[51]) = 27472; // Bmult20 -> Cmult51
    (Amult[20] => Cmult[52]) = 29892; // Amult20 -> Cmult52
    (Bmult[20] => Cmult[52]) = 28126; // Bmult20 -> Cmult52
    (Amult[20] => Cmult[53]) = 30357; // Amult20 -> Cmult53
    (Bmult[20] => Cmult[53]) = 28383; // Bmult20 -> Cmult53
    (Amult[20] => Cmult[54]) = 30636; // Amult20 -> Cmult54
    (Bmult[20] => Cmult[54]) = 28783; // Bmult20 -> Cmult54
    (Amult[20] => Cmult[55]) = 30894; // Amult20 -> Cmult55
    (Bmult[20] => Cmult[55]) = 28920; // Bmult20 -> Cmult55
    (Amult[20] => Cmult[56]) = 31230; // Amult20 -> Cmult56
    (Bmult[20] => Cmult[56]) = 29464; // Bmult20 -> Cmult56
    (Amult[20] => Cmult[57]) = 31612; // Amult20 -> Cmult57
    (Bmult[20] => Cmult[57]) = 29750; // Bmult20 -> Cmult57
    (Amult[20] => Cmult[58]) = 31976; // Amult20 -> Cmult58
    (Bmult[20] => Cmult[58]) = 30208; // Bmult20 -> Cmult58
    (Amult[20] => Cmult[59]) = 32146; // Amult20 -> Cmult59
    (Bmult[20] => Cmult[59]) = 30276; // Bmult20 -> Cmult59
    (Amult[20] => Cmult[60]) = 32604; // Amult20 -> Cmult60
    (Bmult[20] => Cmult[60]) = 30839; // Bmult20 -> Cmult60
    (Amult[20] => Cmult[61]) = 32822; // Amult20 -> Cmult61
    (Bmult[20] => Cmult[61]) = 30847; // Bmult20 -> Cmult61
    (Amult[20] => Cmult[62]) = 33401; // Amult20 -> Cmult62
    (Bmult[20] => Cmult[62]) = 31633; // Bmult20 -> Cmult62
    (Amult[20] => Cmult[63]) = 34496; // Amult20 -> Cmult63
    (Bmult[20] => Cmult[63]) = 32727; // Bmult20 -> Cmult63
    (Amult[21] => Cmult[2]) = 6007; // Amult21 -> Cmult2
    (Bmult[21] => Cmult[2]) = 6032; // Bmult21 -> Cmult2
    (Amult[21] => Cmult[3]) = 6209; // Amult21 -> Cmult3
    (Bmult[21] => Cmult[3]) = 6377; // Bmult21 -> Cmult3
    (Amult[21] => Cmult[4]) = 6895; // Amult21 -> Cmult4
    (Bmult[21] => Cmult[4]) = 6848; // Bmult21 -> Cmult4
    (Amult[21] => Cmult[5]) = 7784; // Amult21 -> Cmult5
    (Bmult[21] => Cmult[5]) = 7568; // Bmult21 -> Cmult5
    (Amult[21] => Cmult[6]) = 8701; // Amult21 -> Cmult6
    (Bmult[21] => Cmult[6]) = 8023; // Bmult21 -> Cmult6
    (Amult[21] => Cmult[7]) = 8892; // Amult21 -> Cmult7
    (Bmult[21] => Cmult[7]) = 8770; // Bmult21 -> Cmult7
    (Amult[21] => Cmult[8]) = 10272; // Amult21 -> Cmult8
    (Bmult[21] => Cmult[8]) = 9515; // Bmult21 -> Cmult8
    (Amult[21] => Cmult[9]) = 10730; // Amult21 -> Cmult9
    (Bmult[21] => Cmult[9]) = 10069; // Bmult21 -> Cmult9
    (Amult[21] => Cmult[10]) = 11045; // Amult21 -> Cmult10
    (Bmult[21] => Cmult[10]) = 10591; // Bmult21 -> Cmult10
    (Amult[21] => Cmult[11]) = 11666; // Amult21 -> Cmult11
    (Bmult[21] => Cmult[11]) = 11080; // Bmult21 -> Cmult11
    (Amult[21] => Cmult[12]) = 12256; // Amult21 -> Cmult12
    (Bmult[21] => Cmult[12]) = 11409; // Bmult21 -> Cmult12
    (Amult[21] => Cmult[13]) = 12759; // Amult21 -> Cmult13
    (Bmult[21] => Cmult[13]) = 12074; // Bmult21 -> Cmult13
    (Amult[21] => Cmult[14]) = 13409; // Amult21 -> Cmult14
    (Bmult[21] => Cmult[14]) = 12600; // Bmult21 -> Cmult14
    (Amult[21] => Cmult[15]) = 15103; // Amult21 -> Cmult15
    (Bmult[21] => Cmult[15]) = 13797; // Bmult21 -> Cmult15
    (Amult[21] => Cmult[16]) = 15003; // Amult21 -> Cmult16
    (Bmult[21] => Cmult[16]) = 13970; // Bmult21 -> Cmult16
    (Amult[21] => Cmult[17]) = 15095; // Amult21 -> Cmult17
    (Bmult[21] => Cmult[17]) = 14352; // Bmult21 -> Cmult17
    (Amult[21] => Cmult[18]) = 15429; // Amult21 -> Cmult18
    (Bmult[21] => Cmult[18]) = 13959; // Bmult21 -> Cmult18
    (Amult[21] => Cmult[19]) = 15755; // Amult21 -> Cmult19
    (Bmult[21] => Cmult[19]) = 14200; // Bmult21 -> Cmult19
    (Amult[21] => Cmult[20]) = 16197; // Amult21 -> Cmult20
    (Bmult[21] => Cmult[20]) = 14544; // Bmult21 -> Cmult20
    (Amult[21] => Cmult[21]) = 16498; // Amult21 -> Cmult21
    (Bmult[21] => Cmult[21]) = 17536; // Bmult21 -> Cmult21
    (Amult[21] => Cmult[22]) = 16797; // Amult21 -> Cmult22
    (Bmult[21] => Cmult[22]) = 18313; // Bmult21 -> Cmult22
    (Amult[21] => Cmult[23]) = 16966; // Amult21 -> Cmult23
    (Bmult[21] => Cmult[23]) = 19053; // Bmult21 -> Cmult23
    (Amult[21] => Cmult[24]) = 16849; // Amult21 -> Cmult24
    (Bmult[21] => Cmult[24]) = 19510; // Bmult21 -> Cmult24
    (Amult[21] => Cmult[25]) = 17105; // Amult21 -> Cmult25
    (Bmult[21] => Cmult[25]) = 20064; // Bmult21 -> Cmult25
    (Amult[21] => Cmult[26]) = 17868; // Amult21 -> Cmult26
    (Bmult[21] => Cmult[26]) = 21027; // Bmult21 -> Cmult26
    (Amult[21] => Cmult[27]) = 17997; // Amult21 -> Cmult27
    (Bmult[21] => Cmult[27]) = 21583; // Bmult21 -> Cmult27
    (Amult[21] => Cmult[28]) = 18261; // Amult21 -> Cmult28
    (Bmult[21] => Cmult[28]) = 22336; // Bmult21 -> Cmult28
    (Amult[21] => Cmult[29]) = 18599; // Amult21 -> Cmult29
    (Bmult[21] => Cmult[29]) = 23065; // Bmult21 -> Cmult29
    (Amult[21] => Cmult[30]) = 19277; // Amult21 -> Cmult30
    (Bmult[21] => Cmult[30]) = 23570; // Bmult21 -> Cmult30
    (Amult[21] => Cmult[31]) = 20084; // Amult21 -> Cmult31
    (Bmult[21] => Cmult[31]) = 25014; // Bmult21 -> Cmult31
    (Amult[21] => Cmult[32]) = 25227; // Amult21 -> Cmult32
    (Bmult[21] => Cmult[32]) = 25207; // Bmult21 -> Cmult32
    (Amult[21] => Cmult[33]) = 25481; // Amult21 -> Cmult33
    (Bmult[21] => Cmult[33]) = 25432; // Bmult21 -> Cmult33
    (Amult[21] => Cmult[34]) = 25723; // Amult21 -> Cmult34
    (Bmult[21] => Cmult[34]) = 25935; // Bmult21 -> Cmult34
    (Amult[21] => Cmult[35]) = 25898; // Amult21 -> Cmult35
    (Bmult[21] => Cmult[35]) = 26050; // Bmult21 -> Cmult35
    (Amult[21] => Cmult[36]) = 26243; // Amult21 -> Cmult36
    (Bmult[21] => Cmult[36]) = 26558; // Bmult21 -> Cmult36
    (Amult[21] => Cmult[37]) = 26451; // Amult21 -> Cmult37
    (Bmult[21] => Cmult[37]) = 24481; // Bmult21 -> Cmult37
    (Amult[21] => Cmult[38]) = 26693; // Amult21 -> Cmult38
    (Bmult[21] => Cmult[38]) = 24843; // Bmult21 -> Cmult38
    (Amult[21] => Cmult[39]) = 26936; // Amult21 -> Cmult39
    (Bmult[21] => Cmult[39]) = 25144; // Bmult21 -> Cmult39
    (Amult[21] => Cmult[40]) = 27284; // Amult21 -> Cmult40
    (Bmult[21] => Cmult[40]) = 25354; // Bmult21 -> Cmult40
    (Amult[21] => Cmult[41]) = 27386; // Amult21 -> Cmult41
    (Bmult[21] => Cmult[41]) = 25588; // Bmult21 -> Cmult41
    (Amult[21] => Cmult[42]) = 26933; // Amult21 -> Cmult42
    (Bmult[21] => Cmult[42]) = 25041; // Bmult21 -> Cmult42
    (Amult[21] => Cmult[43]) = 27508; // Amult21 -> Cmult43
    (Bmult[21] => Cmult[43]) = 25731; // Bmult21 -> Cmult43
    (Amult[21] => Cmult[44]) = 28160; // Amult21 -> Cmult44
    (Bmult[21] => Cmult[44]) = 26173; // Bmult21 -> Cmult44
    (Amult[21] => Cmult[45]) = 28124; // Amult21 -> Cmult45
    (Bmult[21] => Cmult[45]) = 26347; // Bmult21 -> Cmult45
    (Amult[21] => Cmult[46]) = 27644; // Amult21 -> Cmult46
    (Bmult[21] => Cmult[46]) = 25736; // Bmult21 -> Cmult46
    (Amult[21] => Cmult[47]) = 27457; // Amult21 -> Cmult47
    (Bmult[21] => Cmult[47]) = 25652; // Bmult21 -> Cmult47
    (Amult[21] => Cmult[48]) = 28523; // Amult21 -> Cmult48
    (Bmult[21] => Cmult[48]) = 26658; // Bmult21 -> Cmult48
    (Amult[21] => Cmult[49]) = 28317; // Amult21 -> Cmult49
    (Bmult[21] => Cmult[49]) = 26458; // Bmult21 -> Cmult49
    (Amult[21] => Cmult[50]) = 29055; // Amult21 -> Cmult50
    (Bmult[21] => Cmult[50]) = 27280; // Bmult21 -> Cmult50
    (Amult[21] => Cmult[51]) = 29406; // Amult21 -> Cmult51
    (Bmult[21] => Cmult[51]) = 27472; // Bmult21 -> Cmult51
    (Amult[21] => Cmult[52]) = 29892; // Amult21 -> Cmult52
    (Bmult[21] => Cmult[52]) = 28126; // Bmult21 -> Cmult52
    (Amult[21] => Cmult[53]) = 30357; // Amult21 -> Cmult53
    (Bmult[21] => Cmult[53]) = 28383; // Bmult21 -> Cmult53
    (Amult[21] => Cmult[54]) = 30636; // Amult21 -> Cmult54
    (Bmult[21] => Cmult[54]) = 28783; // Bmult21 -> Cmult54
    (Amult[21] => Cmult[55]) = 30894; // Amult21 -> Cmult55
    (Bmult[21] => Cmult[55]) = 28920; // Bmult21 -> Cmult55
    (Amult[21] => Cmult[56]) = 31230; // Amult21 -> Cmult56
    (Bmult[21] => Cmult[56]) = 29464; // Bmult21 -> Cmult56
    (Amult[21] => Cmult[57]) = 31612; // Amult21 -> Cmult57
    (Bmult[21] => Cmult[57]) = 29750; // Bmult21 -> Cmult57
    (Amult[21] => Cmult[58]) = 31976; // Amult21 -> Cmult58
    (Bmult[21] => Cmult[58]) = 30208; // Bmult21 -> Cmult58
    (Amult[21] => Cmult[59]) = 32146; // Amult21 -> Cmult59
    (Bmult[21] => Cmult[59]) = 30276; // Bmult21 -> Cmult59
    (Amult[21] => Cmult[60]) = 32604; // Amult21 -> Cmult60
    (Bmult[21] => Cmult[60]) = 30839; // Bmult21 -> Cmult60
    (Amult[21] => Cmult[61]) = 32822; // Amult21 -> Cmult61
    (Bmult[21] => Cmult[61]) = 30847; // Bmult21 -> Cmult61
    (Amult[21] => Cmult[62]) = 33401; // Amult21 -> Cmult62
    (Bmult[21] => Cmult[62]) = 31633; // Bmult21 -> Cmult62
    (Amult[21] => Cmult[63]) = 34496; // Amult21 -> Cmult63
    (Bmult[21] => Cmult[63]) = 32727; // Bmult21 -> Cmult63
    (Amult[22] => Cmult[2]) = 6007; // Amult22 -> Cmult2
    (Bmult[22] => Cmult[2]) = 6032; // Bmult22 -> Cmult2
    (Amult[22] => Cmult[3]) = 6209; // Amult22 -> Cmult3
    (Bmult[22] => Cmult[3]) = 6377; // Bmult22 -> Cmult3
    (Amult[22] => Cmult[4]) = 6895; // Amult22 -> Cmult4
    (Bmult[22] => Cmult[4]) = 6848; // Bmult22 -> Cmult4
    (Amult[22] => Cmult[5]) = 7784; // Amult22 -> Cmult5
    (Bmult[22] => Cmult[5]) = 7568; // Bmult22 -> Cmult5
    (Amult[22] => Cmult[6]) = 8701; // Amult22 -> Cmult6
    (Bmult[22] => Cmult[6]) = 8023; // Bmult22 -> Cmult6
    (Amult[22] => Cmult[7]) = 8892; // Amult22 -> Cmult7
    (Bmult[22] => Cmult[7]) = 8770; // Bmult22 -> Cmult7
    (Amult[22] => Cmult[8]) = 10272; // Amult22 -> Cmult8
    (Bmult[22] => Cmult[8]) = 9515; // Bmult22 -> Cmult8
    (Amult[22] => Cmult[9]) = 10730; // Amult22 -> Cmult9
    (Bmult[22] => Cmult[9]) = 10069; // Bmult22 -> Cmult9
    (Amult[22] => Cmult[10]) = 11045; // Amult22 -> Cmult10
    (Bmult[22] => Cmult[10]) = 10591; // Bmult22 -> Cmult10
    (Amult[22] => Cmult[11]) = 11666; // Amult22 -> Cmult11
    (Bmult[22] => Cmult[11]) = 11080; // Bmult22 -> Cmult11
    (Amult[22] => Cmult[12]) = 12256; // Amult22 -> Cmult12
    (Bmult[22] => Cmult[12]) = 11409; // Bmult22 -> Cmult12
    (Amult[22] => Cmult[13]) = 12759; // Amult22 -> Cmult13
    (Bmult[22] => Cmult[13]) = 12074; // Bmult22 -> Cmult13
    (Amult[22] => Cmult[14]) = 13409; // Amult22 -> Cmult14
    (Bmult[22] => Cmult[14]) = 12600; // Bmult22 -> Cmult14
    (Amult[22] => Cmult[15]) = 15103; // Amult22 -> Cmult15
    (Bmult[22] => Cmult[15]) = 13797; // Bmult22 -> Cmult15
    (Amult[22] => Cmult[16]) = 15003; // Amult22 -> Cmult16
    (Bmult[22] => Cmult[16]) = 13970; // Bmult22 -> Cmult16
    (Amult[22] => Cmult[17]) = 15095; // Amult22 -> Cmult17
    (Bmult[22] => Cmult[17]) = 14352; // Bmult22 -> Cmult17
    (Amult[22] => Cmult[18]) = 15429; // Amult22 -> Cmult18
    (Bmult[22] => Cmult[18]) = 13959; // Bmult22 -> Cmult18
    (Amult[22] => Cmult[19]) = 15755; // Amult22 -> Cmult19
    (Bmult[22] => Cmult[19]) = 14200; // Bmult22 -> Cmult19
    (Amult[22] => Cmult[20]) = 16197; // Amult22 -> Cmult20
    (Bmult[22] => Cmult[20]) = 14544; // Bmult22 -> Cmult20
    (Amult[22] => Cmult[21]) = 16498; // Amult22 -> Cmult21
    (Bmult[22] => Cmult[21]) = 14730; // Bmult22 -> Cmult21
    (Amult[22] => Cmult[22]) = 16797; // Amult22 -> Cmult22
    (Bmult[22] => Cmult[22]) = 18229; // Bmult22 -> Cmult22
    (Amult[22] => Cmult[23]) = 16966; // Amult22 -> Cmult23
    (Bmult[22] => Cmult[23]) = 19303; // Bmult22 -> Cmult23
    (Amult[22] => Cmult[24]) = 16849; // Amult22 -> Cmult24
    (Bmult[22] => Cmult[24]) = 19593; // Bmult22 -> Cmult24
    (Amult[22] => Cmult[25]) = 17105; // Amult22 -> Cmult25
    (Bmult[22] => Cmult[25]) = 20376; // Bmult22 -> Cmult25
    (Amult[22] => Cmult[26]) = 17868; // Amult22 -> Cmult26
    (Bmult[22] => Cmult[26]) = 21418; // Bmult22 -> Cmult26
    (Amult[22] => Cmult[27]) = 17997; // Amult22 -> Cmult27
    (Bmult[22] => Cmult[27]) = 21992; // Bmult22 -> Cmult27
    (Amult[22] => Cmult[28]) = 18261; // Amult22 -> Cmult28
    (Bmult[22] => Cmult[28]) = 22416; // Bmult22 -> Cmult28
    (Amult[22] => Cmult[29]) = 18599; // Amult22 -> Cmult29
    (Bmult[22] => Cmult[29]) = 23194; // Bmult22 -> Cmult29
    (Amult[22] => Cmult[30]) = 19277; // Amult22 -> Cmult30
    (Bmult[22] => Cmult[30]) = 23714; // Bmult22 -> Cmult30
    (Amult[22] => Cmult[31]) = 20084; // Amult22 -> Cmult31
    (Bmult[22] => Cmult[31]) = 25106; // Bmult22 -> Cmult31
    (Amult[22] => Cmult[32]) = 25227; // Amult22 -> Cmult32
    (Bmult[22] => Cmult[32]) = 25434; // Bmult22 -> Cmult32
    (Amult[22] => Cmult[33]) = 25481; // Amult22 -> Cmult33
    (Bmult[22] => Cmult[33]) = 25777; // Bmult22 -> Cmult33
    (Amult[22] => Cmult[34]) = 25723; // Amult22 -> Cmult34
    (Bmult[22] => Cmult[34]) = 26066; // Bmult22 -> Cmult34
    (Amult[22] => Cmult[35]) = 25898; // Amult22 -> Cmult35
    (Bmult[22] => Cmult[35]) = 26296; // Bmult22 -> Cmult35
    (Amult[22] => Cmult[36]) = 26243; // Amult22 -> Cmult36
    (Bmult[22] => Cmult[36]) = 26362; // Bmult22 -> Cmult36
    (Amult[22] => Cmult[37]) = 26451; // Amult22 -> Cmult37
    (Bmult[22] => Cmult[37]) = 26555; // Bmult22 -> Cmult37
    (Amult[22] => Cmult[38]) = 26693; // Amult22 -> Cmult38
    (Bmult[22] => Cmult[38]) = 24843; // Bmult22 -> Cmult38
    (Amult[22] => Cmult[39]) = 26936; // Amult22 -> Cmult39
    (Bmult[22] => Cmult[39]) = 25144; // Bmult22 -> Cmult39
    (Amult[22] => Cmult[40]) = 27284; // Amult22 -> Cmult40
    (Bmult[22] => Cmult[40]) = 25354; // Bmult22 -> Cmult40
    (Amult[22] => Cmult[41]) = 27386; // Amult22 -> Cmult41
    (Bmult[22] => Cmult[41]) = 25588; // Bmult22 -> Cmult41
    (Amult[22] => Cmult[42]) = 26933; // Amult22 -> Cmult42
    (Bmult[22] => Cmult[42]) = 25041; // Bmult22 -> Cmult42
    (Amult[22] => Cmult[43]) = 27508; // Amult22 -> Cmult43
    (Bmult[22] => Cmult[43]) = 25731; // Bmult22 -> Cmult43
    (Amult[22] => Cmult[44]) = 28160; // Amult22 -> Cmult44
    (Bmult[22] => Cmult[44]) = 26173; // Bmult22 -> Cmult44
    (Amult[22] => Cmult[45]) = 28124; // Amult22 -> Cmult45
    (Bmult[22] => Cmult[45]) = 26347; // Bmult22 -> Cmult45
    (Amult[22] => Cmult[46]) = 27644; // Amult22 -> Cmult46
    (Bmult[22] => Cmult[46]) = 25736; // Bmult22 -> Cmult46
    (Amult[22] => Cmult[47]) = 27457; // Amult22 -> Cmult47
    (Bmult[22] => Cmult[47]) = 25652; // Bmult22 -> Cmult47
    (Amult[22] => Cmult[48]) = 28523; // Amult22 -> Cmult48
    (Bmult[22] => Cmult[48]) = 26658; // Bmult22 -> Cmult48
    (Amult[22] => Cmult[49]) = 28317; // Amult22 -> Cmult49
    (Bmult[22] => Cmult[49]) = 26458; // Bmult22 -> Cmult49
    (Amult[22] => Cmult[50]) = 29055; // Amult22 -> Cmult50
    (Bmult[22] => Cmult[50]) = 27280; // Bmult22 -> Cmult50
    (Amult[22] => Cmult[51]) = 29406; // Amult22 -> Cmult51
    (Bmult[22] => Cmult[51]) = 27472; // Bmult22 -> Cmult51
    (Amult[22] => Cmult[52]) = 29892; // Amult22 -> Cmult52
    (Bmult[22] => Cmult[52]) = 28126; // Bmult22 -> Cmult52
    (Amult[22] => Cmult[53]) = 30357; // Amult22 -> Cmult53
    (Bmult[22] => Cmult[53]) = 28383; // Bmult22 -> Cmult53
    (Amult[22] => Cmult[54]) = 30636; // Amult22 -> Cmult54
    (Bmult[22] => Cmult[54]) = 28783; // Bmult22 -> Cmult54
    (Amult[22] => Cmult[55]) = 30894; // Amult22 -> Cmult55
    (Bmult[22] => Cmult[55]) = 28920; // Bmult22 -> Cmult55
    (Amult[22] => Cmult[56]) = 31230; // Amult22 -> Cmult56
    (Bmult[22] => Cmult[56]) = 29464; // Bmult22 -> Cmult56
    (Amult[22] => Cmult[57]) = 31612; // Amult22 -> Cmult57
    (Bmult[22] => Cmult[57]) = 29750; // Bmult22 -> Cmult57
    (Amult[22] => Cmult[58]) = 31976; // Amult22 -> Cmult58
    (Bmult[22] => Cmult[58]) = 30208; // Bmult22 -> Cmult58
    (Amult[22] => Cmult[59]) = 32146; // Amult22 -> Cmult59
    (Bmult[22] => Cmult[59]) = 30276; // Bmult22 -> Cmult59
    (Amult[22] => Cmult[60]) = 32604; // Amult22 -> Cmult60
    (Bmult[22] => Cmult[60]) = 30839; // Bmult22 -> Cmult60
    (Amult[22] => Cmult[61]) = 32822; // Amult22 -> Cmult61
    (Bmult[22] => Cmult[61]) = 30847; // Bmult22 -> Cmult61
    (Amult[22] => Cmult[62]) = 33401; // Amult22 -> Cmult62
    (Bmult[22] => Cmult[62]) = 31633; // Bmult22 -> Cmult62
    (Amult[22] => Cmult[63]) = 34496; // Amult22 -> Cmult63
    (Bmult[22] => Cmult[63]) = 32727; // Bmult22 -> Cmult63
    (Amult[23] => Cmult[2]) = 6007; // Amult23 -> Cmult2
    (Bmult[23] => Cmult[2]) = 6032; // Bmult23 -> Cmult2
    (Amult[23] => Cmult[3]) = 6209; // Amult23 -> Cmult3
    (Bmult[23] => Cmult[3]) = 6377; // Bmult23 -> Cmult3
    (Amult[23] => Cmult[4]) = 6895; // Amult23 -> Cmult4
    (Bmult[23] => Cmult[4]) = 6848; // Bmult23 -> Cmult4
    (Amult[23] => Cmult[5]) = 7784; // Amult23 -> Cmult5
    (Bmult[23] => Cmult[5]) = 7568; // Bmult23 -> Cmult5
    (Amult[23] => Cmult[6]) = 8701; // Amult23 -> Cmult6
    (Bmult[23] => Cmult[6]) = 8023; // Bmult23 -> Cmult6
    (Amult[23] => Cmult[7]) = 8892; // Amult23 -> Cmult7
    (Bmult[23] => Cmult[7]) = 8770; // Bmult23 -> Cmult7
    (Amult[23] => Cmult[8]) = 10272; // Amult23 -> Cmult8
    (Bmult[23] => Cmult[8]) = 9515; // Bmult23 -> Cmult8
    (Amult[23] => Cmult[9]) = 10730; // Amult23 -> Cmult9
    (Bmult[23] => Cmult[9]) = 10069; // Bmult23 -> Cmult9
    (Amult[23] => Cmult[10]) = 11045; // Amult23 -> Cmult10
    (Bmult[23] => Cmult[10]) = 10591; // Bmult23 -> Cmult10
    (Amult[23] => Cmult[11]) = 11666; // Amult23 -> Cmult11
    (Bmult[23] => Cmult[11]) = 11080; // Bmult23 -> Cmult11
    (Amult[23] => Cmult[12]) = 12256; // Amult23 -> Cmult12
    (Bmult[23] => Cmult[12]) = 11409; // Bmult23 -> Cmult12
    (Amult[23] => Cmult[13]) = 12759; // Amult23 -> Cmult13
    (Bmult[23] => Cmult[13]) = 12074; // Bmult23 -> Cmult13
    (Amult[23] => Cmult[14]) = 13409; // Amult23 -> Cmult14
    (Bmult[23] => Cmult[14]) = 12600; // Bmult23 -> Cmult14
    (Amult[23] => Cmult[15]) = 15103; // Amult23 -> Cmult15
    (Bmult[23] => Cmult[15]) = 13797; // Bmult23 -> Cmult15
    (Amult[23] => Cmult[16]) = 15003; // Amult23 -> Cmult16
    (Bmult[23] => Cmult[16]) = 13970; // Bmult23 -> Cmult16
    (Amult[23] => Cmult[17]) = 15095; // Amult23 -> Cmult17
    (Bmult[23] => Cmult[17]) = 14352; // Bmult23 -> Cmult17
    (Amult[23] => Cmult[18]) = 15429; // Amult23 -> Cmult18
    (Bmult[23] => Cmult[18]) = 13959; // Bmult23 -> Cmult18
    (Amult[23] => Cmult[19]) = 15755; // Amult23 -> Cmult19
    (Bmult[23] => Cmult[19]) = 14200; // Bmult23 -> Cmult19
    (Amult[23] => Cmult[20]) = 16197; // Amult23 -> Cmult20
    (Bmult[23] => Cmult[20]) = 14544; // Bmult23 -> Cmult20
    (Amult[23] => Cmult[21]) = 16498; // Amult23 -> Cmult21
    (Bmult[23] => Cmult[21]) = 14730; // Bmult23 -> Cmult21
    (Amult[23] => Cmult[22]) = 16797; // Amult23 -> Cmult22
    (Bmult[23] => Cmult[22]) = 15133; // Bmult23 -> Cmult22
    (Amult[23] => Cmult[23]) = 16966; // Amult23 -> Cmult23
    (Bmult[23] => Cmult[23]) = 19506; // Bmult23 -> Cmult23
    (Amult[23] => Cmult[24]) = 16849; // Amult23 -> Cmult24
    (Bmult[23] => Cmult[24]) = 19803; // Bmult23 -> Cmult24
    (Amult[23] => Cmult[25]) = 17105; // Amult23 -> Cmult25
    (Bmult[23] => Cmult[25]) = 20596; // Bmult23 -> Cmult25
    (Amult[23] => Cmult[26]) = 17868; // Amult23 -> Cmult26
    (Bmult[23] => Cmult[26]) = 21638; // Bmult23 -> Cmult26
    (Amult[23] => Cmult[27]) = 17997; // Amult23 -> Cmult27
    (Bmult[23] => Cmult[27]) = 22212; // Bmult23 -> Cmult27
    (Amult[23] => Cmult[28]) = 18261; // Amult23 -> Cmult28
    (Bmult[23] => Cmult[28]) = 22636; // Bmult23 -> Cmult28
    (Amult[23] => Cmult[29]) = 18599; // Amult23 -> Cmult29
    (Bmult[23] => Cmult[29]) = 23415; // Bmult23 -> Cmult29
    (Amult[23] => Cmult[30]) = 19277; // Amult23 -> Cmult30
    (Bmult[23] => Cmult[30]) = 23935; // Bmult23 -> Cmult30
    (Amult[23] => Cmult[31]) = 20084; // Amult23 -> Cmult31
    (Bmult[23] => Cmult[31]) = 25326; // Bmult23 -> Cmult31
    (Amult[23] => Cmult[32]) = 25227; // Amult23 -> Cmult32
    (Bmult[23] => Cmult[32]) = 25654; // Bmult23 -> Cmult32
    (Amult[23] => Cmult[33]) = 25481; // Amult23 -> Cmult33
    (Bmult[23] => Cmult[33]) = 25997; // Bmult23 -> Cmult33
    (Amult[23] => Cmult[34]) = 25723; // Amult23 -> Cmult34
    (Bmult[23] => Cmult[34]) = 26286; // Bmult23 -> Cmult34
    (Amult[23] => Cmult[35]) = 25898; // Amult23 -> Cmult35
    (Bmult[23] => Cmult[35]) = 26516; // Bmult23 -> Cmult35
    (Amult[23] => Cmult[36]) = 26243; // Amult23 -> Cmult36
    (Bmult[23] => Cmult[36]) = 26583; // Bmult23 -> Cmult36
    (Amult[23] => Cmult[37]) = 26451; // Amult23 -> Cmult37
    (Bmult[23] => Cmult[37]) = 26775; // Bmult23 -> Cmult37
    (Amult[23] => Cmult[38]) = 26693; // Amult23 -> Cmult38
    (Bmult[23] => Cmult[38]) = 26845; // Bmult23 -> Cmult38
    (Amult[23] => Cmult[39]) = 26936; // Amult23 -> Cmult39
    (Bmult[23] => Cmult[39]) = 25144; // Bmult23 -> Cmult39
    (Amult[23] => Cmult[40]) = 27284; // Amult23 -> Cmult40
    (Bmult[23] => Cmult[40]) = 25354; // Bmult23 -> Cmult40
    (Amult[23] => Cmult[41]) = 27386; // Amult23 -> Cmult41
    (Bmult[23] => Cmult[41]) = 25588; // Bmult23 -> Cmult41
    (Amult[23] => Cmult[42]) = 26933; // Amult23 -> Cmult42
    (Bmult[23] => Cmult[42]) = 25041; // Bmult23 -> Cmult42
    (Amult[23] => Cmult[43]) = 27508; // Amult23 -> Cmult43
    (Bmult[23] => Cmult[43]) = 25731; // Bmult23 -> Cmult43
    (Amult[23] => Cmult[44]) = 28160; // Amult23 -> Cmult44
    (Bmult[23] => Cmult[44]) = 26173; // Bmult23 -> Cmult44
    (Amult[23] => Cmult[45]) = 28124; // Amult23 -> Cmult45
    (Bmult[23] => Cmult[45]) = 26347; // Bmult23 -> Cmult45
    (Amult[23] => Cmult[46]) = 27644; // Amult23 -> Cmult46
    (Bmult[23] => Cmult[46]) = 25736; // Bmult23 -> Cmult46
    (Amult[23] => Cmult[47]) = 27457; // Amult23 -> Cmult47
    (Bmult[23] => Cmult[47]) = 25652; // Bmult23 -> Cmult47
    (Amult[23] => Cmult[48]) = 28523; // Amult23 -> Cmult48
    (Bmult[23] => Cmult[48]) = 26658; // Bmult23 -> Cmult48
    (Amult[23] => Cmult[49]) = 28317; // Amult23 -> Cmult49
    (Bmult[23] => Cmult[49]) = 26458; // Bmult23 -> Cmult49
    (Amult[23] => Cmult[50]) = 29055; // Amult23 -> Cmult50
    (Bmult[23] => Cmult[50]) = 27280; // Bmult23 -> Cmult50
    (Amult[23] => Cmult[51]) = 29406; // Amult23 -> Cmult51
    (Bmult[23] => Cmult[51]) = 27472; // Bmult23 -> Cmult51
    (Amult[23] => Cmult[52]) = 29892; // Amult23 -> Cmult52
    (Bmult[23] => Cmult[52]) = 28126; // Bmult23 -> Cmult52
    (Amult[23] => Cmult[53]) = 30357; // Amult23 -> Cmult53
    (Bmult[23] => Cmult[53]) = 28383; // Bmult23 -> Cmult53
    (Amult[23] => Cmult[54]) = 30636; // Amult23 -> Cmult54
    (Bmult[23] => Cmult[54]) = 28783; // Bmult23 -> Cmult54
    (Amult[23] => Cmult[55]) = 30894; // Amult23 -> Cmult55
    (Bmult[23] => Cmult[55]) = 28920; // Bmult23 -> Cmult55
    (Amult[23] => Cmult[56]) = 31230; // Amult23 -> Cmult56
    (Bmult[23] => Cmult[56]) = 29464; // Bmult23 -> Cmult56
    (Amult[23] => Cmult[57]) = 31612; // Amult23 -> Cmult57
    (Bmult[23] => Cmult[57]) = 29750; // Bmult23 -> Cmult57
    (Amult[23] => Cmult[58]) = 31976; // Amult23 -> Cmult58
    (Bmult[23] => Cmult[58]) = 30208; // Bmult23 -> Cmult58
    (Amult[23] => Cmult[59]) = 32146; // Amult23 -> Cmult59
    (Bmult[23] => Cmult[59]) = 30276; // Bmult23 -> Cmult59
    (Amult[23] => Cmult[60]) = 32604; // Amult23 -> Cmult60
    (Bmult[23] => Cmult[60]) = 30839; // Bmult23 -> Cmult60
    (Amult[23] => Cmult[61]) = 32822; // Amult23 -> Cmult61
    (Bmult[23] => Cmult[61]) = 30847; // Bmult23 -> Cmult61
    (Amult[23] => Cmult[62]) = 33401; // Amult23 -> Cmult62
    (Bmult[23] => Cmult[62]) = 31633; // Bmult23 -> Cmult62
    (Amult[23] => Cmult[63]) = 34496; // Amult23 -> Cmult63
    (Bmult[23] => Cmult[63]) = 32727; // Bmult23 -> Cmult63
    (Amult[24] => Cmult[2]) = 6007; // Amult24 -> Cmult2
    (Bmult[24] => Cmult[2]) = 6032; // Bmult24 -> Cmult2
    (Amult[24] => Cmult[3]) = 6209; // Amult24 -> Cmult3
    (Bmult[24] => Cmult[3]) = 6377; // Bmult24 -> Cmult3
    (Amult[24] => Cmult[4]) = 6895; // Amult24 -> Cmult4
    (Bmult[24] => Cmult[4]) = 6848; // Bmult24 -> Cmult4
    (Amult[24] => Cmult[5]) = 7784; // Amult24 -> Cmult5
    (Bmult[24] => Cmult[5]) = 7568; // Bmult24 -> Cmult5
    (Amult[24] => Cmult[6]) = 8701; // Amult24 -> Cmult6
    (Bmult[24] => Cmult[6]) = 8023; // Bmult24 -> Cmult6
    (Amult[24] => Cmult[7]) = 8892; // Amult24 -> Cmult7
    (Bmult[24] => Cmult[7]) = 8770; // Bmult24 -> Cmult7
    (Amult[24] => Cmult[8]) = 10272; // Amult24 -> Cmult8
    (Bmult[24] => Cmult[8]) = 9515; // Bmult24 -> Cmult8
    (Amult[24] => Cmult[9]) = 10730; // Amult24 -> Cmult9
    (Bmult[24] => Cmult[9]) = 10069; // Bmult24 -> Cmult9
    (Amult[24] => Cmult[10]) = 11045; // Amult24 -> Cmult10
    (Bmult[24] => Cmult[10]) = 10591; // Bmult24 -> Cmult10
    (Amult[24] => Cmult[11]) = 11666; // Amult24 -> Cmult11
    (Bmult[24] => Cmult[11]) = 11080; // Bmult24 -> Cmult11
    (Amult[24] => Cmult[12]) = 12256; // Amult24 -> Cmult12
    (Bmult[24] => Cmult[12]) = 11409; // Bmult24 -> Cmult12
    (Amult[24] => Cmult[13]) = 12759; // Amult24 -> Cmult13
    (Bmult[24] => Cmult[13]) = 12074; // Bmult24 -> Cmult13
    (Amult[24] => Cmult[14]) = 13409; // Amult24 -> Cmult14
    (Bmult[24] => Cmult[14]) = 12600; // Bmult24 -> Cmult14
    (Amult[24] => Cmult[15]) = 15103; // Amult24 -> Cmult15
    (Bmult[24] => Cmult[15]) = 13797; // Bmult24 -> Cmult15
    (Amult[24] => Cmult[16]) = 15003; // Amult24 -> Cmult16
    (Bmult[24] => Cmult[16]) = 13970; // Bmult24 -> Cmult16
    (Amult[24] => Cmult[17]) = 15095; // Amult24 -> Cmult17
    (Bmult[24] => Cmult[17]) = 14352; // Bmult24 -> Cmult17
    (Amult[24] => Cmult[18]) = 15429; // Amult24 -> Cmult18
    (Bmult[24] => Cmult[18]) = 13959; // Bmult24 -> Cmult18
    (Amult[24] => Cmult[19]) = 15755; // Amult24 -> Cmult19
    (Bmult[24] => Cmult[19]) = 14200; // Bmult24 -> Cmult19
    (Amult[24] => Cmult[20]) = 16197; // Amult24 -> Cmult20
    (Bmult[24] => Cmult[20]) = 14544; // Bmult24 -> Cmult20
    (Amult[24] => Cmult[21]) = 16498; // Amult24 -> Cmult21
    (Bmult[24] => Cmult[21]) = 14730; // Bmult24 -> Cmult21
    (Amult[24] => Cmult[22]) = 16797; // Amult24 -> Cmult22
    (Bmult[24] => Cmult[22]) = 15133; // Bmult24 -> Cmult22
    (Amult[24] => Cmult[23]) = 16966; // Amult24 -> Cmult23
    (Bmult[24] => Cmult[23]) = 15419; // Bmult24 -> Cmult23
    (Amult[24] => Cmult[24]) = 16849; // Amult24 -> Cmult24
    (Bmult[24] => Cmult[24]) = 19956; // Bmult24 -> Cmult24
    (Amult[24] => Cmult[25]) = 17105; // Amult24 -> Cmult25
    (Bmult[24] => Cmult[25]) = 20640; // Bmult24 -> Cmult25
    (Amult[24] => Cmult[26]) = 17868; // Amult24 -> Cmult26
    (Bmult[24] => Cmult[26]) = 21215; // Bmult24 -> Cmult26
    (Amult[24] => Cmult[27]) = 17997; // Amult24 -> Cmult27
    (Bmult[24] => Cmult[27]) = 21934; // Bmult24 -> Cmult27
    (Amult[24] => Cmult[28]) = 18261; // Amult24 -> Cmult28
    (Bmult[24] => Cmult[28]) = 22911; // Bmult24 -> Cmult28
    (Amult[24] => Cmult[29]) = 18599; // Amult24 -> Cmult29
    (Bmult[24] => Cmult[29]) = 23706; // Bmult24 -> Cmult29
    (Amult[24] => Cmult[30]) = 19277; // Amult24 -> Cmult30
    (Bmult[24] => Cmult[30]) = 24145; // Bmult24 -> Cmult30
    (Amult[24] => Cmult[31]) = 20084; // Amult24 -> Cmult31
    (Bmult[24] => Cmult[31]) = 25791; // Bmult24 -> Cmult31
    (Amult[24] => Cmult[32]) = 25227; // Amult24 -> Cmult32
    (Bmult[24] => Cmult[32]) = 25939; // Bmult24 -> Cmult32
    (Amult[24] => Cmult[33]) = 25481; // Amult24 -> Cmult33
    (Bmult[24] => Cmult[33]) = 26033; // Bmult24 -> Cmult33
    (Amult[24] => Cmult[34]) = 25723; // Amult24 -> Cmult34
    (Bmult[24] => Cmult[34]) = 26510; // Bmult24 -> Cmult34
    (Amult[24] => Cmult[35]) = 25898; // Amult24 -> Cmult35
    (Bmult[24] => Cmult[35]) = 26626; // Bmult24 -> Cmult35
    (Amult[24] => Cmult[36]) = 26243; // Amult24 -> Cmult36
    (Bmult[24] => Cmult[36]) = 27136; // Bmult24 -> Cmult36
    (Amult[24] => Cmult[37]) = 26451; // Amult24 -> Cmult37
    (Bmult[24] => Cmult[37]) = 27343; // Bmult24 -> Cmult37
    (Amult[24] => Cmult[38]) = 26693; // Amult24 -> Cmult38
    (Bmult[24] => Cmult[38]) = 27610; // Bmult24 -> Cmult38
    (Amult[24] => Cmult[39]) = 26936; // Amult24 -> Cmult39
    (Bmult[24] => Cmult[39]) = 27911; // Bmult24 -> Cmult39
    (Amult[24] => Cmult[40]) = 27284; // Amult24 -> Cmult40
    (Bmult[24] => Cmult[40]) = 25354; // Bmult24 -> Cmult40
    (Amult[24] => Cmult[41]) = 27386; // Amult24 -> Cmult41
    (Bmult[24] => Cmult[41]) = 25588; // Bmult24 -> Cmult41
    (Amult[24] => Cmult[42]) = 26933; // Amult24 -> Cmult42
    (Bmult[24] => Cmult[42]) = 25041; // Bmult24 -> Cmult42
    (Amult[24] => Cmult[43]) = 27508; // Amult24 -> Cmult43
    (Bmult[24] => Cmult[43]) = 25731; // Bmult24 -> Cmult43
    (Amult[24] => Cmult[44]) = 28160; // Amult24 -> Cmult44
    (Bmult[24] => Cmult[44]) = 26173; // Bmult24 -> Cmult44
    (Amult[24] => Cmult[45]) = 28124; // Amult24 -> Cmult45
    (Bmult[24] => Cmult[45]) = 26347; // Bmult24 -> Cmult45
    (Amult[24] => Cmult[46]) = 27644; // Amult24 -> Cmult46
    (Bmult[24] => Cmult[46]) = 25736; // Bmult24 -> Cmult46
    (Amult[24] => Cmult[47]) = 27457; // Amult24 -> Cmult47
    (Bmult[24] => Cmult[47]) = 25652; // Bmult24 -> Cmult47
    (Amult[24] => Cmult[48]) = 28523; // Amult24 -> Cmult48
    (Bmult[24] => Cmult[48]) = 26658; // Bmult24 -> Cmult48
    (Amult[24] => Cmult[49]) = 28317; // Amult24 -> Cmult49
    (Bmult[24] => Cmult[49]) = 26458; // Bmult24 -> Cmult49
    (Amult[24] => Cmult[50]) = 29055; // Amult24 -> Cmult50
    (Bmult[24] => Cmult[50]) = 27280; // Bmult24 -> Cmult50
    (Amult[24] => Cmult[51]) = 29406; // Amult24 -> Cmult51
    (Bmult[24] => Cmult[51]) = 27472; // Bmult24 -> Cmult51
    (Amult[24] => Cmult[52]) = 29892; // Amult24 -> Cmult52
    (Bmult[24] => Cmult[52]) = 28126; // Bmult24 -> Cmult52
    (Amult[24] => Cmult[53]) = 30357; // Amult24 -> Cmult53
    (Bmult[24] => Cmult[53]) = 28383; // Bmult24 -> Cmult53
    (Amult[24] => Cmult[54]) = 30636; // Amult24 -> Cmult54
    (Bmult[24] => Cmult[54]) = 28783; // Bmult24 -> Cmult54
    (Amult[24] => Cmult[55]) = 30894; // Amult24 -> Cmult55
    (Bmult[24] => Cmult[55]) = 28920; // Bmult24 -> Cmult55
    (Amult[24] => Cmult[56]) = 31230; // Amult24 -> Cmult56
    (Bmult[24] => Cmult[56]) = 29464; // Bmult24 -> Cmult56
    (Amult[24] => Cmult[57]) = 31612; // Amult24 -> Cmult57
    (Bmult[24] => Cmult[57]) = 29750; // Bmult24 -> Cmult57
    (Amult[24] => Cmult[58]) = 31976; // Amult24 -> Cmult58
    (Bmult[24] => Cmult[58]) = 30208; // Bmult24 -> Cmult58
    (Amult[24] => Cmult[59]) = 32146; // Amult24 -> Cmult59
    (Bmult[24] => Cmult[59]) = 30276; // Bmult24 -> Cmult59
    (Amult[24] => Cmult[60]) = 32604; // Amult24 -> Cmult60
    (Bmult[24] => Cmult[60]) = 30839; // Bmult24 -> Cmult60
    (Amult[24] => Cmult[61]) = 32822; // Amult24 -> Cmult61
    (Bmult[24] => Cmult[61]) = 30847; // Bmult24 -> Cmult61
    (Amult[24] => Cmult[62]) = 33401; // Amult24 -> Cmult62
    (Bmult[24] => Cmult[62]) = 31633; // Bmult24 -> Cmult62
    (Amult[24] => Cmult[63]) = 34496; // Amult24 -> Cmult63
    (Bmult[24] => Cmult[63]) = 32727; // Bmult24 -> Cmult63
    (Amult[25] => Cmult[2]) = 6007; // Amult25 -> Cmult2
    (Bmult[25] => Cmult[2]) = 6032; // Bmult25 -> Cmult2
    (Amult[25] => Cmult[3]) = 6209; // Amult25 -> Cmult3
    (Bmult[25] => Cmult[3]) = 6377; // Bmult25 -> Cmult3
    (Amult[25] => Cmult[4]) = 6895; // Amult25 -> Cmult4
    (Bmult[25] => Cmult[4]) = 6848; // Bmult25 -> Cmult4
    (Amult[25] => Cmult[5]) = 7784; // Amult25 -> Cmult5
    (Bmult[25] => Cmult[5]) = 7568; // Bmult25 -> Cmult5
    (Amult[25] => Cmult[6]) = 8701; // Amult25 -> Cmult6
    (Bmult[25] => Cmult[6]) = 8023; // Bmult25 -> Cmult6
    (Amult[25] => Cmult[7]) = 8892; // Amult25 -> Cmult7
    (Bmult[25] => Cmult[7]) = 8770; // Bmult25 -> Cmult7
    (Amult[25] => Cmult[8]) = 10272; // Amult25 -> Cmult8
    (Bmult[25] => Cmult[8]) = 9515; // Bmult25 -> Cmult8
    (Amult[25] => Cmult[9]) = 10730; // Amult25 -> Cmult9
    (Bmult[25] => Cmult[9]) = 10069; // Bmult25 -> Cmult9
    (Amult[25] => Cmult[10]) = 11045; // Amult25 -> Cmult10
    (Bmult[25] => Cmult[10]) = 10591; // Bmult25 -> Cmult10
    (Amult[25] => Cmult[11]) = 11666; // Amult25 -> Cmult11
    (Bmult[25] => Cmult[11]) = 11080; // Bmult25 -> Cmult11
    (Amult[25] => Cmult[12]) = 12256; // Amult25 -> Cmult12
    (Bmult[25] => Cmult[12]) = 11409; // Bmult25 -> Cmult12
    (Amult[25] => Cmult[13]) = 12759; // Amult25 -> Cmult13
    (Bmult[25] => Cmult[13]) = 12074; // Bmult25 -> Cmult13
    (Amult[25] => Cmult[14]) = 13409; // Amult25 -> Cmult14
    (Bmult[25] => Cmult[14]) = 12600; // Bmult25 -> Cmult14
    (Amult[25] => Cmult[15]) = 15103; // Amult25 -> Cmult15
    (Bmult[25] => Cmult[15]) = 13797; // Bmult25 -> Cmult15
    (Amult[25] => Cmult[16]) = 15003; // Amult25 -> Cmult16
    (Bmult[25] => Cmult[16]) = 13970; // Bmult25 -> Cmult16
    (Amult[25] => Cmult[17]) = 15095; // Amult25 -> Cmult17
    (Bmult[25] => Cmult[17]) = 14352; // Bmult25 -> Cmult17
    (Amult[25] => Cmult[18]) = 15429; // Amult25 -> Cmult18
    (Bmult[25] => Cmult[18]) = 13959; // Bmult25 -> Cmult18
    (Amult[25] => Cmult[19]) = 15755; // Amult25 -> Cmult19
    (Bmult[25] => Cmult[19]) = 14200; // Bmult25 -> Cmult19
    (Amult[25] => Cmult[20]) = 16197; // Amult25 -> Cmult20
    (Bmult[25] => Cmult[20]) = 14544; // Bmult25 -> Cmult20
    (Amult[25] => Cmult[21]) = 16498; // Amult25 -> Cmult21
    (Bmult[25] => Cmult[21]) = 14730; // Bmult25 -> Cmult21
    (Amult[25] => Cmult[22]) = 16797; // Amult25 -> Cmult22
    (Bmult[25] => Cmult[22]) = 15133; // Bmult25 -> Cmult22
    (Amult[25] => Cmult[23]) = 16966; // Amult25 -> Cmult23
    (Bmult[25] => Cmult[23]) = 15419; // Bmult25 -> Cmult23
    (Amult[25] => Cmult[24]) = 16849; // Amult25 -> Cmult24
    (Bmult[25] => Cmult[24]) = 15826; // Bmult25 -> Cmult24
    (Amult[25] => Cmult[25]) = 17105; // Amult25 -> Cmult25
    (Bmult[25] => Cmult[25]) = 20318; // Bmult25 -> Cmult25
    (Amult[25] => Cmult[26]) = 17868; // Amult25 -> Cmult26
    (Bmult[25] => Cmult[26]) = 21315; // Bmult25 -> Cmult26
    (Amult[25] => Cmult[27]) = 17997; // Amult25 -> Cmult27
    (Bmult[25] => Cmult[27]) = 21836; // Bmult25 -> Cmult27
    (Amult[25] => Cmult[28]) = 18261; // Amult25 -> Cmult28
    (Bmult[25] => Cmult[28]) = 22617; // Bmult25 -> Cmult28
    (Amult[25] => Cmult[29]) = 18599; // Amult25 -> Cmult29
    (Bmult[25] => Cmult[29]) = 23347; // Bmult25 -> Cmult29
    (Amult[25] => Cmult[30]) = 19277; // Amult25 -> Cmult30
    (Bmult[25] => Cmult[30]) = 23851; // Bmult25 -> Cmult30
    (Amult[25] => Cmult[31]) = 20084; // Amult25 -> Cmult31
    (Bmult[25] => Cmult[31]) = 25295; // Bmult25 -> Cmult31
    (Amult[25] => Cmult[32]) = 25227; // Amult25 -> Cmult32
    (Bmult[25] => Cmult[32]) = 25489; // Bmult25 -> Cmult32
    (Amult[25] => Cmult[33]) = 25481; // Amult25 -> Cmult33
    (Bmult[25] => Cmult[33]) = 25726; // Bmult25 -> Cmult33
    (Amult[25] => Cmult[34]) = 25723; // Amult25 -> Cmult34
    (Bmult[25] => Cmult[34]) = 26216; // Bmult25 -> Cmult34
    (Amult[25] => Cmult[35]) = 25898; // Amult25 -> Cmult35
    (Bmult[25] => Cmult[35]) = 26332; // Bmult25 -> Cmult35
    (Amult[25] => Cmult[36]) = 26243; // Amult25 -> Cmult36
    (Bmult[25] => Cmult[36]) = 26839; // Bmult25 -> Cmult36
    (Amult[25] => Cmult[37]) = 26451; // Amult25 -> Cmult37
    (Bmult[25] => Cmult[37]) = 26880; // Bmult25 -> Cmult37
    (Amult[25] => Cmult[38]) = 26693; // Amult25 -> Cmult38
    (Bmult[25] => Cmult[38]) = 27316; // Bmult25 -> Cmult38
    (Amult[25] => Cmult[39]) = 26936; // Amult25 -> Cmult39
    (Bmult[25] => Cmult[39]) = 27618; // Bmult25 -> Cmult39
    (Amult[25] => Cmult[40]) = 27284; // Amult25 -> Cmult40
    (Bmult[25] => Cmult[40]) = 27822; // Bmult25 -> Cmult40
    (Amult[25] => Cmult[41]) = 27386; // Amult25 -> Cmult41
    (Bmult[25] => Cmult[41]) = 25588; // Bmult25 -> Cmult41
    (Amult[25] => Cmult[42]) = 26933; // Amult25 -> Cmult42
    (Bmult[25] => Cmult[42]) = 25041; // Bmult25 -> Cmult42
    (Amult[25] => Cmult[43]) = 27508; // Amult25 -> Cmult43
    (Bmult[25] => Cmult[43]) = 25731; // Bmult25 -> Cmult43
    (Amult[25] => Cmult[44]) = 28160; // Amult25 -> Cmult44
    (Bmult[25] => Cmult[44]) = 26173; // Bmult25 -> Cmult44
    (Amult[25] => Cmult[45]) = 28124; // Amult25 -> Cmult45
    (Bmult[25] => Cmult[45]) = 26347; // Bmult25 -> Cmult45
    (Amult[25] => Cmult[46]) = 27644; // Amult25 -> Cmult46
    (Bmult[25] => Cmult[46]) = 25736; // Bmult25 -> Cmult46
    (Amult[25] => Cmult[47]) = 27457; // Amult25 -> Cmult47
    (Bmult[25] => Cmult[47]) = 25652; // Bmult25 -> Cmult47
    (Amult[25] => Cmult[48]) = 28523; // Amult25 -> Cmult48
    (Bmult[25] => Cmult[48]) = 26658; // Bmult25 -> Cmult48
    (Amult[25] => Cmult[49]) = 28317; // Amult25 -> Cmult49
    (Bmult[25] => Cmult[49]) = 26458; // Bmult25 -> Cmult49
    (Amult[25] => Cmult[50]) = 29055; // Amult25 -> Cmult50
    (Bmult[25] => Cmult[50]) = 27280; // Bmult25 -> Cmult50
    (Amult[25] => Cmult[51]) = 29406; // Amult25 -> Cmult51
    (Bmult[25] => Cmult[51]) = 27472; // Bmult25 -> Cmult51
    (Amult[25] => Cmult[52]) = 29892; // Amult25 -> Cmult52
    (Bmult[25] => Cmult[52]) = 28126; // Bmult25 -> Cmult52
    (Amult[25] => Cmult[53]) = 30357; // Amult25 -> Cmult53
    (Bmult[25] => Cmult[53]) = 28383; // Bmult25 -> Cmult53
    (Amult[25] => Cmult[54]) = 30636; // Amult25 -> Cmult54
    (Bmult[25] => Cmult[54]) = 28783; // Bmult25 -> Cmult54
    (Amult[25] => Cmult[55]) = 30894; // Amult25 -> Cmult55
    (Bmult[25] => Cmult[55]) = 28920; // Bmult25 -> Cmult55
    (Amult[25] => Cmult[56]) = 31230; // Amult25 -> Cmult56
    (Bmult[25] => Cmult[56]) = 29464; // Bmult25 -> Cmult56
    (Amult[25] => Cmult[57]) = 31612; // Amult25 -> Cmult57
    (Bmult[25] => Cmult[57]) = 29750; // Bmult25 -> Cmult57
    (Amult[25] => Cmult[58]) = 31976; // Amult25 -> Cmult58
    (Bmult[25] => Cmult[58]) = 30208; // Bmult25 -> Cmult58
    (Amult[25] => Cmult[59]) = 32146; // Amult25 -> Cmult59
    (Bmult[25] => Cmult[59]) = 30276; // Bmult25 -> Cmult59
    (Amult[25] => Cmult[60]) = 32604; // Amult25 -> Cmult60
    (Bmult[25] => Cmult[60]) = 30839; // Bmult25 -> Cmult60
    (Amult[25] => Cmult[61]) = 32822; // Amult25 -> Cmult61
    (Bmult[25] => Cmult[61]) = 30847; // Bmult25 -> Cmult61
    (Amult[25] => Cmult[62]) = 33401; // Amult25 -> Cmult62
    (Bmult[25] => Cmult[62]) = 31633; // Bmult25 -> Cmult62
    (Amult[25] => Cmult[63]) = 34496; // Amult25 -> Cmult63
    (Bmult[25] => Cmult[63]) = 32727; // Bmult25 -> Cmult63
    (Amult[26] => Cmult[2]) = 6007; // Amult26 -> Cmult2
    (Bmult[26] => Cmult[2]) = 6032; // Bmult26 -> Cmult2
    (Amult[26] => Cmult[3]) = 6209; // Amult26 -> Cmult3
    (Bmult[26] => Cmult[3]) = 6377; // Bmult26 -> Cmult3
    (Amult[26] => Cmult[4]) = 6895; // Amult26 -> Cmult4
    (Bmult[26] => Cmult[4]) = 6848; // Bmult26 -> Cmult4
    (Amult[26] => Cmult[5]) = 7784; // Amult26 -> Cmult5
    (Bmult[26] => Cmult[5]) = 7568; // Bmult26 -> Cmult5
    (Amult[26] => Cmult[6]) = 8701; // Amult26 -> Cmult6
    (Bmult[26] => Cmult[6]) = 8023; // Bmult26 -> Cmult6
    (Amult[26] => Cmult[7]) = 8892; // Amult26 -> Cmult7
    (Bmult[26] => Cmult[7]) = 8770; // Bmult26 -> Cmult7
    (Amult[26] => Cmult[8]) = 10272; // Amult26 -> Cmult8
    (Bmult[26] => Cmult[8]) = 9515; // Bmult26 -> Cmult8
    (Amult[26] => Cmult[9]) = 10730; // Amult26 -> Cmult9
    (Bmult[26] => Cmult[9]) = 10069; // Bmult26 -> Cmult9
    (Amult[26] => Cmult[10]) = 11045; // Amult26 -> Cmult10
    (Bmult[26] => Cmult[10]) = 10591; // Bmult26 -> Cmult10
    (Amult[26] => Cmult[11]) = 11666; // Amult26 -> Cmult11
    (Bmult[26] => Cmult[11]) = 11080; // Bmult26 -> Cmult11
    (Amult[26] => Cmult[12]) = 12256; // Amult26 -> Cmult12
    (Bmult[26] => Cmult[12]) = 11409; // Bmult26 -> Cmult12
    (Amult[26] => Cmult[13]) = 12759; // Amult26 -> Cmult13
    (Bmult[26] => Cmult[13]) = 12074; // Bmult26 -> Cmult13
    (Amult[26] => Cmult[14]) = 13409; // Amult26 -> Cmult14
    (Bmult[26] => Cmult[14]) = 12600; // Bmult26 -> Cmult14
    (Amult[26] => Cmult[15]) = 15103; // Amult26 -> Cmult15
    (Bmult[26] => Cmult[15]) = 13797; // Bmult26 -> Cmult15
    (Amult[26] => Cmult[16]) = 15003; // Amult26 -> Cmult16
    (Bmult[26] => Cmult[16]) = 13970; // Bmult26 -> Cmult16
    (Amult[26] => Cmult[17]) = 15095; // Amult26 -> Cmult17
    (Bmult[26] => Cmult[17]) = 14352; // Bmult26 -> Cmult17
    (Amult[26] => Cmult[18]) = 15429; // Amult26 -> Cmult18
    (Bmult[26] => Cmult[18]) = 13959; // Bmult26 -> Cmult18
    (Amult[26] => Cmult[19]) = 15755; // Amult26 -> Cmult19
    (Bmult[26] => Cmult[19]) = 14200; // Bmult26 -> Cmult19
    (Amult[26] => Cmult[20]) = 16197; // Amult26 -> Cmult20
    (Bmult[26] => Cmult[20]) = 14544; // Bmult26 -> Cmult20
    (Amult[26] => Cmult[21]) = 16498; // Amult26 -> Cmult21
    (Bmult[26] => Cmult[21]) = 14730; // Bmult26 -> Cmult21
    (Amult[26] => Cmult[22]) = 16797; // Amult26 -> Cmult22
    (Bmult[26] => Cmult[22]) = 15133; // Bmult26 -> Cmult22
    (Amult[26] => Cmult[23]) = 16966; // Amult26 -> Cmult23
    (Bmult[26] => Cmult[23]) = 15419; // Bmult26 -> Cmult23
    (Amult[26] => Cmult[24]) = 16849; // Amult26 -> Cmult24
    (Bmult[26] => Cmult[24]) = 15826; // Bmult26 -> Cmult24
    (Amult[26] => Cmult[25]) = 17105; // Amult26 -> Cmult25
    (Bmult[26] => Cmult[25]) = 16229; // Bmult26 -> Cmult25
    (Amult[26] => Cmult[26]) = 17868; // Amult26 -> Cmult26
    (Bmult[26] => Cmult[26]) = 21096; // Bmult26 -> Cmult26
    (Amult[26] => Cmult[27]) = 17997; // Amult26 -> Cmult27
    (Bmult[26] => Cmult[27]) = 21678; // Bmult26 -> Cmult27
    (Amult[26] => Cmult[28]) = 18261; // Amult26 -> Cmult28
    (Bmult[26] => Cmult[28]) = 22676; // Bmult26 -> Cmult28
    (Amult[26] => Cmult[29]) = 18599; // Amult26 -> Cmult29
    (Bmult[26] => Cmult[29]) = 23476; // Bmult26 -> Cmult29
    (Amult[26] => Cmult[30]) = 19277; // Amult26 -> Cmult30
    (Bmult[26] => Cmult[30]) = 23904; // Bmult26 -> Cmult30
    (Amult[26] => Cmult[31]) = 20084; // Amult26 -> Cmult31
    (Bmult[26] => Cmult[31]) = 25563; // Bmult26 -> Cmult31
    (Amult[26] => Cmult[32]) = 25227; // Amult26 -> Cmult32
    (Bmult[26] => Cmult[32]) = 25712; // Bmult26 -> Cmult32
    (Amult[26] => Cmult[33]) = 25481; // Amult26 -> Cmult33
    (Bmult[26] => Cmult[33]) = 25806; // Bmult26 -> Cmult33
    (Amult[26] => Cmult[34]) = 25723; // Amult26 -> Cmult34
    (Bmult[26] => Cmult[34]) = 26269; // Bmult26 -> Cmult34
    (Amult[26] => Cmult[35]) = 25898; // Amult26 -> Cmult35
    (Bmult[26] => Cmult[35]) = 26385; // Bmult26 -> Cmult35
    (Amult[26] => Cmult[36]) = 26243; // Amult26 -> Cmult36
    (Bmult[26] => Cmult[36]) = 26909; // Bmult26 -> Cmult36
    (Amult[26] => Cmult[37]) = 26451; // Amult26 -> Cmult37
    (Bmult[26] => Cmult[37]) = 27116; // Bmult26 -> Cmult37
    (Amult[26] => Cmult[38]) = 26693; // Amult26 -> Cmult38
    (Bmult[26] => Cmult[38]) = 27370; // Bmult26 -> Cmult38
    (Amult[26] => Cmult[39]) = 26936; // Amult26 -> Cmult39
    (Bmult[26] => Cmult[39]) = 27671; // Bmult26 -> Cmult39
    (Amult[26] => Cmult[40]) = 27284; // Amult26 -> Cmult40
    (Bmult[26] => Cmult[40]) = 27949; // Bmult26 -> Cmult40
    (Amult[26] => Cmult[41]) = 27386; // Amult26 -> Cmult41
    (Bmult[26] => Cmult[41]) = 28121; // Bmult26 -> Cmult41
    (Amult[26] => Cmult[42]) = 26933; // Amult26 -> Cmult42
    (Bmult[26] => Cmult[42]) = 25041; // Bmult26 -> Cmult42
    (Amult[26] => Cmult[43]) = 27508; // Amult26 -> Cmult43
    (Bmult[26] => Cmult[43]) = 25731; // Bmult26 -> Cmult43
    (Amult[26] => Cmult[44]) = 28160; // Amult26 -> Cmult44
    (Bmult[26] => Cmult[44]) = 26173; // Bmult26 -> Cmult44
    (Amult[26] => Cmult[45]) = 28124; // Amult26 -> Cmult45
    (Bmult[26] => Cmult[45]) = 26347; // Bmult26 -> Cmult45
    (Amult[26] => Cmult[46]) = 27644; // Amult26 -> Cmult46
    (Bmult[26] => Cmult[46]) = 25736; // Bmult26 -> Cmult46
    (Amult[26] => Cmult[47]) = 27457; // Amult26 -> Cmult47
    (Bmult[26] => Cmult[47]) = 25652; // Bmult26 -> Cmult47
    (Amult[26] => Cmult[48]) = 28523; // Amult26 -> Cmult48
    (Bmult[26] => Cmult[48]) = 26658; // Bmult26 -> Cmult48
    (Amult[26] => Cmult[49]) = 28317; // Amult26 -> Cmult49
    (Bmult[26] => Cmult[49]) = 26458; // Bmult26 -> Cmult49
    (Amult[26] => Cmult[50]) = 29055; // Amult26 -> Cmult50
    (Bmult[26] => Cmult[50]) = 27280; // Bmult26 -> Cmult50
    (Amult[26] => Cmult[51]) = 29406; // Amult26 -> Cmult51
    (Bmult[26] => Cmult[51]) = 27472; // Bmult26 -> Cmult51
    (Amult[26] => Cmult[52]) = 29892; // Amult26 -> Cmult52
    (Bmult[26] => Cmult[52]) = 28126; // Bmult26 -> Cmult52
    (Amult[26] => Cmult[53]) = 30357; // Amult26 -> Cmult53
    (Bmult[26] => Cmult[53]) = 28383; // Bmult26 -> Cmult53
    (Amult[26] => Cmult[54]) = 30636; // Amult26 -> Cmult54
    (Bmult[26] => Cmult[54]) = 28783; // Bmult26 -> Cmult54
    (Amult[26] => Cmult[55]) = 30894; // Amult26 -> Cmult55
    (Bmult[26] => Cmult[55]) = 28920; // Bmult26 -> Cmult55
    (Amult[26] => Cmult[56]) = 31230; // Amult26 -> Cmult56
    (Bmult[26] => Cmult[56]) = 29464; // Bmult26 -> Cmult56
    (Amult[26] => Cmult[57]) = 31612; // Amult26 -> Cmult57
    (Bmult[26] => Cmult[57]) = 29750; // Bmult26 -> Cmult57
    (Amult[26] => Cmult[58]) = 31976; // Amult26 -> Cmult58
    (Bmult[26] => Cmult[58]) = 30208; // Bmult26 -> Cmult58
    (Amult[26] => Cmult[59]) = 32146; // Amult26 -> Cmult59
    (Bmult[26] => Cmult[59]) = 30276; // Bmult26 -> Cmult59
    (Amult[26] => Cmult[60]) = 32604; // Amult26 -> Cmult60
    (Bmult[26] => Cmult[60]) = 30839; // Bmult26 -> Cmult60
    (Amult[26] => Cmult[61]) = 32822; // Amult26 -> Cmult61
    (Bmult[26] => Cmult[61]) = 30847; // Bmult26 -> Cmult61
    (Amult[26] => Cmult[62]) = 33401; // Amult26 -> Cmult62
    (Bmult[26] => Cmult[62]) = 31633; // Bmult26 -> Cmult62
    (Amult[26] => Cmult[63]) = 34496; // Amult26 -> Cmult63
    (Bmult[26] => Cmult[63]) = 32727; // Bmult26 -> Cmult63
    (Amult[27] => Cmult[2]) = 6007; // Amult27 -> Cmult2
    (Bmult[27] => Cmult[2]) = 6032; // Bmult27 -> Cmult2
    (Amult[27] => Cmult[3]) = 6209; // Amult27 -> Cmult3
    (Bmult[27] => Cmult[3]) = 6377; // Bmult27 -> Cmult3
    (Amult[27] => Cmult[4]) = 6895; // Amult27 -> Cmult4
    (Bmult[27] => Cmult[4]) = 6848; // Bmult27 -> Cmult4
    (Amult[27] => Cmult[5]) = 7784; // Amult27 -> Cmult5
    (Bmult[27] => Cmult[5]) = 7568; // Bmult27 -> Cmult5
    (Amult[27] => Cmult[6]) = 8701; // Amult27 -> Cmult6
    (Bmult[27] => Cmult[6]) = 8023; // Bmult27 -> Cmult6
    (Amult[27] => Cmult[7]) = 8892; // Amult27 -> Cmult7
    (Bmult[27] => Cmult[7]) = 8770; // Bmult27 -> Cmult7
    (Amult[27] => Cmult[8]) = 10272; // Amult27 -> Cmult8
    (Bmult[27] => Cmult[8]) = 9515; // Bmult27 -> Cmult8
    (Amult[27] => Cmult[9]) = 10730; // Amult27 -> Cmult9
    (Bmult[27] => Cmult[9]) = 10069; // Bmult27 -> Cmult9
    (Amult[27] => Cmult[10]) = 11045; // Amult27 -> Cmult10
    (Bmult[27] => Cmult[10]) = 10591; // Bmult27 -> Cmult10
    (Amult[27] => Cmult[11]) = 11666; // Amult27 -> Cmult11
    (Bmult[27] => Cmult[11]) = 11080; // Bmult27 -> Cmult11
    (Amult[27] => Cmult[12]) = 12256; // Amult27 -> Cmult12
    (Bmult[27] => Cmult[12]) = 11409; // Bmult27 -> Cmult12
    (Amult[27] => Cmult[13]) = 12759; // Amult27 -> Cmult13
    (Bmult[27] => Cmult[13]) = 12074; // Bmult27 -> Cmult13
    (Amult[27] => Cmult[14]) = 13409; // Amult27 -> Cmult14
    (Bmult[27] => Cmult[14]) = 12600; // Bmult27 -> Cmult14
    (Amult[27] => Cmult[15]) = 15103; // Amult27 -> Cmult15
    (Bmult[27] => Cmult[15]) = 13797; // Bmult27 -> Cmult15
    (Amult[27] => Cmult[16]) = 15003; // Amult27 -> Cmult16
    (Bmult[27] => Cmult[16]) = 13970; // Bmult27 -> Cmult16
    (Amult[27] => Cmult[17]) = 15095; // Amult27 -> Cmult17
    (Bmult[27] => Cmult[17]) = 14352; // Bmult27 -> Cmult17
    (Amult[27] => Cmult[18]) = 15429; // Amult27 -> Cmult18
    (Bmult[27] => Cmult[18]) = 13959; // Bmult27 -> Cmult18
    (Amult[27] => Cmult[19]) = 15755; // Amult27 -> Cmult19
    (Bmult[27] => Cmult[19]) = 14200; // Bmult27 -> Cmult19
    (Amult[27] => Cmult[20]) = 16197; // Amult27 -> Cmult20
    (Bmult[27] => Cmult[20]) = 14544; // Bmult27 -> Cmult20
    (Amult[27] => Cmult[21]) = 16498; // Amult27 -> Cmult21
    (Bmult[27] => Cmult[21]) = 14730; // Bmult27 -> Cmult21
    (Amult[27] => Cmult[22]) = 16797; // Amult27 -> Cmult22
    (Bmult[27] => Cmult[22]) = 15133; // Bmult27 -> Cmult22
    (Amult[27] => Cmult[23]) = 16966; // Amult27 -> Cmult23
    (Bmult[27] => Cmult[23]) = 15419; // Bmult27 -> Cmult23
    (Amult[27] => Cmult[24]) = 16849; // Amult27 -> Cmult24
    (Bmult[27] => Cmult[24]) = 15826; // Bmult27 -> Cmult24
    (Amult[27] => Cmult[25]) = 17105; // Amult27 -> Cmult25
    (Bmult[27] => Cmult[25]) = 16229; // Bmult27 -> Cmult25
    (Amult[27] => Cmult[26]) = 17868; // Amult27 -> Cmult26
    (Bmult[27] => Cmult[26]) = 16508; // Bmult27 -> Cmult26
    (Amult[27] => Cmult[27]) = 17997; // Amult27 -> Cmult27
    (Bmult[27] => Cmult[27]) = 21553; // Bmult27 -> Cmult27
    (Amult[27] => Cmult[28]) = 18261; // Amult27 -> Cmult28
    (Bmult[27] => Cmult[28]) = 22503; // Bmult27 -> Cmult28
    (Amult[27] => Cmult[29]) = 18599; // Amult27 -> Cmult29
    (Bmult[27] => Cmult[29]) = 23303; // Bmult27 -> Cmult29
    (Amult[27] => Cmult[30]) = 19277; // Amult27 -> Cmult30
    (Bmult[27] => Cmult[30]) = 23746; // Bmult27 -> Cmult30
    (Amult[27] => Cmult[31]) = 20084; // Amult27 -> Cmult31
    (Bmult[27] => Cmult[31]) = 25269; // Bmult27 -> Cmult31
    (Amult[27] => Cmult[32]) = 25227; // Amult27 -> Cmult32
    (Bmult[27] => Cmult[32]) = 25418; // Bmult27 -> Cmult32
    (Amult[27] => Cmult[33]) = 25481; // Amult27 -> Cmult33
    (Bmult[27] => Cmult[33]) = 25743; // Bmult27 -> Cmult33
    (Amult[27] => Cmult[34]) = 25723; // Amult27 -> Cmult34
    (Bmult[27] => Cmult[34]) = 26129; // Bmult27 -> Cmult34
    (Amult[27] => Cmult[35]) = 25898; // Amult27 -> Cmult35
    (Bmult[27] => Cmult[35]) = 26268; // Bmult27 -> Cmult35
    (Amult[27] => Cmult[36]) = 26243; // Amult27 -> Cmult36
    (Bmult[27] => Cmult[36]) = 26752; // Bmult27 -> Cmult36
    (Amult[27] => Cmult[37]) = 26451; // Amult27 -> Cmult37
    (Bmult[27] => Cmult[37]) = 26829; // Bmult27 -> Cmult37
    (Amult[27] => Cmult[38]) = 26693; // Amult27 -> Cmult38
    (Bmult[27] => Cmult[38]) = 27230; // Bmult27 -> Cmult38
    (Amult[27] => Cmult[39]) = 26936; // Amult27 -> Cmult39
    (Bmult[27] => Cmult[39]) = 27531; // Bmult27 -> Cmult39
    (Amult[27] => Cmult[40]) = 27284; // Amult27 -> Cmult40
    (Bmult[27] => Cmult[40]) = 27735; // Bmult27 -> Cmult40
    (Amult[27] => Cmult[41]) = 27386; // Amult27 -> Cmult41
    (Bmult[27] => Cmult[41]) = 27981; // Bmult27 -> Cmult41
    (Amult[27] => Cmult[42]) = 26933; // Amult27 -> Cmult42
    (Bmult[27] => Cmult[42]) = 27413; // Bmult27 -> Cmult42
    (Amult[27] => Cmult[43]) = 27508; // Amult27 -> Cmult43
    (Bmult[27] => Cmult[43]) = 25731; // Bmult27 -> Cmult43
    (Amult[27] => Cmult[44]) = 28160; // Amult27 -> Cmult44
    (Bmult[27] => Cmult[44]) = 26173; // Bmult27 -> Cmult44
    (Amult[27] => Cmult[45]) = 28124; // Amult27 -> Cmult45
    (Bmult[27] => Cmult[45]) = 26347; // Bmult27 -> Cmult45
    (Amult[27] => Cmult[46]) = 27644; // Amult27 -> Cmult46
    (Bmult[27] => Cmult[46]) = 25736; // Bmult27 -> Cmult46
    (Amult[27] => Cmult[47]) = 27457; // Amult27 -> Cmult47
    (Bmult[27] => Cmult[47]) = 25652; // Bmult27 -> Cmult47
    (Amult[27] => Cmult[48]) = 28523; // Amult27 -> Cmult48
    (Bmult[27] => Cmult[48]) = 26658; // Bmult27 -> Cmult48
    (Amult[27] => Cmult[49]) = 28317; // Amult27 -> Cmult49
    (Bmult[27] => Cmult[49]) = 26458; // Bmult27 -> Cmult49
    (Amult[27] => Cmult[50]) = 29055; // Amult27 -> Cmult50
    (Bmult[27] => Cmult[50]) = 27280; // Bmult27 -> Cmult50
    (Amult[27] => Cmult[51]) = 29406; // Amult27 -> Cmult51
    (Bmult[27] => Cmult[51]) = 27472; // Bmult27 -> Cmult51
    (Amult[27] => Cmult[52]) = 29892; // Amult27 -> Cmult52
    (Bmult[27] => Cmult[52]) = 28126; // Bmult27 -> Cmult52
    (Amult[27] => Cmult[53]) = 30357; // Amult27 -> Cmult53
    (Bmult[27] => Cmult[53]) = 28383; // Bmult27 -> Cmult53
    (Amult[27] => Cmult[54]) = 30636; // Amult27 -> Cmult54
    (Bmult[27] => Cmult[54]) = 28783; // Bmult27 -> Cmult54
    (Amult[27] => Cmult[55]) = 30894; // Amult27 -> Cmult55
    (Bmult[27] => Cmult[55]) = 28920; // Bmult27 -> Cmult55
    (Amult[27] => Cmult[56]) = 31230; // Amult27 -> Cmult56
    (Bmult[27] => Cmult[56]) = 29464; // Bmult27 -> Cmult56
    (Amult[27] => Cmult[57]) = 31612; // Amult27 -> Cmult57
    (Bmult[27] => Cmult[57]) = 29750; // Bmult27 -> Cmult57
    (Amult[27] => Cmult[58]) = 31976; // Amult27 -> Cmult58
    (Bmult[27] => Cmult[58]) = 30208; // Bmult27 -> Cmult58
    (Amult[27] => Cmult[59]) = 32146; // Amult27 -> Cmult59
    (Bmult[27] => Cmult[59]) = 30276; // Bmult27 -> Cmult59
    (Amult[27] => Cmult[60]) = 32604; // Amult27 -> Cmult60
    (Bmult[27] => Cmult[60]) = 30839; // Bmult27 -> Cmult60
    (Amult[27] => Cmult[61]) = 32822; // Amult27 -> Cmult61
    (Bmult[27] => Cmult[61]) = 30847; // Bmult27 -> Cmult61
    (Amult[27] => Cmult[62]) = 33401; // Amult27 -> Cmult62
    (Bmult[27] => Cmult[62]) = 31633; // Bmult27 -> Cmult62
    (Amult[27] => Cmult[63]) = 34496; // Amult27 -> Cmult63
    (Bmult[27] => Cmult[63]) = 32727; // Bmult27 -> Cmult63
    (Amult[28] => Cmult[2]) = 6007; // Amult28 -> Cmult2
    (Bmult[28] => Cmult[2]) = 6032; // Bmult28 -> Cmult2
    (Amult[28] => Cmult[3]) = 6209; // Amult28 -> Cmult3
    (Bmult[28] => Cmult[3]) = 6377; // Bmult28 -> Cmult3
    (Amult[28] => Cmult[4]) = 6895; // Amult28 -> Cmult4
    (Bmult[28] => Cmult[4]) = 6848; // Bmult28 -> Cmult4
    (Amult[28] => Cmult[5]) = 7784; // Amult28 -> Cmult5
    (Bmult[28] => Cmult[5]) = 7568; // Bmult28 -> Cmult5
    (Amult[28] => Cmult[6]) = 8701; // Amult28 -> Cmult6
    (Bmult[28] => Cmult[6]) = 8023; // Bmult28 -> Cmult6
    (Amult[28] => Cmult[7]) = 8892; // Amult28 -> Cmult7
    (Bmult[28] => Cmult[7]) = 8770; // Bmult28 -> Cmult7
    (Amult[28] => Cmult[8]) = 10272; // Amult28 -> Cmult8
    (Bmult[28] => Cmult[8]) = 9515; // Bmult28 -> Cmult8
    (Amult[28] => Cmult[9]) = 10730; // Amult28 -> Cmult9
    (Bmult[28] => Cmult[9]) = 10069; // Bmult28 -> Cmult9
    (Amult[28] => Cmult[10]) = 11045; // Amult28 -> Cmult10
    (Bmult[28] => Cmult[10]) = 10591; // Bmult28 -> Cmult10
    (Amult[28] => Cmult[11]) = 11666; // Amult28 -> Cmult11
    (Bmult[28] => Cmult[11]) = 11080; // Bmult28 -> Cmult11
    (Amult[28] => Cmult[12]) = 12256; // Amult28 -> Cmult12
    (Bmult[28] => Cmult[12]) = 11409; // Bmult28 -> Cmult12
    (Amult[28] => Cmult[13]) = 12759; // Amult28 -> Cmult13
    (Bmult[28] => Cmult[13]) = 12074; // Bmult28 -> Cmult13
    (Amult[28] => Cmult[14]) = 13409; // Amult28 -> Cmult14
    (Bmult[28] => Cmult[14]) = 12600; // Bmult28 -> Cmult14
    (Amult[28] => Cmult[15]) = 15103; // Amult28 -> Cmult15
    (Bmult[28] => Cmult[15]) = 13797; // Bmult28 -> Cmult15
    (Amult[28] => Cmult[16]) = 15003; // Amult28 -> Cmult16
    (Bmult[28] => Cmult[16]) = 13970; // Bmult28 -> Cmult16
    (Amult[28] => Cmult[17]) = 15095; // Amult28 -> Cmult17
    (Bmult[28] => Cmult[17]) = 14352; // Bmult28 -> Cmult17
    (Amult[28] => Cmult[18]) = 15429; // Amult28 -> Cmult18
    (Bmult[28] => Cmult[18]) = 13959; // Bmult28 -> Cmult18
    (Amult[28] => Cmult[19]) = 15755; // Amult28 -> Cmult19
    (Bmult[28] => Cmult[19]) = 14200; // Bmult28 -> Cmult19
    (Amult[28] => Cmult[20]) = 16197; // Amult28 -> Cmult20
    (Bmult[28] => Cmult[20]) = 14544; // Bmult28 -> Cmult20
    (Amult[28] => Cmult[21]) = 16498; // Amult28 -> Cmult21
    (Bmult[28] => Cmult[21]) = 14730; // Bmult28 -> Cmult21
    (Amult[28] => Cmult[22]) = 16797; // Amult28 -> Cmult22
    (Bmult[28] => Cmult[22]) = 15133; // Bmult28 -> Cmult22
    (Amult[28] => Cmult[23]) = 16966; // Amult28 -> Cmult23
    (Bmult[28] => Cmult[23]) = 15419; // Bmult28 -> Cmult23
    (Amult[28] => Cmult[24]) = 16849; // Amult28 -> Cmult24
    (Bmult[28] => Cmult[24]) = 15826; // Bmult28 -> Cmult24
    (Amult[28] => Cmult[25]) = 17105; // Amult28 -> Cmult25
    (Bmult[28] => Cmult[25]) = 16229; // Bmult28 -> Cmult25
    (Amult[28] => Cmult[26]) = 17868; // Amult28 -> Cmult26
    (Bmult[28] => Cmult[26]) = 16508; // Bmult28 -> Cmult26
    (Amult[28] => Cmult[27]) = 17997; // Amult28 -> Cmult27
    (Bmult[28] => Cmult[27]) = 16896; // Bmult28 -> Cmult27
    (Amult[28] => Cmult[28]) = 18261; // Amult28 -> Cmult28
    (Bmult[28] => Cmult[28]) = 22367; // Bmult28 -> Cmult28
    (Amult[28] => Cmult[29]) = 18599; // Amult28 -> Cmult29
    (Bmult[28] => Cmult[29]) = 23391; // Bmult28 -> Cmult29
    (Amult[28] => Cmult[30]) = 19277; // Amult28 -> Cmult30
    (Bmult[28] => Cmult[30]) = 24017; // Bmult28 -> Cmult30
    (Amult[28] => Cmult[31]) = 20084; // Amult28 -> Cmult31
    (Bmult[28] => Cmult[31]) = 25398; // Bmult28 -> Cmult31
    (Amult[28] => Cmult[32]) = 25227; // Amult28 -> Cmult32
    (Bmult[28] => Cmult[32]) = 25835; // Bmult28 -> Cmult32
    (Amult[28] => Cmult[33]) = 25481; // Amult28 -> Cmult33
    (Bmult[28] => Cmult[33]) = 26172; // Bmult28 -> Cmult33
    (Amult[28] => Cmult[34]) = 25723; // Amult28 -> Cmult34
    (Bmult[28] => Cmult[34]) = 26447; // Bmult28 -> Cmult34
    (Amult[28] => Cmult[35]) = 25898; // Amult28 -> Cmult35
    (Bmult[28] => Cmult[35]) = 26697; // Bmult28 -> Cmult35
    (Amult[28] => Cmult[36]) = 26243; // Amult28 -> Cmult36
    (Bmult[28] => Cmult[36]) = 26764; // Bmult28 -> Cmult36
    (Amult[28] => Cmult[37]) = 26451; // Amult28 -> Cmult37
    (Bmult[28] => Cmult[37]) = 26956; // Bmult28 -> Cmult37
    (Amult[28] => Cmult[38]) = 26693; // Amult28 -> Cmult38
    (Bmult[28] => Cmult[38]) = 27014; // Bmult28 -> Cmult38
    (Amult[28] => Cmult[39]) = 26936; // Amult28 -> Cmult39
    (Bmult[28] => Cmult[39]) = 27251; // Bmult28 -> Cmult39
    (Amult[28] => Cmult[40]) = 27284; // Amult28 -> Cmult40
    (Bmult[28] => Cmult[40]) = 27608; // Bmult28 -> Cmult40
    (Amult[28] => Cmult[41]) = 27386; // Amult28 -> Cmult41
    (Bmult[28] => Cmult[41]) = 27702; // Bmult28 -> Cmult41
    (Amult[28] => Cmult[42]) = 26933; // Amult28 -> Cmult42
    (Bmult[28] => Cmult[42]) = 27254; // Bmult28 -> Cmult42
    (Amult[28] => Cmult[43]) = 27508; // Amult28 -> Cmult43
    (Bmult[28] => Cmult[43]) = 27811; // Bmult28 -> Cmult43
    (Amult[28] => Cmult[44]) = 28160; // Amult28 -> Cmult44
    (Bmult[28] => Cmult[44]) = 26173; // Bmult28 -> Cmult44
    (Amult[28] => Cmult[45]) = 28124; // Amult28 -> Cmult45
    (Bmult[28] => Cmult[45]) = 26347; // Bmult28 -> Cmult45
    (Amult[28] => Cmult[46]) = 27644; // Amult28 -> Cmult46
    (Bmult[28] => Cmult[46]) = 25736; // Bmult28 -> Cmult46
    (Amult[28] => Cmult[47]) = 27457; // Amult28 -> Cmult47
    (Bmult[28] => Cmult[47]) = 25652; // Bmult28 -> Cmult47
    (Amult[28] => Cmult[48]) = 28523; // Amult28 -> Cmult48
    (Bmult[28] => Cmult[48]) = 26658; // Bmult28 -> Cmult48
    (Amult[28] => Cmult[49]) = 28317; // Amult28 -> Cmult49
    (Bmult[28] => Cmult[49]) = 26458; // Bmult28 -> Cmult49
    (Amult[28] => Cmult[50]) = 29055; // Amult28 -> Cmult50
    (Bmult[28] => Cmult[50]) = 27280; // Bmult28 -> Cmult50
    (Amult[28] => Cmult[51]) = 29406; // Amult28 -> Cmult51
    (Bmult[28] => Cmult[51]) = 27472; // Bmult28 -> Cmult51
    (Amult[28] => Cmult[52]) = 29892; // Amult28 -> Cmult52
    (Bmult[28] => Cmult[52]) = 28126; // Bmult28 -> Cmult52
    (Amult[28] => Cmult[53]) = 30357; // Amult28 -> Cmult53
    (Bmult[28] => Cmult[53]) = 28383; // Bmult28 -> Cmult53
    (Amult[28] => Cmult[54]) = 30636; // Amult28 -> Cmult54
    (Bmult[28] => Cmult[54]) = 28783; // Bmult28 -> Cmult54
    (Amult[28] => Cmult[55]) = 30894; // Amult28 -> Cmult55
    (Bmult[28] => Cmult[55]) = 28920; // Bmult28 -> Cmult55
    (Amult[28] => Cmult[56]) = 31230; // Amult28 -> Cmult56
    (Bmult[28] => Cmult[56]) = 29464; // Bmult28 -> Cmult56
    (Amult[28] => Cmult[57]) = 31612; // Amult28 -> Cmult57
    (Bmult[28] => Cmult[57]) = 29750; // Bmult28 -> Cmult57
    (Amult[28] => Cmult[58]) = 31976; // Amult28 -> Cmult58
    (Bmult[28] => Cmult[58]) = 30208; // Bmult28 -> Cmult58
    (Amult[28] => Cmult[59]) = 32146; // Amult28 -> Cmult59
    (Bmult[28] => Cmult[59]) = 30276; // Bmult28 -> Cmult59
    (Amult[28] => Cmult[60]) = 32604; // Amult28 -> Cmult60
    (Bmult[28] => Cmult[60]) = 30839; // Bmult28 -> Cmult60
    (Amult[28] => Cmult[61]) = 32822; // Amult28 -> Cmult61
    (Bmult[28] => Cmult[61]) = 30847; // Bmult28 -> Cmult61
    (Amult[28] => Cmult[62]) = 33401; // Amult28 -> Cmult62
    (Bmult[28] => Cmult[62]) = 31633; // Bmult28 -> Cmult62
    (Amult[28] => Cmult[63]) = 34496; // Amult28 -> Cmult63
    (Bmult[28] => Cmult[63]) = 32727; // Bmult28 -> Cmult63
    (Amult[29] => Cmult[2]) = 6007; // Amult29 -> Cmult2
    (Bmult[29] => Cmult[2]) = 6032; // Bmult29 -> Cmult2
    (Amult[29] => Cmult[3]) = 6209; // Amult29 -> Cmult3
    (Bmult[29] => Cmult[3]) = 6377; // Bmult29 -> Cmult3
    (Amult[29] => Cmult[4]) = 6895; // Amult29 -> Cmult4
    (Bmult[29] => Cmult[4]) = 6848; // Bmult29 -> Cmult4
    (Amult[29] => Cmult[5]) = 7784; // Amult29 -> Cmult5
    (Bmult[29] => Cmult[5]) = 7568; // Bmult29 -> Cmult5
    (Amult[29] => Cmult[6]) = 8701; // Amult29 -> Cmult6
    (Bmult[29] => Cmult[6]) = 8023; // Bmult29 -> Cmult6
    (Amult[29] => Cmult[7]) = 8892; // Amult29 -> Cmult7
    (Bmult[29] => Cmult[7]) = 8770; // Bmult29 -> Cmult7
    (Amult[29] => Cmult[8]) = 10272; // Amult29 -> Cmult8
    (Bmult[29] => Cmult[8]) = 9515; // Bmult29 -> Cmult8
    (Amult[29] => Cmult[9]) = 10730; // Amult29 -> Cmult9
    (Bmult[29] => Cmult[9]) = 10069; // Bmult29 -> Cmult9
    (Amult[29] => Cmult[10]) = 11045; // Amult29 -> Cmult10
    (Bmult[29] => Cmult[10]) = 10591; // Bmult29 -> Cmult10
    (Amult[29] => Cmult[11]) = 11666; // Amult29 -> Cmult11
    (Bmult[29] => Cmult[11]) = 11080; // Bmult29 -> Cmult11
    (Amult[29] => Cmult[12]) = 12256; // Amult29 -> Cmult12
    (Bmult[29] => Cmult[12]) = 11409; // Bmult29 -> Cmult12
    (Amult[29] => Cmult[13]) = 12759; // Amult29 -> Cmult13
    (Bmult[29] => Cmult[13]) = 12074; // Bmult29 -> Cmult13
    (Amult[29] => Cmult[14]) = 13409; // Amult29 -> Cmult14
    (Bmult[29] => Cmult[14]) = 12600; // Bmult29 -> Cmult14
    (Amult[29] => Cmult[15]) = 15103; // Amult29 -> Cmult15
    (Bmult[29] => Cmult[15]) = 13797; // Bmult29 -> Cmult15
    (Amult[29] => Cmult[16]) = 15003; // Amult29 -> Cmult16
    (Bmult[29] => Cmult[16]) = 13970; // Bmult29 -> Cmult16
    (Amult[29] => Cmult[17]) = 15095; // Amult29 -> Cmult17
    (Bmult[29] => Cmult[17]) = 14352; // Bmult29 -> Cmult17
    (Amult[29] => Cmult[18]) = 15429; // Amult29 -> Cmult18
    (Bmult[29] => Cmult[18]) = 13959; // Bmult29 -> Cmult18
    (Amult[29] => Cmult[19]) = 15755; // Amult29 -> Cmult19
    (Bmult[29] => Cmult[19]) = 14200; // Bmult29 -> Cmult19
    (Amult[29] => Cmult[20]) = 16197; // Amult29 -> Cmult20
    (Bmult[29] => Cmult[20]) = 14544; // Bmult29 -> Cmult20
    (Amult[29] => Cmult[21]) = 16498; // Amult29 -> Cmult21
    (Bmult[29] => Cmult[21]) = 14730; // Bmult29 -> Cmult21
    (Amult[29] => Cmult[22]) = 16797; // Amult29 -> Cmult22
    (Bmult[29] => Cmult[22]) = 15133; // Bmult29 -> Cmult22
    (Amult[29] => Cmult[23]) = 16966; // Amult29 -> Cmult23
    (Bmult[29] => Cmult[23]) = 15419; // Bmult29 -> Cmult23
    (Amult[29] => Cmult[24]) = 16849; // Amult29 -> Cmult24
    (Bmult[29] => Cmult[24]) = 15826; // Bmult29 -> Cmult24
    (Amult[29] => Cmult[25]) = 17105; // Amult29 -> Cmult25
    (Bmult[29] => Cmult[25]) = 16229; // Bmult29 -> Cmult25
    (Amult[29] => Cmult[26]) = 17868; // Amult29 -> Cmult26
    (Bmult[29] => Cmult[26]) = 16508; // Bmult29 -> Cmult26
    (Amult[29] => Cmult[27]) = 17997; // Amult29 -> Cmult27
    (Bmult[29] => Cmult[27]) = 16896; // Bmult29 -> Cmult27
    (Amult[29] => Cmult[28]) = 18261; // Amult29 -> Cmult28
    (Bmult[29] => Cmult[28]) = 17420; // Bmult29 -> Cmult28
    (Amult[29] => Cmult[29]) = 18599; // Amult29 -> Cmult29
    (Bmult[29] => Cmult[29]) = 23031; // Bmult29 -> Cmult29
    (Amult[29] => Cmult[30]) = 19277; // Amult29 -> Cmult30
    (Bmult[29] => Cmult[30]) = 23625; // Bmult29 -> Cmult30
    (Amult[29] => Cmult[31]) = 20084; // Amult29 -> Cmult31
    (Bmult[29] => Cmult[31]) = 25137; // Bmult29 -> Cmult31
    (Amult[29] => Cmult[32]) = 25227; // Amult29 -> Cmult32
    (Bmult[29] => Cmult[32]) = 25447; // Bmult29 -> Cmult32
    (Amult[29] => Cmult[33]) = 25481; // Amult29 -> Cmult33
    (Bmult[29] => Cmult[33]) = 25797; // Bmult29 -> Cmult33
    (Amult[29] => Cmult[34]) = 25723; // Amult29 -> Cmult34
    (Bmult[29] => Cmult[34]) = 26087; // Bmult29 -> Cmult34
    (Amult[29] => Cmult[35]) = 25898; // Amult29 -> Cmult35
    (Bmult[29] => Cmult[35]) = 26309; // Bmult29 -> Cmult35
    (Amult[29] => Cmult[36]) = 26243; // Amult29 -> Cmult36
    (Bmult[29] => Cmult[36]) = 26584; // Bmult29 -> Cmult36
    (Amult[29] => Cmult[37]) = 26451; // Amult29 -> Cmult37
    (Bmult[29] => Cmult[37]) = 26791; // Bmult29 -> Cmult37
    (Amult[29] => Cmult[38]) = 26693; // Amult29 -> Cmult38
    (Bmult[29] => Cmult[38]) = 27034; // Bmult29 -> Cmult38
    (Amult[29] => Cmult[39]) = 26936; // Amult29 -> Cmult39
    (Bmult[29] => Cmult[39]) = 27299; // Bmult29 -> Cmult39
    (Amult[29] => Cmult[40]) = 27284; // Amult29 -> Cmult40
    (Bmult[29] => Cmult[40]) = 27625; // Bmult29 -> Cmult40
    (Amult[29] => Cmult[41]) = 27386; // Amult29 -> Cmult41
    (Bmult[29] => Cmult[41]) = 27749; // Bmult29 -> Cmult41
    (Amult[29] => Cmult[42]) = 26933; // Amult29 -> Cmult42
    (Bmult[29] => Cmult[42]) = 27274; // Bmult29 -> Cmult42
    (Amult[29] => Cmult[43]) = 27508; // Amult29 -> Cmult43
    (Bmult[29] => Cmult[43]) = 27871; // Bmult29 -> Cmult43
    (Amult[29] => Cmult[44]) = 28160; // Amult29 -> Cmult44
    (Bmult[29] => Cmult[44]) = 28501; // Bmult29 -> Cmult44
    (Amult[29] => Cmult[45]) = 28124; // Amult29 -> Cmult45
    (Bmult[29] => Cmult[45]) = 26347; // Bmult29 -> Cmult45
    (Amult[29] => Cmult[46]) = 27644; // Amult29 -> Cmult46
    (Bmult[29] => Cmult[46]) = 25736; // Bmult29 -> Cmult46
    (Amult[29] => Cmult[47]) = 27457; // Amult29 -> Cmult47
    (Bmult[29] => Cmult[47]) = 25652; // Bmult29 -> Cmult47
    (Amult[29] => Cmult[48]) = 28523; // Amult29 -> Cmult48
    (Bmult[29] => Cmult[48]) = 26658; // Bmult29 -> Cmult48
    (Amult[29] => Cmult[49]) = 28317; // Amult29 -> Cmult49
    (Bmult[29] => Cmult[49]) = 26458; // Bmult29 -> Cmult49
    (Amult[29] => Cmult[50]) = 29055; // Amult29 -> Cmult50
    (Bmult[29] => Cmult[50]) = 27280; // Bmult29 -> Cmult50
    (Amult[29] => Cmult[51]) = 29406; // Amult29 -> Cmult51
    (Bmult[29] => Cmult[51]) = 27472; // Bmult29 -> Cmult51
    (Amult[29] => Cmult[52]) = 29892; // Amult29 -> Cmult52
    (Bmult[29] => Cmult[52]) = 28126; // Bmult29 -> Cmult52
    (Amult[29] => Cmult[53]) = 30357; // Amult29 -> Cmult53
    (Bmult[29] => Cmult[53]) = 28383; // Bmult29 -> Cmult53
    (Amult[29] => Cmult[54]) = 30636; // Amult29 -> Cmult54
    (Bmult[29] => Cmult[54]) = 28783; // Bmult29 -> Cmult54
    (Amult[29] => Cmult[55]) = 30894; // Amult29 -> Cmult55
    (Bmult[29] => Cmult[55]) = 28920; // Bmult29 -> Cmult55
    (Amult[29] => Cmult[56]) = 31230; // Amult29 -> Cmult56
    (Bmult[29] => Cmult[56]) = 29464; // Bmult29 -> Cmult56
    (Amult[29] => Cmult[57]) = 31612; // Amult29 -> Cmult57
    (Bmult[29] => Cmult[57]) = 29750; // Bmult29 -> Cmult57
    (Amult[29] => Cmult[58]) = 31976; // Amult29 -> Cmult58
    (Bmult[29] => Cmult[58]) = 30208; // Bmult29 -> Cmult58
    (Amult[29] => Cmult[59]) = 32146; // Amult29 -> Cmult59
    (Bmult[29] => Cmult[59]) = 30276; // Bmult29 -> Cmult59
    (Amult[29] => Cmult[60]) = 32604; // Amult29 -> Cmult60
    (Bmult[29] => Cmult[60]) = 30839; // Bmult29 -> Cmult60
    (Amult[29] => Cmult[61]) = 32822; // Amult29 -> Cmult61
    (Bmult[29] => Cmult[61]) = 30847; // Bmult29 -> Cmult61
    (Amult[29] => Cmult[62]) = 33401; // Amult29 -> Cmult62
    (Bmult[29] => Cmult[62]) = 31633; // Bmult29 -> Cmult62
    (Amult[29] => Cmult[63]) = 34496; // Amult29 -> Cmult63
    (Bmult[29] => Cmult[63]) = 32727; // Bmult29 -> Cmult63
    (Amult[30] => Cmult[3]) = 5925; // Amult30 -> Cmult3
    (Bmult[30] => Cmult[3]) = 5396; // Bmult30 -> Cmult3
    (Amult[30] => Cmult[4]) = 6479; // Amult30 -> Cmult4
    (Bmult[30] => Cmult[4]) = 6192; // Bmult30 -> Cmult4
    (Amult[30] => Cmult[5]) = 7154; // Amult30 -> Cmult5
    (Bmult[30] => Cmult[5]) = 6995; // Bmult30 -> Cmult5
    (Amult[30] => Cmult[6]) = 7891; // Amult30 -> Cmult6
    (Bmult[30] => Cmult[6]) = 7689; // Bmult30 -> Cmult6
    (Amult[30] => Cmult[7]) = 8415; // Amult30 -> Cmult7
    (Bmult[30] => Cmult[7]) = 8126; // Bmult30 -> Cmult7
    (Amult[30] => Cmult[8]) = 9467; // Amult30 -> Cmult8
    (Bmult[30] => Cmult[8]) = 8923; // Bmult30 -> Cmult8
    (Amult[30] => Cmult[9]) = 9896; // Amult30 -> Cmult9
    (Bmult[30] => Cmult[9]) = 9424; // Bmult30 -> Cmult9
    (Amult[30] => Cmult[10]) = 10639; // Amult30 -> Cmult10
    (Bmult[30] => Cmult[10]) = 10109; // Bmult30 -> Cmult10
    (Amult[30] => Cmult[11]) = 11243; // Amult30 -> Cmult11
    (Bmult[30] => Cmult[11]) = 10541; // Bmult30 -> Cmult11
    (Amult[30] => Cmult[12]) = 11529; // Amult30 -> Cmult12
    (Bmult[30] => Cmult[12]) = 10832; // Bmult30 -> Cmult12
    (Amult[30] => Cmult[13]) = 12274; // Amult30 -> Cmult13
    (Bmult[30] => Cmult[13]) = 11563; // Bmult30 -> Cmult13
    (Amult[30] => Cmult[14]) = 12847; // Amult30 -> Cmult14
    (Bmult[30] => Cmult[14]) = 12034; // Bmult30 -> Cmult14
    (Amult[30] => Cmult[15]) = 14256; // Amult30 -> Cmult15
    (Bmult[30] => Cmult[15]) = 13354; // Bmult30 -> Cmult15
    (Amult[30] => Cmult[16]) = 14327; // Amult30 -> Cmult16
    (Bmult[30] => Cmult[16]) = 13528; // Bmult30 -> Cmult16
    (Amult[30] => Cmult[17]) = 14708; // Amult30 -> Cmult17
    (Bmult[30] => Cmult[17]) = 13909; // Bmult30 -> Cmult17
    (Amult[30] => Cmult[18]) = 14762; // Amult30 -> Cmult18
    (Bmult[30] => Cmult[18]) = 13668; // Bmult30 -> Cmult18
    (Amult[30] => Cmult[19]) = 15043; // Amult30 -> Cmult19
    (Bmult[30] => Cmult[19]) = 13994; // Bmult30 -> Cmult19
    (Amult[30] => Cmult[20]) = 15556; // Amult30 -> Cmult20
    (Bmult[30] => Cmult[20]) = 14417; // Bmult30 -> Cmult20
    (Amult[30] => Cmult[21]) = 15802; // Amult30 -> Cmult21
    (Bmult[30] => Cmult[21]) = 14737; // Bmult30 -> Cmult21
    (Amult[30] => Cmult[22]) = 16155; // Amult30 -> Cmult22
    (Bmult[30] => Cmult[22]) = 14992; // Bmult30 -> Cmult22
    (Amult[30] => Cmult[23]) = 16259; // Amult30 -> Cmult23
    (Bmult[30] => Cmult[23]) = 15205; // Bmult30 -> Cmult23
    (Amult[30] => Cmult[24]) = 16188; // Amult30 -> Cmult24
    (Bmult[30] => Cmult[24]) = 15228; // Bmult30 -> Cmult24
    (Amult[30] => Cmult[25]) = 16426; // Amult30 -> Cmult25
    (Bmult[30] => Cmult[25]) = 15631; // Bmult30 -> Cmult25
    (Amult[30] => Cmult[26]) = 17226; // Amult30 -> Cmult26
    (Bmult[30] => Cmult[26]) = 16073; // Bmult30 -> Cmult26
    (Amult[30] => Cmult[27]) = 17199; // Amult30 -> Cmult27
    (Bmult[30] => Cmult[27]) = 16298; // Bmult30 -> Cmult27
    (Amult[30] => Cmult[28]) = 17676; // Amult30 -> Cmult28
    (Bmult[30] => Cmult[28]) = 16822; // Bmult30 -> Cmult28
    (Amult[30] => Cmult[29]) = 18057; // Amult30 -> Cmult29
    (Bmult[30] => Cmult[29]) = 17260; // Bmult30 -> Cmult29
    (Amult[30] => Cmult[30]) = 18626; // Amult30 -> Cmult30
    (Bmult[30] => Cmult[30]) = 23548; // Bmult30 -> Cmult30
    (Amult[30] => Cmult[31]) = 19480; // Amult30 -> Cmult31
    (Bmult[30] => Cmult[31]) = 25124; // Bmult30 -> Cmult31
    (Amult[30] => Cmult[32]) = 24993; // Amult30 -> Cmult32
    (Bmult[30] => Cmult[32]) = 25545; // Bmult30 -> Cmult32
    (Amult[30] => Cmult[33]) = 25247; // Amult30 -> Cmult33
    (Bmult[30] => Cmult[33]) = 25822; // Bmult30 -> Cmult33
    (Amult[30] => Cmult[34]) = 25486; // Amult30 -> Cmult34
    (Bmult[30] => Cmult[34]) = 26097; // Bmult30 -> Cmult34
    (Amult[30] => Cmult[35]) = 25667; // Amult30 -> Cmult35
    (Bmult[30] => Cmult[35]) = 26347; // Bmult30 -> Cmult35
    (Amult[30] => Cmult[36]) = 25863; // Amult30 -> Cmult36
    (Bmult[30] => Cmult[36]) = 26552; // Bmult30 -> Cmult36
    (Amult[30] => Cmult[37]) = 25934; // Amult30 -> Cmult37
    (Bmult[30] => Cmult[37]) = 26722; // Bmult30 -> Cmult37
    (Amult[30] => Cmult[38]) = 26015; // Amult30 -> Cmult38
    (Bmult[30] => Cmult[38]) = 27029; // Bmult30 -> Cmult38
    (Amult[30] => Cmult[39]) = 26315; // Amult30 -> Cmult39
    (Bmult[30] => Cmult[39]) = 27330; // Bmult30 -> Cmult39
    (Amult[30] => Cmult[40]) = 26789; // Amult30 -> Cmult40
    (Bmult[30] => Cmult[40]) = 27555; // Bmult30 -> Cmult40
    (Amult[30] => Cmult[41]) = 26765; // Amult30 -> Cmult41
    (Bmult[30] => Cmult[41]) = 27780; // Bmult30 -> Cmult41
    (Amult[30] => Cmult[42]) = 26255; // Amult30 -> Cmult42
    (Bmult[30] => Cmult[42]) = 27212; // Bmult30 -> Cmult42
    (Amult[30] => Cmult[43]) = 26887; // Amult30 -> Cmult43
    (Bmult[30] => Cmult[43]) = 27903; // Bmult30 -> Cmult43
    (Amult[30] => Cmult[44]) = 27482; // Amult30 -> Cmult44
    (Bmult[30] => Cmult[44]) = 28431; // Bmult30 -> Cmult44
    (Amult[30] => Cmult[45]) = 27503; // Amult30 -> Cmult45
    (Bmult[30] => Cmult[45]) = 28518; // Bmult30 -> Cmult45
    (Amult[30] => Cmult[46]) = 26966; // Amult30 -> Cmult46
    (Bmult[30] => Cmult[46]) = 25818; // Bmult30 -> Cmult46
    (Amult[30] => Cmult[47]) = 26836; // Amult30 -> Cmult47
    (Bmult[30] => Cmult[47]) = 25801; // Bmult30 -> Cmult47
    (Amult[30] => Cmult[48]) = 27845; // Amult30 -> Cmult48
    (Bmult[30] => Cmult[48]) = 26740; // Bmult30 -> Cmult48
    (Amult[30] => Cmult[49]) = 27650; // Amult30 -> Cmult49
    (Bmult[30] => Cmult[49]) = 26606; // Bmult30 -> Cmult49
    (Amult[30] => Cmult[50]) = 28424; // Amult30 -> Cmult50
    (Bmult[30] => Cmult[50]) = 27362; // Bmult30 -> Cmult50
    (Amult[30] => Cmult[51]) = 28728; // Amult30 -> Cmult51
    (Bmult[30] => Cmult[51]) = 27591; // Bmult30 -> Cmult51
    (Amult[30] => Cmult[52]) = 29381; // Amult30 -> Cmult52
    (Bmult[30] => Cmult[52]) = 28208; // Bmult30 -> Cmult52
    (Amult[30] => Cmult[53]) = 29679; // Amult30 -> Cmult53
    (Bmult[30] => Cmult[53]) = 28543; // Bmult30 -> Cmult53
    (Amult[30] => Cmult[54]) = 29958; // Amult30 -> Cmult54
    (Bmult[30] => Cmult[54]) = 28865; // Bmult30 -> Cmult54
    (Amult[30] => Cmult[55]) = 30216; // Amult30 -> Cmult55
    (Bmult[30] => Cmult[55]) = 29080; // Bmult30 -> Cmult55
    (Amult[30] => Cmult[56]) = 30690; // Amult30 -> Cmult56
    (Bmult[30] => Cmult[56]) = 29546; // Bmult30 -> Cmult56
    (Amult[30] => Cmult[57]) = 30934; // Amult30 -> Cmult57
    (Bmult[30] => Cmult[57]) = 29831; // Bmult30 -> Cmult57
    (Amult[30] => Cmult[58]) = 31352; // Amult30 -> Cmult58
    (Bmult[30] => Cmult[58]) = 30289; // Bmult30 -> Cmult58
    (Amult[30] => Cmult[59]) = 31468; // Amult30 -> Cmult59
    (Bmult[30] => Cmult[59]) = 30358; // Bmult30 -> Cmult59
    (Amult[30] => Cmult[60]) = 31983; // Amult30 -> Cmult60
    (Bmult[30] => Cmult[60]) = 30920; // Bmult30 -> Cmult60
    (Amult[30] => Cmult[61]) = 32144; // Amult30 -> Cmult61
    (Bmult[30] => Cmult[61]) = 31007; // Bmult30 -> Cmult61
    (Amult[30] => Cmult[62]) = 32779; // Amult30 -> Cmult62
    (Bmult[30] => Cmult[62]) = 31715; // Bmult30 -> Cmult62
    (Amult[30] => Cmult[63]) = 33874; // Amult30 -> Cmult63
    (Bmult[30] => Cmult[63]) = 32809; // Bmult30 -> Cmult63
    (Amult[31] => Cmult[3]) = 5925; // Amult31 -> Cmult3
    (Bmult[31] => Cmult[3]) = 5396; // Bmult31 -> Cmult3
    (Amult[31] => Cmult[4]) = 6479; // Amult31 -> Cmult4
    (Bmult[31] => Cmult[4]) = 6192; // Bmult31 -> Cmult4
    (Amult[31] => Cmult[5]) = 7154; // Amult31 -> Cmult5
    (Bmult[31] => Cmult[5]) = 6995; // Bmult31 -> Cmult5
    (Amult[31] => Cmult[6]) = 7891; // Amult31 -> Cmult6
    (Bmult[31] => Cmult[6]) = 7689; // Bmult31 -> Cmult6
    (Amult[31] => Cmult[7]) = 8415; // Amult31 -> Cmult7
    (Bmult[31] => Cmult[7]) = 8126; // Bmult31 -> Cmult7
    (Amult[31] => Cmult[8]) = 9467; // Amult31 -> Cmult8
    (Bmult[31] => Cmult[8]) = 8923; // Bmult31 -> Cmult8
    (Amult[31] => Cmult[9]) = 9896; // Amult31 -> Cmult9
    (Bmult[31] => Cmult[9]) = 9424; // Bmult31 -> Cmult9
    (Amult[31] => Cmult[10]) = 10639; // Amult31 -> Cmult10
    (Bmult[31] => Cmult[10]) = 10109; // Bmult31 -> Cmult10
    (Amult[31] => Cmult[11]) = 11243; // Amult31 -> Cmult11
    (Bmult[31] => Cmult[11]) = 10541; // Bmult31 -> Cmult11
    (Amult[31] => Cmult[12]) = 11529; // Amult31 -> Cmult12
    (Bmult[31] => Cmult[12]) = 10832; // Bmult31 -> Cmult12
    (Amult[31] => Cmult[13]) = 12274; // Amult31 -> Cmult13
    (Bmult[31] => Cmult[13]) = 11563; // Bmult31 -> Cmult13
    (Amult[31] => Cmult[14]) = 12847; // Amult31 -> Cmult14
    (Bmult[31] => Cmult[14]) = 12034; // Bmult31 -> Cmult14
    (Amult[31] => Cmult[15]) = 14256; // Amult31 -> Cmult15
    (Bmult[31] => Cmult[15]) = 13354; // Bmult31 -> Cmult15
    (Amult[31] => Cmult[16]) = 14327; // Amult31 -> Cmult16
    (Bmult[31] => Cmult[16]) = 13528; // Bmult31 -> Cmult16
    (Amult[31] => Cmult[17]) = 14708; // Amult31 -> Cmult17
    (Bmult[31] => Cmult[17]) = 13909; // Bmult31 -> Cmult17
    (Amult[31] => Cmult[18]) = 14762; // Amult31 -> Cmult18
    (Bmult[31] => Cmult[18]) = 13668; // Bmult31 -> Cmult18
    (Amult[31] => Cmult[19]) = 15043; // Amult31 -> Cmult19
    (Bmult[31] => Cmult[19]) = 13994; // Bmult31 -> Cmult19
    (Amult[31] => Cmult[20]) = 15556; // Amult31 -> Cmult20
    (Bmult[31] => Cmult[20]) = 14417; // Bmult31 -> Cmult20
    (Amult[31] => Cmult[21]) = 15802; // Amult31 -> Cmult21
    (Bmult[31] => Cmult[21]) = 14737; // Bmult31 -> Cmult21
    (Amult[31] => Cmult[22]) = 16155; // Amult31 -> Cmult22
    (Bmult[31] => Cmult[22]) = 14992; // Bmult31 -> Cmult22
    (Amult[31] => Cmult[23]) = 16259; // Amult31 -> Cmult23
    (Bmult[31] => Cmult[23]) = 15205; // Bmult31 -> Cmult23
    (Amult[31] => Cmult[24]) = 16188; // Amult31 -> Cmult24
    (Bmult[31] => Cmult[24]) = 15228; // Bmult31 -> Cmult24
    (Amult[31] => Cmult[25]) = 16426; // Amult31 -> Cmult25
    (Bmult[31] => Cmult[25]) = 15631; // Bmult31 -> Cmult25
    (Amult[31] => Cmult[26]) = 17226; // Amult31 -> Cmult26
    (Bmult[31] => Cmult[26]) = 16073; // Bmult31 -> Cmult26
    (Amult[31] => Cmult[27]) = 17199; // Amult31 -> Cmult27
    (Bmult[31] => Cmult[27]) = 16298; // Bmult31 -> Cmult27
    (Amult[31] => Cmult[28]) = 17676; // Amult31 -> Cmult28
    (Bmult[31] => Cmult[28]) = 16822; // Bmult31 -> Cmult28
    (Amult[31] => Cmult[29]) = 18057; // Amult31 -> Cmult29
    (Bmult[31] => Cmult[29]) = 17260; // Bmult31 -> Cmult29
    (Amult[31] => Cmult[30]) = 18626; // Amult31 -> Cmult30
    (Bmult[31] => Cmult[30]) = 17826; // Bmult31 -> Cmult30
    (Amult[31] => Cmult[31]) = 19480; // Amult31 -> Cmult31
    (Bmult[31] => Cmult[31]) = 25401; // Bmult31 -> Cmult31
    (Amult[31] => Cmult[32]) = 24993; // Amult31 -> Cmult32
    (Bmult[31] => Cmult[32]) = 25605; // Bmult31 -> Cmult32
    (Amult[31] => Cmult[33]) = 25247; // Amult31 -> Cmult33
    (Bmult[31] => Cmult[33]) = 25700; // Bmult31 -> Cmult33
    (Amult[31] => Cmult[34]) = 25486; // Amult31 -> Cmult34
    (Bmult[31] => Cmult[34]) = 26138; // Bmult31 -> Cmult34
    (Amult[31] => Cmult[35]) = 25667; // Amult31 -> Cmult35
    (Bmult[31] => Cmult[35]) = 26263; // Bmult31 -> Cmult35
    (Amult[31] => Cmult[36]) = 25863; // Amult31 -> Cmult36
    (Bmult[31] => Cmult[36]) = 26832; // Bmult31 -> Cmult36
    (Amult[31] => Cmult[37]) = 25934; // Amult31 -> Cmult37
    (Bmult[31] => Cmult[37]) = 27039; // Bmult31 -> Cmult37
    (Amult[31] => Cmult[38]) = 26015; // Amult31 -> Cmult38
    (Bmult[31] => Cmult[38]) = 27282; // Bmult31 -> Cmult38
    (Amult[31] => Cmult[39]) = 26315; // Amult31 -> Cmult39
    (Bmult[31] => Cmult[39]) = 27520; // Bmult31 -> Cmult39
    (Amult[31] => Cmult[40]) = 26789; // Amult31 -> Cmult40
    (Bmult[31] => Cmult[40]) = 27873; // Bmult31 -> Cmult40
    (Amult[31] => Cmult[41]) = 26765; // Amult31 -> Cmult41
    (Bmult[31] => Cmult[41]) = 27970; // Bmult31 -> Cmult41
    (Amult[31] => Cmult[42]) = 26255; // Amult31 -> Cmult42
    (Bmult[31] => Cmult[42]) = 27522; // Bmult31 -> Cmult42
    (Amult[31] => Cmult[43]) = 26887; // Amult31 -> Cmult43
    (Bmult[31] => Cmult[43]) = 28054; // Bmult31 -> Cmult43
    (Amult[31] => Cmult[44]) = 27482; // Amult31 -> Cmult44
    (Bmult[31] => Cmult[44]) = 28749; // Bmult31 -> Cmult44
    (Amult[31] => Cmult[45]) = 27503; // Amult31 -> Cmult45
    (Bmult[31] => Cmult[45]) = 28675; // Bmult31 -> Cmult45
    (Amult[31] => Cmult[46]) = 26966; // Amult31 -> Cmult46
    (Bmult[31] => Cmult[46]) = 28233; // Bmult31 -> Cmult46
    (Amult[31] => Cmult[47]) = 26836; // Amult31 -> Cmult47
    (Bmult[31] => Cmult[47]) = 25801; // Bmult31 -> Cmult47
    (Amult[31] => Cmult[48]) = 27845; // Amult31 -> Cmult48
    (Bmult[31] => Cmult[48]) = 26740; // Bmult31 -> Cmult48
    (Amult[31] => Cmult[49]) = 27650; // Amult31 -> Cmult49
    (Bmult[31] => Cmult[49]) = 26606; // Bmult31 -> Cmult49
    (Amult[31] => Cmult[50]) = 28424; // Amult31 -> Cmult50
    (Bmult[31] => Cmult[50]) = 27362; // Bmult31 -> Cmult50
    (Amult[31] => Cmult[51]) = 28728; // Amult31 -> Cmult51
    (Bmult[31] => Cmult[51]) = 27591; // Bmult31 -> Cmult51
    (Amult[31] => Cmult[52]) = 29381; // Amult31 -> Cmult52
    (Bmult[31] => Cmult[52]) = 28208; // Bmult31 -> Cmult52
    (Amult[31] => Cmult[53]) = 29679; // Amult31 -> Cmult53
    (Bmult[31] => Cmult[53]) = 28543; // Bmult31 -> Cmult53
    (Amult[31] => Cmult[54]) = 29958; // Amult31 -> Cmult54
    (Bmult[31] => Cmult[54]) = 28865; // Bmult31 -> Cmult54
    (Amult[31] => Cmult[55]) = 30216; // Amult31 -> Cmult55
    (Bmult[31] => Cmult[55]) = 29080; // Bmult31 -> Cmult55
    (Amult[31] => Cmult[56]) = 30690; // Amult31 -> Cmult56
    (Bmult[31] => Cmult[56]) = 29546; // Bmult31 -> Cmult56
    (Amult[31] => Cmult[57]) = 30934; // Amult31 -> Cmult57
    (Bmult[31] => Cmult[57]) = 29831; // Bmult31 -> Cmult57
    (Amult[31] => Cmult[58]) = 31352; // Amult31 -> Cmult58
    (Bmult[31] => Cmult[58]) = 30289; // Bmult31 -> Cmult58
    (Amult[31] => Cmult[59]) = 31468; // Amult31 -> Cmult59
    (Bmult[31] => Cmult[59]) = 30358; // Bmult31 -> Cmult59
    (Amult[31] => Cmult[60]) = 31983; // Amult31 -> Cmult60
    (Bmult[31] => Cmult[60]) = 30920; // Bmult31 -> Cmult60
    (Amult[31] => Cmult[61]) = 32144; // Amult31 -> Cmult61
    (Bmult[31] => Cmult[61]) = 31007; // Bmult31 -> Cmult61
    (Amult[31] => Cmult[62]) = 32779; // Amult31 -> Cmult62
    (Bmult[31] => Cmult[62]) = 31715; // Bmult31 -> Cmult62
    (Amult[31] => Cmult[63]) = 33874; // Amult31 -> Cmult63
    (Bmult[31] => Cmult[63]) = 32809; // Bmult31 -> Cmult63
  endspecify

  wire [15:0] A_mult_16_0;
  wire [15:0] B_mult_16_0;
  wire [31:0] C_mult_16_0;
  wire [15:0] A_mult_16_1;
  wire [15:0] B_mult_16_1;
  wire [31:0] C_mult_16_1;
  wire [31:0] A_mult_32;
  wire [31:0] B_mult_32;
  wire [63:0] C_mult_32;
  wire Valid_mult_16_0;
  wire Valid_mult_16_1;
  wire Valid_mult_32;


  assign Cmult = sel_mul_32x32 ? C_mult_32 : {C_mult_16_1, C_mult_16_0};

  assign A_mult_16_0 = sel_mul_32x32 ? 16'h0 : Amult[15:0];
  assign B_mult_16_0 = sel_mul_32x32 ? 16'h0 : Bmult[15:0];
  assign A_mult_16_1 = sel_mul_32x32 ? 16'h0 : Amult[31:16];
  assign B_mult_16_1 = sel_mul_32x32 ? 16'h0 : Bmult[31:16];

  assign A_mult_32 = sel_mul_32x32 ? Amult : 32'h0;
  assign B_mult_32 = sel_mul_32x32 ? Bmult : 32'h0;

  assign Valid_mult_16_0 = sel_mul_32x32 ? 1'b0 : Valid_mult[0];
  assign Valid_mult_16_1 = sel_mul_32x32 ? 1'b0 : Valid_mult[1];
  assign Valid_mult_32 = sel_mul_32x32 ? Valid_mult[0] : 1'b0;

  signed_mult #(
    .WIDTH(16)
  ) u_signed_mult_16_0 (
    .A(A_mult_16_0),  //I: 16 bits
    .B(B_mult_16_0),  //I: 16 bits
    .Valid(Valid_mult_16_0),  //I
    .C(C_mult_16_0)  //O: 32 bits
  );

  signed_mult #(
    .WIDTH(16)
  ) u_signed_mult_16_1 (
    .A(A_mult_16_1),  //I: 16 bits
    .B(B_mult_16_1),  //I: 16 bits
    .Valid(Valid_mult_16_1),  //I
    .C(C_mult_16_1)  //O: 32 bits
  );

  signed_mult #(
    .WIDTH(32)
  ) u_signed_mult_32 (
    .A(A_mult_32),  //I: 32 bits
    .B(B_mult_32),  //I: 32 bits
    .Valid(Valid_mult_32),  //I
    .C(C_mult_32)  //O: 64 bits
  );

endmodule
/*qlal4s3_mult_cell*/


(* blackbox *)
module RAM_8K_BLK (
  WA,
  RA,
  WD,
  WClk,
  RClk,
  WClk_En,
  RClk_En,
  WEN,
  RD
);

  parameter addr_int       = 9,
            data_depth_int = 512,
            data_width_int = 18,
            wr_enable_int  = 2,
            reg_rd_int     = 0;

  parameter [8191:0] INIT = 8192'bx;
  parameter INIT_FILE = "init.mem";

  input [addr_int-1:0] WA;
  input [addr_int-1:0] RA;
  input WClk, RClk;
  input WClk_En, RClk_En;
  input [wr_enable_int-1:0] WEN;
  input [data_width_int-1:0] WD;
  output [data_width_int-1:0] RD;

  wire VCC, GND;
  wire WClk0_Sel, RClk0_Sel;
  wire WClk1_Sel, RClk1_Sel;

  wire reg_rd0;
  wire reg_rd1;
  wire [10:0] addr_wr0, addr_rd0, addr_wr1, addr_rd1;

  wire [17:0] in_reg0;

  wire [2:0] wen_reg0;

  wire [15:0] out_reg0;

  wire [1:0] out_par0;

  wire [1:0] WS1_0, WS2_0;
  wire [1:0] WS_GND;

  wire LS, DS, SD, LS_RB1, DS_RB1, SD_RB1;

  wire WD0_SEL, RD0_SEL;
  wire WD1_SEL, RD1_SEL;

  assign VCC = 1'b1;
  assign GND = 1'b0;

  assign WD0_SEL = 1'b1;
  assign RD0_SEL = 1'b1;
  assign WD1_SEL = 1'b0;
  assign RD1_SEL = 1'b0;

  assign WClk0_Sel = 1'b0;
  assign RClk0_Sel = 1'b0;

  assign WClk1_Sel = 1'b0;
  assign RClk1_Sel = 1'b0;

  assign LS = 1'b0;
  assign DS = 1'b0;
  assign SD = 1'b0;
  assign LS_RB1 = 1'b0;
  assign DS_RB1 = 1'b0;
  assign SD_RB1 = 1'b0;

  assign reg_rd0 = reg_rd_int;
  assign WS_GND = 2'b00;

  assign reg_rd1 = 1'b0;

  assign wen_reg0[2:wr_enable_int] = 0;
  assign wen_reg0[wr_enable_int-1:0] = WEN;

  assign addr_wr1 = 11'b0000000000;
  assign addr_rd1 = 11'b0000000000;

  generate

    if (addr_int == 11) begin
      assign addr_wr0[10:0] = WA;
      assign addr_rd0[10:0] = RA;
    end else begin
      assign addr_wr0[10:addr_int] = 0;
      assign addr_wr0[addr_int-1:0] = WA;
      assign addr_rd0[10:addr_int] = 0;
      assign addr_rd0[addr_int-1:0] = RA;
    end

    if (data_width_int == 16) begin
      assign in_reg0[data_width_int-1:0] = WD[data_width_int-1:0];
    end else if (data_width_int > 8 && data_width_int < 16) begin
      assign in_reg0[15:data_width_int] = 0;
      assign in_reg0[data_width_int-1:0] = WD[data_width_int-1:0];
    end else if (data_width_int <= 8) begin
      assign in_reg0[15:data_width_int] = 0;
      assign in_reg0[data_width_int-1:0] = WD[data_width_int-1:0];
    end

    if (data_width_int <= 8) begin
      assign WS1_0 = 2'b00;
      assign WS2_0 = 2'b00;
    end else if (data_width_int > 8 && data_width_int <= 16) begin
      assign WS1_0 = 2'b01;
      assign WS2_0 = 2'b01;
    end else if (data_width_int > 16) begin
      assign WS1_0 = 2'b10;
      assign WS2_0 = 2'b10;
    end

  endgenerate

  ram8k_2x1_cell_macro #(
    `include "bram_init_8_16.vh"
    .INIT_FILE(INIT_FILE),
    .data_width_int(data_width_int),
    .data_depth_int(data_depth_int)
  ) U1 (
    .A1_0(addr_wr0),
    .A1_1(addr_wr1),
    .A2_0(addr_rd0),
    .A2_1(addr_rd1),
    .ASYNC_FLUSH_0(GND),  //chk
    .ASYNC_FLUSH_1(GND),  //chk
    .ASYNC_FLUSH_S0(GND),
    .ASYNC_FLUSH_S1(GND),
    .CLK1_0(WClk),
    .CLK1_1(GND),
    .CLK1S_0(WClk0_Sel),
    .CLK1S_1(WClk1_Sel),
    .CLK1EN_0(WClk_En),
    .CLK1EN_1(GND),
    .CLK2_0(RClk),
    .CLK2_1(GND),
    .CLK2S_0(RClk0_Sel),
    .CLK2S_1(RClk1_Sel),
    .CLK2EN_0(RClk_En),
    .CLK2EN_1(GND),
    .CONCAT_EN_0(GND),
    .CONCAT_EN_1(GND),
    .CS1_0(WD0_SEL),
    .CS1_1(WD1_SEL),
    .CS2_0(RD0_SEL),
    .CS2_1(RD1_SEL),
    .DIR_0(GND),
    .DIR_1(GND),
    .FIFO_EN_0(GND),
    .FIFO_EN_1(GND),
    .P1_0(GND),  //P1_0
    .P1_1(GND),  //P1_1
    .P2_0(GND),  //
    .P2_1(GND),  //
    .PIPELINE_RD_0(reg_rd0),
    .PIPELINE_RD_1(reg_rd1),
    .SYNC_FIFO_0(GND),
    .SYNC_FIFO_1(GND),
    .WD_1({18{GND}}),
    .WD_0({1'b0, in_reg0[15:8], 1'b0, in_reg0[7:0]}),
    .WIDTH_SELECT1_0(WS1_0),
    .WIDTH_SELECT1_1(WS_GND),
    .WIDTH_SELECT2_0(WS2_0),
    .WIDTH_SELECT2_1(WS_GND),
    .WEN1_0(wen_reg0[1:0]),
    .WEN1_1({2{GND}}),
    .Almost_Empty_0(),
    .Almost_Empty_1(),
    .Almost_Full_0(),
    .Almost_Full_1(),
    .POP_FLAG_0(),
    .POP_FLAG_1(),
    .PUSH_FLAG_0(),
    .PUSH_FLAG_1(),
    .RD_0({out_par0[1], out_reg0[15:8], out_par0[0], out_reg0[7:0]}),
    .RD_1(),
    .SD(SD),
    .SD_RB1(SD_RB1),
    .LS(LS),
    .LS_RB1(LS_RB1),
    .DS(DS),
    .DS_RB1(DS_RB1),
    .TEST1A(GND),
    .TEST1B(GND),
    .RMA(4'd0),
    .RMB(4'd0),
    .RMEA(GND),
    .RMEB(GND)
  );

  assign RD[data_width_int-1 : 0] = out_reg0[data_width_int-1 : 0];

endmodule

(* blackbox *)
module RAM_16K_BLK (
  WA,
  RA,
  WD,
  WClk,
  RClk,
  WClk_En,
  RClk_En,
  WEN,
  RD
);

  parameter addr_int       = 9,
            data_depth_int = 512,
            data_width_int = 36,
            wr_enable_int  = 4,
            reg_rd_int     = 0;

  parameter [16383:0] INIT = 16384'bx;
  parameter INIT_FILE = "init.mem";

  input [addr_int-1:0] WA;
  input [addr_int-1:0] RA;
  input WClk, RClk;
  input WClk_En, RClk_En;
  input [wr_enable_int-1:0] WEN;
  input [data_width_int-1:0] WD;
  output [data_width_int-1:0] RD;

  wire VCC, GND;

  wire WClk0_Sel, RClk0_Sel;
  wire WClk1_Sel, RClk1_Sel;

  wire reg_rd0;
  wire reg_rd1;
  wire [10:0] addr_wr0, addr_rd0, addr_wr1, addr_rd1;

  wire [31:0] in_reg0;

  wire [4:0] wen_reg0;

  wire [31:0] out_reg0;

  wire [3:0] out_par0;

  wire [1:0] WS1_0, WS2_0;
  wire [1:0] WS_GND;

  wire LS, DS, SD, LS_RB1, DS_RB1, SD_RB1;

  wire WD0_SEL, RD0_SEL;
  wire WD1_SEL, RD1_SEL;

  assign VCC = 1'b1;
  assign GND = 1'b0;

  assign WD0_SEL = 1'b1;
  assign RD0_SEL = 1'b1;
  assign WD1_SEL = 1'b1;
  assign RD1_SEL = 1'b1;

  assign WClk0_Sel = 1'b0;
  assign RClk0_Sel = 1'b0;

  assign WClk1_Sel = 1'b0;
  assign RClk1_Sel = 1'b0;

  assign LS = 1'b0;
  assign DS = 1'b0;
  assign SD = 1'b0;
  assign LS_RB1 = 1'b0;
  assign DS_RB1 = 1'b0;
  assign SD_RB1 = 1'b0;

  assign reg_rd0 = reg_rd_int;
  assign WS_GND = 2'b00;

  assign reg_rd1 = 1'b0;

  assign wen_reg0[4:wr_enable_int] = 0;
  assign wen_reg0[wr_enable_int-1:0] = WEN;

  assign addr_wr1 = 11'b0000000000;
  assign addr_rd1 = 11'b0000000000;

  generate

    if (addr_int == 11) begin
      assign addr_wr0[10:0] = WA;
      assign addr_rd0[10:0] = RA;
    end else begin
      assign addr_wr0[10:addr_int] = 0;
      assign addr_wr0[addr_int-1:0] = WA;
      assign addr_rd0[10:addr_int] = 0;
      assign addr_rd0[addr_int-1:0] = RA;
    end

    if (data_width_int == 32) begin
      assign in_reg0[data_width_int-1:0] = WD[data_width_int-1:0];
    end else if (data_width_int > 8 && data_width_int < 32) begin
      assign in_reg0[31:data_width_int] = 0;
      assign in_reg0[data_width_int-1:0] = WD[data_width_int-1:0];
    end else if (data_width_int <= 8) begin
      assign in_reg0[31:data_width_int] = 0;
      assign in_reg0[data_width_int-1:0] = WD[data_width_int-1:0];
    end

    if (data_width_int <= 8) begin
      assign WS1_0 = 2'b00;
      assign WS2_0 = 2'b00;
    end else if (data_width_int > 8 && data_width_int <= 16) begin
      assign WS1_0 = 2'b01;
      assign WS2_0 = 2'b01;
    end else if (data_width_int > 16) begin
      assign WS1_0 = 2'b10;
      assign WS2_0 = 2'b10;
    end

    if (data_width_int <= 16) begin

      ram8k_2x1_cell_macro #(
        `include "bram_init_8_16.vh"
        .INIT_FILE(INIT_FILE),
        .data_width_int(data_width_int),
        .data_depth_int(data_depth_int)
      ) U1 (
        .A1_0(addr_wr0),
        .A1_1(addr_wr1),
        .A2_0(addr_rd0),
        .A2_1(addr_rd1),
        .ASYNC_FLUSH_0(GND),
        .ASYNC_FLUSH_1(GND),
        .ASYNC_FLUSH_S0(GND),
        .ASYNC_FLUSH_S1(GND),
        .CLK1_0(WClk),
        .CLK1_1(WClk),
        .CLK1S_0(WClk0_Sel),
        .CLK1S_1(WClk0_Sel),
        .CLK1EN_0(WClk_En),
        .CLK1EN_1(WClk_En),
        .CLK2_0(RClk),
        .CLK2_1(RClk),
        .CLK2S_0(RClk0_Sel),
        .CLK2S_1(RClk0_Sel),
        .CLK2EN_0(RClk_En),
        .CLK2EN_1(RClk_En),
        .CONCAT_EN_0(VCC),
        .CONCAT_EN_1(GND),
        .CS1_0(WD0_SEL),
        .CS1_1(GND),
        .CS2_0(RD0_SEL),
        .CS2_1(GND),
        .DIR_0(GND),
        .DIR_1(GND),
        .FIFO_EN_0(GND),
        .FIFO_EN_1(GND),
        .P1_0(GND),
        .P1_1(GND),
        .P2_0(GND),
        .P2_1(GND),
        .PIPELINE_RD_0(reg_rd0),
        .PIPELINE_RD_1(GND),
        .SYNC_FIFO_0(GND),
        .SYNC_FIFO_1(GND),
        .WD_1({18{GND}}),
        .WD_0({1'b0, in_reg0[15:8], 1'b0, in_reg0[7:0]}),
        .WIDTH_SELECT1_0(WS1_0),
        .WIDTH_SELECT1_1(WS_GND),
        .WIDTH_SELECT2_0(WS2_0),
        .WIDTH_SELECT2_1(WS_GND),
        .WEN1_0(wen_reg0[1:0]),
        .WEN1_1(wen_reg0[3:2]),
        .Almost_Empty_0(),
        .Almost_Empty_1(),
        .Almost_Full_0(),
        .Almost_Full_1(),
        .POP_FLAG_0(),
        .POP_FLAG_1(),
        .PUSH_FLAG_0(),
        .PUSH_FLAG_1(),
        .RD_0({out_par0[1], out_reg0[15:8], out_par0[0], out_reg0[7:0]}),
        .RD_1(),
        .SD(SD),
        .SD_RB1(SD_RB1),
        .LS(LS),
        .LS_RB1(LS_RB1),
        .DS(DS),
        .DS_RB1(DS_RB1),
        .TEST1A(GND),
        .TEST1B(GND),
        .RMA(4'd0),
        .RMB(4'd0),
        .RMEA(GND),
        .RMEB(GND)
      );
    end else if (data_width_int > 16) begin

      ram8k_2x1_cell_macro #(
        `include "bram_init_32.vh"
        .INIT_FILE(INIT_FILE),
        .data_width_int(data_width_int),
        .data_depth_int(data_depth_int)
      ) U2 (
        .A1_0(addr_wr0),
        .A1_1(addr_wr1),
        .A2_0(addr_rd0),
        .A2_1(addr_rd1),
        .ASYNC_FLUSH_0(GND),
        .ASYNC_FLUSH_1(GND),
        .ASYNC_FLUSH_S0(GND),
        .ASYNC_FLUSH_S1(GND),
        .CLK1_0(WClk),
        .CLK1_1(WClk),
        .CLK1S_0(WClk0_Sel),
        .CLK1S_1(WClk0_Sel),
        .CLK1EN_0(WClk_En),
        .CLK1EN_1(WClk_En),
        .CLK2_0(RClk),
        .CLK2_1(RClk),
        .CLK2S_0(RClk0_Sel),
        .CLK2S_1(RClk0_Sel),
        .CLK2EN_0(RClk_En),
        .CLK2EN_1(RClk_En),
        .CONCAT_EN_0(VCC),
        .CONCAT_EN_1(GND),
        .CS1_0(WD0_SEL),
        .CS1_1(GND),
        .CS2_0(RD0_SEL),
        .CS2_1(GND),
        .DIR_0(GND),
        .DIR_1(GND),
        .FIFO_EN_0(GND),
        .FIFO_EN_1(GND),
        .P1_0(GND),
        .P1_1(GND),
        .P2_0(GND),
        .P2_1(GND),
        .PIPELINE_RD_0(reg_rd0),
        .PIPELINE_RD_1(GND),
        .SYNC_FIFO_0(GND),
        .SYNC_FIFO_1(GND),
        .WD_1({1'b0, in_reg0[31:24], 1'b0, in_reg0[23:16]}),
        .WD_0({1'b0, in_reg0[15:8], 1'b0, in_reg0[7:0]}),
        .WIDTH_SELECT1_0(WS1_0),
        .WIDTH_SELECT1_1(WS_GND),
        .WIDTH_SELECT2_0(WS2_0),
        .WIDTH_SELECT2_1(WS_GND),
        .WEN1_0(wen_reg0[1:0]),
        .WEN1_1(wen_reg0[3:2]),
        .Almost_Empty_0(),
        .Almost_Empty_1(),
        .Almost_Full_0(),
        .Almost_Full_1(),
        .POP_FLAG_0(),
        .POP_FLAG_1(),
        .PUSH_FLAG_0(),
        .PUSH_FLAG_1(),
        .RD_0({out_par0[1], out_reg0[15:8], out_par0[0], out_reg0[7:0]}),
        .RD_1({out_par0[3], out_reg0[31:24], out_par0[2], out_reg0[23:16]}),
        .SD(SD),
        .SD_RB1(SD_RB1),
        .LS(LS),
        .LS_RB1(LS_RB1),
        .DS(DS),
        .DS_RB1(DS_RB1),
        .TEST1A(GND),
        .TEST1B(GND),
        .RMA(4'd0),
        .RMB(4'd0),
        .RMEA(GND),
        .RMEB(GND)
      );
    end

  endgenerate

  assign RD[data_width_int-1 : 0] = out_reg0[data_width_int-1 : 0];

endmodule

(* blackbox *)
module FIFO_8K_BLK (
  DIN,
  Fifo_Push_Flush,
  Fifo_Pop_Flush,
  PUSH,
  POP,
  Push_Clk,
  Pop_Clk,
  Push_Clk_En,
  Pop_Clk_En,
  Fifo_Dir,
  Async_Flush,
  Almost_Full,
  Almost_Empty,
  PUSH_FLAG,
  POP_FLAG,
  DOUT
);

  parameter data_depth_int = 512, data_width_int = 36, reg_rd_int = 0, sync_fifo_int = 0;

  input Fifo_Push_Flush, Fifo_Pop_Flush;
  input Push_Clk, Pop_Clk;
  input PUSH, POP;
  input [data_width_int-1:0] DIN;
  input Push_Clk_En, Pop_Clk_En, Fifo_Dir, Async_Flush;
  output [data_width_int-1:0] DOUT;
  output [3:0] PUSH_FLAG, POP_FLAG;
  output Almost_Full, Almost_Empty;

  wire LS, DS, SD, LS_RB1, DS_RB1, SD_RB1;
  wire VCC, GND;

  wire [10:0] addr_wr, addr_rd;
  wire clk1_sig0, clk2_sig0, clk1_sig_en0, clk2_sig_en0, fifo_clk1_flush_sig0, fifo_clk2_flush_sig0, p1_sig0, p2_sig0,clk1_sig_sel0,clk2_sig_sel0;
  wire reg_rd0, sync_fifo0;
  wire [15:0] in_reg0;
  wire [15:0] out_reg0;
  wire [1:0] WS1_0;
  wire [1:0] WS2_0;
  wire Push_Clk0_Sel, Pop_Clk0_Sel;
  wire Async_Flush_Sel0;

  wire [1:0] out_par0;

  assign LS = 1'b0;
  assign DS = 1'b0;
  assign SD = 1'b0;
  assign LS_RB1 = 1'b0;
  assign DS_RB1 = 1'b0;
  assign SD_RB1 = 1'b0;

  assign VCC = 1'b1;
  assign GND = 1'b0;

  assign Push_Clk0_Sel = 1'b0;
  assign Pop_Clk0_Sel = 1'b0;
  assign Async_Flush_Sel0 = 1'b0;

  assign reg_rd0 = reg_rd_int;
  assign sync_fifo0 = sync_fifo_int;

  assign addr_wr = 11'b00000000000;
  assign addr_rd = 11'b00000000000;

  assign clk1_sig0 = Fifo_Dir ? Pop_Clk : Push_Clk;
  assign clk2_sig0 = Fifo_Dir ? Push_Clk : Pop_Clk;
  assign clk1_sig_en0 = Fifo_Dir ? Pop_Clk_En : Push_Clk_En;
  assign clk2_sig_en0 = Fifo_Dir ? Push_Clk_En : Pop_Clk_En;
  assign clk1_sig_sel0 = Push_Clk0_Sel;
  assign clk2_sig_sel0 = Pop_Clk0_Sel;
  assign fifo_clk1_flush_sig0 = Fifo_Dir ? Fifo_Pop_Flush : Fifo_Push_Flush;
  assign fifo_clk2_flush_sig0 = Fifo_Dir ? Fifo_Push_Flush : Fifo_Pop_Flush;
  assign p1_sig0 = Fifo_Dir ? POP : PUSH;
  assign p2_sig0 = Fifo_Dir ? PUSH : POP;

  generate

    if (data_width_int == 16) begin
      assign in_reg0[data_width_int-1:0] = DIN[data_width_int-1:0];
    end else if (data_width_int > 8 && data_width_int < 16) begin
      assign in_reg0[15:data_width_int] = 0;
      assign in_reg0[data_width_int-1:0] = DIN[data_width_int-1:0];
    end else if (data_width_int <= 8) begin
      assign in_reg0[15:data_width_int] = 0;
      assign in_reg0[data_width_int-1:0] = DIN[data_width_int-1:0];
    end

    if (data_width_int <= 8) begin
      assign WS1_0 = 2'b00;
      assign WS2_0 = 2'b00;
    end else if (data_width_int > 8 && data_width_int <= 16) begin
      assign WS1_0 = 2'b01;
      assign WS2_0 = 2'b01;
    end else if (data_width_int > 16) begin
      assign WS1_0 = 2'b10;
      assign WS2_0 = 2'b10;
    end

  endgenerate

  ram8k_2x1_cell_macro #(
    .data_width_int(data_width_int),
    .data_depth_int(data_depth_int)
  ) U1 (
    .A1_0(addr_wr),
    .A1_1(addr_wr),
    .A2_0(addr_rd),
    .A2_1(addr_rd),
    .ASYNC_FLUSH_0(Async_Flush),
    .ASYNC_FLUSH_1(GND),
    .ASYNC_FLUSH_S0(Async_Flush_Sel0),
    .ASYNC_FLUSH_S1(GND),
    .CLK1_0(clk1_sig0),
    .CLK1_1(GND),
    .CLK1EN_0(clk1_sig_en0),
    .CLK1EN_1(GND),
    .CLK2_0(clk2_sig0),
    .CLK2_1(GND),
    .CLK1S_0(clk1_sig_sel0),
    .CLK1S_1(GND),
    .CLK2S_0(clk2_sig_sel0),
    .CLK2S_1(GND),
    .CLK2EN_0(clk2_sig_en0),
    .CLK2EN_1(GND),
    .CONCAT_EN_0(GND),
    .CONCAT_EN_1(GND),
    .CS1_0(fifo_clk1_flush_sig0),
    .CS1_1(GND),
    .CS2_0(fifo_clk2_flush_sig0),
    .CS2_1(GND),
    .DIR_0(Fifo_Dir),
    .DIR_1(GND),
    .FIFO_EN_0(VCC),
    .FIFO_EN_1(GND),
    .P1_0(p1_sig0),
    .P1_1(GND),
    .P2_0(p2_sig0),
    .P2_1(GND),
    .PIPELINE_RD_0(reg_rd0),
    .PIPELINE_RD_1(GND),
    .SYNC_FIFO_0(sync_fifo0),
    .SYNC_FIFO_1(GND),
    .WD_1({18{GND}}),
    .WD_0({1'b0, in_reg0[15:8], 1'b0, in_reg0[7:0]}),
    .WIDTH_SELECT1_0(WS1_0),
    .WIDTH_SELECT1_1({GND, GND}),
    .WIDTH_SELECT2_0(WS2_0),
    .WIDTH_SELECT2_1({GND, GND}),
    .WEN1_0({GND, GND}),
    .WEN1_1({GND, GND}),
    .Almost_Empty_0(Almost_Empty),
    .Almost_Empty_1(),
    .Almost_Full_0(Almost_Full),
    .Almost_Full_1(),
    .POP_FLAG_0(POP_FLAG),
    .POP_FLAG_1(),
    .PUSH_FLAG_0(PUSH_FLAG),
    .PUSH_FLAG_1(),
    .RD_0({out_par0[1], out_reg0[15:8], out_par0[0], out_reg0[7:0]}),
    .RD_1(),
    .SD(SD),
    .SD_RB1(SD_RB1),
    .LS(LS),
    .LS_RB1(LS_RB1),
    .DS(DS),
    .DS_RB1(DS_RB1),
    .TEST1A(GND),
    .TEST1B(GND),
    .RMA(4'd0),
    .RMB(4'd0),
    .RMEA(GND),
    .RMEB(GND)
  );

  assign DOUT[data_width_int-1 : 0] = out_reg0[data_width_int-1 : 0];

endmodule

(* blackbox *)
module FIFO_16K_BLK (
  DIN,
  Fifo_Push_Flush,
  Fifo_Pop_Flush,
  PUSH,
  POP,
  Push_Clk,
  Pop_Clk,
  Push_Clk_En,
  Pop_Clk_En,
  Fifo_Dir,
  Async_Flush,
  Almost_Full,
  Almost_Empty,
  PUSH_FLAG,
  POP_FLAG,
  DOUT
);

  parameter data_depth_int = 512, data_width_int = 36, reg_rd_int = 0, sync_fifo_int = 0;

  input Fifo_Push_Flush, Fifo_Pop_Flush;
  input Push_Clk, Pop_Clk;
  input PUSH, POP;
  input [data_width_int-1:0] DIN;
  input Push_Clk_En, Pop_Clk_En, Fifo_Dir, Async_Flush;
  output [data_width_int-1:0] DOUT;
  output [3:0] PUSH_FLAG, POP_FLAG;
  output Almost_Full, Almost_Empty;

  wire LS, DS, SD, LS_RB1, DS_RB1, SD_RB1;
  wire VCC, GND;

  wire [10:0] addr_wr, addr_rd;
  wire clk1_sig0, clk2_sig0, clk1_sig_en0, clk2_sig_en0, fifo_clk1_flush_sig0, fifo_clk2_flush_sig0, p1_sig0, p2_sig0,clk1_sig_sel0,clk2_sig_sel0;
  wire reg_rd0, sync_fifo0;
  wire [31:0] in_reg0;
  wire [31:0] out_reg0;
  wire [1:0] WS1_0;
  wire [1:0] WS2_0;
  wire Push_Clk0_Sel, Pop_Clk0_Sel;
  wire Async_Flush_Sel0;

  wire [3:0] out_par0;
  wire [1:0] out_par1;

  assign LS = 1'b0;
  assign DS = 1'b0;
  assign SD = 1'b0;
  assign LS_RB1 = 1'b0;
  assign DS_RB1 = 1'b0;
  assign SD_RB1 = 1'b0;

  assign VCC = 1'b1;
  assign GND = 1'b0;

  assign Push_Clk0_Sel = 1'b0;
  assign Pop_Clk0_Sel = 1'b0;
  assign Async_Flush_Sel0 = 1'b0;

  assign reg_rd0 = reg_rd_int;
  assign sync_fifo0 = sync_fifo_int;

  assign addr_wr = 11'b00000000000;
  assign addr_rd = 11'b00000000000;

  assign clk1_sig0 = Fifo_Dir ? Pop_Clk : Push_Clk;
  assign clk2_sig0 = Fifo_Dir ? Push_Clk : Pop_Clk;
  assign clk1_sig_en0 = Fifo_Dir ? Pop_Clk_En : Push_Clk_En;
  assign clk2_sig_en0 = Fifo_Dir ? Push_Clk_En : Pop_Clk_En;
  assign clk1_sig_sel0 = Push_Clk0_Sel;
  assign clk2_sig_sel0 = Pop_Clk0_Sel;
  assign fifo_clk1_flush_sig0 = Fifo_Dir ? Fifo_Pop_Flush : Fifo_Push_Flush;
  assign fifo_clk2_flush_sig0 = Fifo_Dir ? Fifo_Push_Flush : Fifo_Pop_Flush;
  assign p1_sig0 = Fifo_Dir ? POP : PUSH;
  assign p2_sig0 = Fifo_Dir ? PUSH : POP;

  generate
    if (data_width_int == 32) begin
      assign in_reg0[data_width_int-1:0] = DIN[data_width_int-1:0];
    end else if (data_width_int > 8 && data_width_int < 32) begin
      assign in_reg0[31:data_width_int] = 0;
      assign in_reg0[data_width_int-1:0] = DIN[data_width_int-1:0];
    end else if (data_width_int <= 8) begin
      assign in_reg0[31:data_width_int] = 0;
      assign in_reg0[data_width_int-1:0] = DIN[data_width_int-1:0];
    end

    if (data_width_int <= 8) begin
      assign WS1_0 = 2'b00;
      assign WS2_0 = 2'b00;
    end else if (data_width_int > 8 && data_width_int <= 16) begin
      assign WS1_0 = 2'b01;
      assign WS2_0 = 2'b01;
    end else if (data_width_int > 16) begin
      assign WS1_0 = 2'b10;
      assign WS2_0 = 2'b10;
    end

    if (data_width_int <= 16) begin

      ram8k_2x1_cell_macro #(
        .data_width_int(data_width_int),
        .data_depth_int(data_depth_int)
      ) U1 (
        .A1_0(addr_wr),
        .A1_1(addr_wr),
        .A2_0(addr_rd),
        .A2_1(addr_rd),
        .ASYNC_FLUSH_0(Async_Flush),
        .ASYNC_FLUSH_1(GND),
        .ASYNC_FLUSH_S0(Async_Flush_Sel0),
        .ASYNC_FLUSH_S1(Async_Flush_Sel0),
        .CLK1_0(clk1_sig0),
        .CLK1_1(clk1_sig0),
        .CLK1EN_0(clk1_sig_en0),
        .CLK1EN_1(clk1_sig_en0),
        .CLK2_0(clk2_sig0),
        .CLK2_1(clk2_sig0),
        .CLK1S_0(clk1_sig_sel0),
        .CLK1S_1(clk1_sig_sel0),
        .CLK2S_0(clk2_sig_sel0),
        .CLK2S_1(clk2_sig_sel0),
        .CLK2EN_0(clk2_sig_en0),
        .CLK2EN_1(clk2_sig_en0),
        .CONCAT_EN_0(VCC),
        .CONCAT_EN_1(GND),
        .CS1_0(fifo_clk1_flush_sig0),
        .CS1_1(GND),
        .CS2_0(fifo_clk2_flush_sig0),
        .CS2_1(GND),
        .DIR_0(Fifo_Dir),
        .DIR_1(GND),
        .FIFO_EN_0(VCC),
        .FIFO_EN_1(GND),
        .P1_0(p1_sig0),
        .P1_1(GND),
        .P2_0(p2_sig0),
        .P2_1(GND),
        .PIPELINE_RD_0(reg_rd0),
        .PIPELINE_RD_1(GND),
        .SYNC_FIFO_0(sync_fifo0),
        .SYNC_FIFO_1(GND),
        .WD_1({18{GND}}),
        .WD_0({1'b0, in_reg0[15:8], 1'b0, in_reg0[7:0]}),
        .WIDTH_SELECT1_0(WS1_0),
        .WIDTH_SELECT1_1({GND, GND}),
        .WIDTH_SELECT2_0(WS2_0),
        .WIDTH_SELECT2_1({GND, GND}),
        .WEN1_0({GND, GND}),
        .WEN1_1({GND, GND}),
        .Almost_Empty_0(Almost_Empty),
        .Almost_Empty_1(),
        .Almost_Full_0(Almost_Full),
        .Almost_Full_1(),
        .POP_FLAG_0(POP_FLAG),
        .POP_FLAG_1(),
        .PUSH_FLAG_0(PUSH_FLAG),
        .PUSH_FLAG_1(),
        .RD_0({out_par0[1], out_reg0[15:8], out_par0[0], out_reg0[7:0]}),
        .RD_1(),
        .SD(SD),
        .SD_RB1(SD_RB1),
        .LS(LS),
        .LS_RB1(LS_RB1),
        .DS(DS),
        .DS_RB1(DS_RB1),
        .TEST1A(GND),
        .TEST1B(GND),
        .RMA(4'd0),
        .RMB(4'd0),
        .RMEA(GND),
        .RMEB(GND)
      );

    end else if (data_width_int > 16) begin

      ram8k_2x1_cell_macro #(
        .data_width_int(data_width_int),
        .data_depth_int(data_depth_int)
      ) U2 (
        .A1_0(addr_wr),
        .A1_1(addr_wr),
        .A2_0(addr_rd),
        .A2_1(addr_rd),
        .ASYNC_FLUSH_0(Async_Flush),
        .ASYNC_FLUSH_1(GND),
        .ASYNC_FLUSH_S0(Async_Flush_Sel0),
        .ASYNC_FLUSH_S1(Async_Flush_Sel0),
        .CLK1_0(clk1_sig0),
        .CLK1_1(clk1_sig0),
        .CLK1EN_0(clk1_sig_en0),
        .CLK1EN_1(clk1_sig_en0),
        .CLK2_0(clk2_sig0),
        .CLK2_1(clk2_sig0),
        .CLK1S_0(clk1_sig_sel0),
        .CLK1S_1(clk1_sig_sel0),
        .CLK2S_0(clk2_sig_sel0),
        .CLK2S_1(clk2_sig_sel0),
        .CLK2EN_0(clk2_sig_en0),
        .CLK2EN_1(clk2_sig_en0),
        .CONCAT_EN_0(VCC),
        .CONCAT_EN_1(GND),
        .CS1_0(fifo_clk1_flush_sig0),
        .CS1_1(GND),
        .CS2_0(fifo_clk2_flush_sig0),
        .CS2_1(GND),
        .DIR_0(Fifo_Dir),
        .DIR_1(GND),
        .FIFO_EN_0(VCC),
        .FIFO_EN_1(GND),
        .P1_0(p1_sig0),
        .P1_1(GND),
        .P2_0(p2_sig0),
        .P2_1(GND),
        .PIPELINE_RD_0(reg_rd0),
        .PIPELINE_RD_1(GND),
        .SYNC_FIFO_0(sync_fifo0),
        .SYNC_FIFO_1(GND),
        .WD_1({1'b0, in_reg0[31:24], 1'b0, in_reg0[23:16]}),
        .WD_0({1'b0, in_reg0[15:8], 1'b0, in_reg0[7:0]}),
        .WIDTH_SELECT1_0(WS1_0),
        .WIDTH_SELECT1_1({GND, GND}),
        .WIDTH_SELECT2_0(WS2_0),
        .WIDTH_SELECT2_1({GND, GND}),
        .WEN1_0({GND, GND}),
        .WEN1_1({GND, GND}),
        .Almost_Empty_0(Almost_Empty),
        .Almost_Empty_1(),
        .Almost_Full_0(Almost_Full),
        .Almost_Full_1(),
        .POP_FLAG_0(POP_FLAG),
        .POP_FLAG_1(),
        .PUSH_FLAG_0(PUSH_FLAG),
        .PUSH_FLAG_1(),
        .RD_0({out_par0[1], out_reg0[15:8], out_par0[0], out_reg0[7:0]}),
        .RD_1({out_par0[3], out_reg0[31:24], out_par0[2], out_reg0[23:16]}),
        .SD(SD),
        .SD_RB1(SD_RB1),
        .LS(LS),
        .LS_RB1(LS_RB1),
        .DS(DS),
        .DS_RB1(DS_RB1),
        .TEST1A(GND),
        .TEST1B(GND),
        .RMA(4'd0),
        .RMB(4'd0),
        .RMEA(GND),
        .RMEB(GND)
      );
    end

  endgenerate

  assign DOUT[data_width_int-1 : 0] = out_reg0[data_width_int-1 : 0];

endmodule
