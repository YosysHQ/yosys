//----------------------------------------------------------------------------
// Copyright (C) 2009 , Olivier Girard
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the authors nor the names of its contributors
//       may be used to endorse or promote products derived from this software
//       without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
// OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
// THE POSSIBILITY OF SUCH DAMAGE
//
//----------------------------------------------------------------------------
//
// *File Name: omsp_sfr.v
// 
// *Module Description:
//                       Processor Special function register
//                       Non-Maskable Interrupt generation
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 134 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2012-03-22 21:31:06 +0100 (Thu, 22 Mar 2012) $
//----------------------------------------------------------------------------
`ifdef OMSP_NO_INCLUDE
`else
`include "openMSP430_defines.v"
`endif

module  omsp_sfr (

// OUTPUTs
    cpu_id,                       // CPU ID
    nmi_pnd,                      // NMI Pending
    nmi_wkup,                     // NMI Wakeup
    per_dout,                     // Peripheral data output
    wdtie,                        // Watchdog-timer interrupt enable
    wdtifg_sw_clr,                // Watchdog-timer interrupt flag software clear
    wdtifg_sw_set,                // Watchdog-timer interrupt flag software set

// INPUTs
    mclk,                         // Main system clock
    nmi,                          // Non-maskable interrupt (asynchronous)
    nmi_acc,                      // Non-Maskable interrupt request accepted
    per_addr,                     // Peripheral address
    per_din,                      // Peripheral data input
    per_en,                       // Peripheral enable (high active)
    per_we,                       // Peripheral write enable (high active)
    puc_rst,                      // Main system reset
    scan_mode,                    // Scan mode
    wdtifg,                       // Watchdog-timer interrupt flag
    wdtnmies                      // Watchdog-timer NMI edge selection
);

// OUTPUTs
//=========
output       [31:0] cpu_id;       // CPU ID
output              nmi_pnd;      // NMI Pending
output              nmi_wkup;     // NMI Wakeup
output       [15:0] per_dout;     // Peripheral data output
output              wdtie;        // Watchdog-timer interrupt enable
output              wdtifg_sw_clr;// Watchdog-timer interrupt flag software clear
output              wdtifg_sw_set;// Watchdog-timer interrupt flag software set

// INPUTs
//=========
input               mclk;         // Main system clock
input               nmi;          // Non-maskable interrupt (asynchronous)
input               nmi_acc;      // Non-Maskable interrupt request accepted
input        [13:0] per_addr;     // Peripheral address
input        [15:0] per_din;      // Peripheral data input
input               per_en;       // Peripheral enable (high active)
input         [1:0] per_we;       // Peripheral write enable (high active)
input               puc_rst;      // Main system reset
input               scan_mode;    // Scan mode
input               wdtifg;       // Watchdog-timer interrupt flag
input               wdtnmies;     // Watchdog-timer NMI edge selection


//=============================================================================
// 1)  PARAMETER DECLARATION
//=============================================================================

// Register base address (must be aligned to decoder bit width)
parameter       [14:0] BASE_ADDR   = 15'h0000;

// Decoder bit width (defines how many bits are considered for address decoding)
parameter              DEC_WD      =  3;

// Register addresses offset
parameter [DEC_WD-1:0] IE1         =  'h0,
                       IFG1        =  'h2,
                       CPU_ID_LO   =  'h4,
                       CPU_ID_HI   =  'h6;

// Register one-hot decoder utilities
parameter              DEC_SZ      =  (1 << DEC_WD);
parameter [DEC_SZ-1:0] BASE_REG    =  {{DEC_SZ-1{1'b0}}, 1'b1};

// Register one-hot decoder
parameter [DEC_SZ-1:0] IE1_D       = (BASE_REG << IE1),
                       IFG1_D      = (BASE_REG << IFG1),
                       CPU_ID_LO_D = (BASE_REG << CPU_ID_LO),
                       CPU_ID_HI_D = (BASE_REG << CPU_ID_HI);


//============================================================================
// 2)  REGISTER DECODER
//============================================================================

// Local register selection
wire              reg_sel      =  per_en & (per_addr[13:DEC_WD-1]==BASE_ADDR[14:DEC_WD]);

// Register local address
wire [DEC_WD-1:0] reg_addr     =  {1'b0, per_addr[DEC_WD-2:0]};

// Register address decode
wire [DEC_SZ-1:0] reg_dec      = (IE1_D        &  {DEC_SZ{(reg_addr==(IE1       >>1))}})  |
                                 (IFG1_D       &  {DEC_SZ{(reg_addr==(IFG1      >>1))}})  |
                                 (CPU_ID_LO_D  &  {DEC_SZ{(reg_addr==(CPU_ID_LO >>1))}})  |
                                 (CPU_ID_HI_D  &  {DEC_SZ{(reg_addr==(CPU_ID_HI >>1))}});

// Read/Write probes
wire              reg_lo_write =  per_we[0] & reg_sel;
wire              reg_hi_write =  per_we[1] & reg_sel;
wire              reg_read     = ~|per_we   & reg_sel;

// Read/Write vectors
wire [DEC_SZ-1:0] reg_hi_wr    = reg_dec & {DEC_SZ{reg_hi_write}};
wire [DEC_SZ-1:0] reg_lo_wr    = reg_dec & {DEC_SZ{reg_lo_write}};
wire [DEC_SZ-1:0] reg_rd       = reg_dec & {DEC_SZ{reg_read}};


//============================================================================
// 3) REGISTERS
//============================================================================

// IE1 Register
//--------------
wire [7:0] ie1;
wire       ie1_wr  = IE1[0] ? reg_hi_wr[IE1] : reg_lo_wr[IE1];
wire [7:0] ie1_nxt = IE1[0] ? per_din[15:8]  : per_din[7:0];

`ifdef NMI
reg        nmie;
always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)      nmie  <=  1'b0;
  else if (nmi_acc) nmie  <=  1'b0; 
  else if (ie1_wr)  nmie  <=  ie1_nxt[4];    
`else
wire       nmie  =  1'b0;
`endif

`ifdef WATCHDOG
reg        wdtie;
always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)      wdtie <=  1'b0;
  else if (ie1_wr)  wdtie <=  ie1_nxt[0];    
`else
wire       wdtie =  1'b0;    
`endif

assign  ie1 = {3'b000, nmie, 3'b000, wdtie};


// IFG1 Register
//---------------
wire [7:0] ifg1;

wire       ifg1_wr  = IFG1[0] ? reg_hi_wr[IFG1] : reg_lo_wr[IFG1];
wire [7:0] ifg1_nxt = IFG1[0] ? per_din[15:8]   : per_din[7:0];

`ifdef NMI
reg        nmiifg;
wire       nmi_edge;
always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)       nmiifg <=  1'b0;
  else if (nmi_edge) nmiifg <=  1'b1;
  else if (ifg1_wr)  nmiifg <=  ifg1_nxt[4];
`else
wire       nmiifg = 1'b0;
`endif

`ifdef WATCHDOG
assign  wdtifg_sw_clr = ifg1_wr & ~ifg1_nxt[0];
assign  wdtifg_sw_set = ifg1_wr &  ifg1_nxt[0];
`else
assign  wdtifg_sw_clr = 1'b0;
assign  wdtifg_sw_set = 1'b0;
`endif

assign  ifg1 = {3'b000, nmiifg, 3'b000, wdtifg};


// CPU_ID Register (READ ONLY)
//-----------------------------
//              -------------------------------------------------------------------
// CPU_ID_LO:  | 15  14  13  12  11  10  9  |  8  7  6  5  4  |  3   |   2  1  0   |
//             |----------------------------+-----------------+------+-------------|
//             |        PER_SPACE           |   USER_VERSION  | ASIC | CPU_VERSION |
//              --------------------------------------------------------------------
// CPU_ID_HI:  |   15  14  13  12  11  10   |   9  8  7  6  5  4  3  2  1   |   0  |
//             |----------------------------+-------------------------------+------|
//             |         PMEM_SIZE          |            DMEM_SIZE          |  MPY |
//              -------------------------------------------------------------------

wire  [2:0] cpu_version  =  `CPU_VERSION;
`ifdef ASIC
wire        cpu_asic     =  1'b1;
`else
wire        cpu_asic     =  1'b0;
`endif
wire  [4:0] user_version =  `USER_VERSION;
wire  [6:0] per_space    = (`PER_SIZE  >> 9);  // cpu_id_per  *  512 = peripheral space size
`ifdef MULTIPLIER
wire        mpy_info     =  1'b1;
`else
wire        mpy_info     =  1'b0;
`endif
wire  [8:0] dmem_size    = (`DMEM_SIZE >> 7);  // cpu_id_dmem *  128 = data memory size
wire  [5:0] pmem_size    = (`PMEM_SIZE >> 10); // cpu_id_pmem * 1024 = program memory size

assign      cpu_id       = {pmem_size,
			    dmem_size,
			    mpy_info,
			    per_space,
			    user_version,
			    cpu_asic,
                            cpu_version};


//============================================================================
// 4) DATA OUTPUT GENERATION
//============================================================================

// Data output mux
wire [15:0] ie1_rd        = {8'h00, (ie1  &  {8{reg_rd[IE1]}})}  << (8 & {4{IE1[0]}});
wire [15:0] ifg1_rd       = {8'h00, (ifg1 &  {8{reg_rd[IFG1]}})} << (8 & {4{IFG1[0]}});
wire [15:0] cpu_id_lo_rd  = cpu_id[15:0]  & {16{reg_rd[CPU_ID_LO]}};
wire [15:0] cpu_id_hi_rd  = cpu_id[31:16] & {16{reg_rd[CPU_ID_HI]}};

wire [15:0] per_dout =  ie1_rd       |
                        ifg1_rd      |
                        cpu_id_lo_rd |
                        cpu_id_hi_rd;


//=============================================================================
// 5)  NMI GENERATION
//=============================================================================
// NOTE THAT THE NMI INPUT IS ASSUMED TO BE NON-GLITCHY
`ifdef NMI

//-----------------------------------
// Edge selection
//-----------------------------------
wire nmi_pol = nmi ^ wdtnmies;

//-----------------------------------
// Pulse capture and synchronization
//-----------------------------------
`ifdef SYNC_NMI
  `ifdef ASIC
   // Glitch free reset for the event capture
   reg    nmi_capture_rst;
   always @(posedge mclk or posedge puc_rst)
     if (puc_rst) nmi_capture_rst <= 1'b1;
     else         nmi_capture_rst <= ifg1_wr & ~ifg1_nxt[4];
 
   // NMI event capture
   wire   nmi_capture;
   omsp_wakeup_cell wakeup_cell_nmi (
				     .wkup_out   (nmi_capture),     // Wakup signal (asynchronous)
				     .scan_clk   (mclk),            // Scan clock
				     .scan_mode  (scan_mode),       // Scan mode
				     .scan_rst   (puc_rst),         // Scan reset
				     .wkup_clear (nmi_capture_rst), // Glitch free wakeup event clear
				     .wkup_event (nmi_pol)          // Glitch free asynchronous wakeup event
   );
  `else
   wire   nmi_capture = nmi_pol;
  `endif

   // Synchronization
   wire   nmi_s;
   omsp_sync_cell sync_cell_nmi (
       .data_out  (nmi_s),
       .data_in   (nmi_capture),
       .clk       (mclk),
       .rst       (puc_rst)
   );

`else
   wire   nmi_capture = nmi_pol;
   wire   nmi_s       = nmi_pol;
`endif

//-----------------------------------
// NMI Pending flag
//-----------------------------------

// Delay
reg  nmi_dly;
always @ (posedge mclk or posedge puc_rst)
  if (puc_rst) nmi_dly <= 1'b0;
  else         nmi_dly <= nmi_s;

// Edge detection
assign      nmi_edge  = ~nmi_dly & nmi_s;

// NMI pending
wire        nmi_pnd   = nmiifg & nmie;

// NMI wakeup
`ifdef ASIC
wire        nmi_wkup;
omsp_and_gate and_nmi_wkup (.y(nmi_wkup), .a(nmi_capture ^ nmi_dly), .b(nmie));
`else
wire        nmi_wkup  = 1'b0;
`endif

`else

wire        nmi_pnd   = 1'b0;
wire        nmi_wkup  = 1'b0;

`endif

endmodule // omsp_sfr

`ifdef OMSP_NO_INCLUDE
`else
`include "openMSP430_undefines.v"
`endif
