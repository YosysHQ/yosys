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
// *File Name: omsp_clock_module.v
// 
// *Module Description:
//                       Basic clock module implementation.
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

module  omsp_clock_module (

// OUTPUTs
    aclk,                         // ACLK
    aclk_en,                      // ACLK enable
    cpu_en_s,                     // Enable CPU code execution (synchronous)
    dbg_clk,                      // Debug unit clock
    dbg_en_s,                     // Debug interface enable (synchronous)
    dbg_rst,                      // Debug unit reset
    dco_enable,                   // Fast oscillator enable
    dco_wkup,                     // Fast oscillator wake-up (asynchronous)
    lfxt_enable,                  // Low frequency oscillator enable
    lfxt_wkup,                    // Low frequency oscillator wake-up (asynchronous)
    mclk,                         // Main system clock
    per_dout,                     // Peripheral data output
    por,                          // Power-on reset
    puc_pnd_set,                  // PUC pending set for the serial debug interface
    puc_rst,                      // Main system reset
    smclk,                        // SMCLK
    smclk_en,                     // SMCLK enable
	     
// INPUTs
    cpu_en,                       // Enable CPU code execution (asynchronous)
    cpuoff,                       // Turns off the CPU
    dbg_cpu_reset,                // Reset CPU from debug interface
    dbg_en,                       // Debug interface enable (asynchronous)
    dco_clk,                      // Fast oscillator (fast clock)
    lfxt_clk,                     // Low frequency oscillator (typ 32kHz)
    mclk_enable,                  // Main System Clock enable
    mclk_wkup,                    // Main System Clock wake-up (asynchronous)
    oscoff,                       // Turns off LFXT1 clock input
    per_addr,                     // Peripheral address
    per_din,                      // Peripheral data input
    per_en,                       // Peripheral enable (high active)
    per_we,                       // Peripheral write enable (high active)
    reset_n,                      // Reset Pin (low active, asynchronous)
    scan_enable,                  // Scan enable (active during scan shifting)
    scan_mode,                    // Scan mode
    scg0,                         // System clock generator 1. Turns off the DCO
    scg1,                         // System clock generator 1. Turns off the SMCLK
    wdt_reset                     // Watchdog-timer reset
);

// OUTPUTs
//=========
output              aclk;         // ACLK
output              aclk_en;      // ACLK enable
output              cpu_en_s;     // Enable CPU code execution (synchronous)
output              dbg_clk;      // Debug unit clock
output              dbg_en_s;     // Debug unit enable (synchronous)
output              dbg_rst;      // Debug unit reset
output              dco_enable;   // Fast oscillator enable
output              dco_wkup;     // Fast oscillator wake-up (asynchronous)
output              lfxt_enable;  // Low frequency oscillator enable
output              lfxt_wkup;    // Low frequency oscillator wake-up (asynchronous)
output              mclk;         // Main system clock
output       [15:0] per_dout;     // Peripheral data output
output              por;          // Power-on reset
output              puc_pnd_set;  // PUC pending set for the serial debug interface
output              puc_rst;      // Main system reset
output              smclk;        // SMCLK
output              smclk_en;     // SMCLK enable

// INPUTs
//=========
input               cpu_en;       // Enable CPU code execution (asynchronous)
input               cpuoff;       // Turns off the CPU
input               dbg_cpu_reset;// Reset CPU from debug interface
input               dbg_en;       // Debug interface enable (asynchronous)
input               dco_clk;      // Fast oscillator (fast clock)
input               lfxt_clk;     // Low frequency oscillator (typ 32kHz)
input               mclk_enable;  // Main System Clock enable
input               mclk_wkup;    // Main System Clock wake-up (asynchronous)
input               oscoff;       // Turns off LFXT1 clock input
input        [13:0] per_addr;     // Peripheral address
input        [15:0] per_din;      // Peripheral data input
input               per_en;       // Peripheral enable (high active)
input         [1:0] per_we;       // Peripheral write enable (high active)
input               reset_n;      // Reset Pin (low active, asynchronous)
input               scan_enable;  // Scan enable (active during scan shifting)
input               scan_mode;    // Scan mode
input               scg0;         // System clock generator 1. Turns off the DCO
input               scg1;         // System clock generator 1. Turns off the SMCLK
input               wdt_reset;    // Watchdog-timer reset


//=============================================================================
// 1)  WIRES & PARAMETER DECLARATION
//=============================================================================

// Register base address (must be aligned to decoder bit width)
parameter       [14:0] BASE_ADDR   = 15'h0050;

// Decoder bit width (defines how many bits are considered for address decoding)
parameter              DEC_WD      =  4;

// Register addresses offset
parameter [DEC_WD-1:0] BCSCTL1     =  'h7,
                       BCSCTL2     =  'h8;

// Register one-hot decoder utilities
parameter              DEC_SZ      =  (1 << DEC_WD);
parameter [DEC_SZ-1:0] BASE_REG    =  {{DEC_SZ-1{1'b0}}, 1'b1};

// Register one-hot decoder
parameter [DEC_SZ-1:0] BCSCTL1_D   = (BASE_REG << BCSCTL1),
                       BCSCTL2_D   = (BASE_REG << BCSCTL2);

// Local wire declarations
wire nodiv_mclk;
wire nodiv_mclk_n;
wire nodiv_smclk;


//============================================================================
// 2)  REGISTER DECODER
//============================================================================

// Local register selection
wire              reg_sel      =  per_en & (per_addr[13:DEC_WD-1]==BASE_ADDR[14:DEC_WD]);

// Register local address
wire [DEC_WD-1:0] reg_addr     =  {1'b0, per_addr[DEC_WD-2:0]};

// Register address decode
wire [DEC_SZ-1:0] reg_dec      = (BCSCTL1_D  &  {DEC_SZ{(reg_addr==(BCSCTL1 >>1))}}) |
                                 (BCSCTL2_D  &  {DEC_SZ{(reg_addr==(BCSCTL2 >>1))}});

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

// BCSCTL1 Register
//--------------
reg  [7:0] bcsctl1;
wire       bcsctl1_wr  = BCSCTL1[0] ? reg_hi_wr[BCSCTL1] : reg_lo_wr[BCSCTL1];
wire [7:0] bcsctl1_nxt = BCSCTL1[0] ? per_din[15:8]      : per_din[7:0];

`ifdef ASIC
  `ifdef ACLK_DIVIDER
wire [7:0] divax_mask = 8'h30;
  `else
wire [7:0] divax_mask = 8'h00;
  `endif
`else
wire [7:0] divax_mask = 8'h30;
`endif

always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)          bcsctl1  <=  8'h00;
  else if (bcsctl1_wr)  bcsctl1  <=  bcsctl1_nxt & divax_mask; // Mask unused bits


// BCSCTL2 Register
//--------------
reg  [7:0] bcsctl2;
wire       bcsctl2_wr    = BCSCTL2[0] ? reg_hi_wr[BCSCTL2] : reg_lo_wr[BCSCTL2];
wire [7:0] bcsctl2_nxt   = BCSCTL2[0] ? per_din[15:8]      : per_din[7:0];

`ifdef MCLK_MUX
wire [7:0] selmx_mask = 8'h80;
`else
wire [7:0] selmx_mask = 8'h00;
`endif
`ifdef MCLK_DIVIDER
wire [7:0] divmx_mask = 8'h30;
`else
wire [7:0] divmx_mask = 8'h00;
`endif
`ifdef ASIC
  `ifdef SMCLK_MUX
wire [7:0] sels_mask  = 8'h08;
  `else
wire [7:0] sels_mask  = 8'h00;
  `endif
  `ifdef SMCLK_DIVIDER
wire [7:0] divsx_mask = 8'h06;
  `else
wire [7:0] divsx_mask = 8'h00;
  `endif
`else
wire [7:0] sels_mask  = 8'h08;
wire [7:0] divsx_mask = 8'h06;
`endif

always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)          bcsctl2  <=  8'h00;
  else if (bcsctl2_wr)  bcsctl2  <=  bcsctl2_nxt & ( sels_mask  | divsx_mask |
                                                     selmx_mask | divmx_mask); // Mask unused bits


//============================================================================
// 4) DATA OUTPUT GENERATION
//============================================================================

// Data output mux
wire [15:0] bcsctl1_rd   = {8'h00, (bcsctl1  & {8{reg_rd[BCSCTL1]}})}  << (8 & {4{BCSCTL1[0]}});
wire [15:0] bcsctl2_rd   = {8'h00, (bcsctl2  & {8{reg_rd[BCSCTL2]}})}  << (8 & {4{BCSCTL2[0]}});

wire [15:0] per_dout =  bcsctl1_rd   |
                        bcsctl2_rd;


//=============================================================================
// 5)  DCO_CLK / LFXT_CLK INTERFACES (WAKEUP, ENABLE, ...)
//=============================================================================

`ifdef ASIC
   wire cpuoff_and_mclk_enable;
   omsp_and_gate and_cpuoff_mclk_en (.y(cpuoff_and_mclk_enable), .a(cpuoff), .b(mclk_enable));
`endif

//-----------------------------------------------------------
// 5.1) HIGH SPEED SYSTEM CLOCK GENERATOR (DCO_CLK)
//-----------------------------------------------------------
// Note1: switching off the DCO osillator is only
//        supported in ASIC mode with SCG0 low power mode
//
// Note2: unlike the original MSP430 specification,
//        we allow to switch off the DCO even
//        if it is selected by MCLK or SMCLK.

wire por_a;
wire dco_wkup;
wire cpu_en_wkup;

`ifdef SCG0_EN

   // The DCO oscillator is synchronously disabled if:
   //      - the cpu pin is disabled (in that case, wait for mclk_enable==0)
   //      - the debug interface is disabled
   //      - SCG0 is set (in that case, wait for the mclk_enable==0 if selected by SELMx)
   //
   // Note that we make extensive use of the AND gate module in order
   // to prevent glitch propagation on the wakeup logic cone.
   wire cpu_enabled_with_dco;
   wire dco_not_enabled_by_dbg;
   wire dco_disable_by_scg0;
   wire dco_disable_by_cpu_en;
   wire dco_enable_nxt;
   omsp_and_gate and_dco_dis1 (.y(cpu_enabled_with_dco),   .a(~bcsctl2[`SELMx]),     .b(cpuoff_and_mclk_enable));
   omsp_and_gate and_dco_dis2 (.y(dco_not_enabled_by_dbg), .a(~dbg_en_s),            .b(~cpu_enabled_with_dco));
   omsp_and_gate and_dco_dis3 (.y(dco_disable_by_scg0),    .a(scg0),                 .b(dco_not_enabled_by_dbg));
   omsp_and_gate and_dco_dis4 (.y(dco_disable_by_cpu_en),  .a(~cpu_en_s),            .b(~mclk_enable));
   omsp_and_gate and_dco_dis5 (.y(dco_enable_nxt),         .a(~dco_disable_by_scg0), .b(~dco_disable_by_cpu_en));

   // Register to prevent glitch propagation
   reg  dco_disable;
   always @(posedge nodiv_mclk_n or posedge por)
   if (por) dco_disable <= 1'b1;
   else     dco_disable <= ~dco_enable_nxt;

   // Note that a synchronizer is required if the MCLK mux is included
   wire dco_clk_n  = ~dco_clk;
   `ifdef MCLK_MUX
      omsp_sync_cell sync_cell_dco_disable (
         .data_out  (dco_enable),
         .data_in   (~dco_disable),
         .clk       (dco_clk_n),
         .rst       (por)
      );
   `else

      assign dco_enable     = ~dco_disable;
   `endif

   // The DCO oscillator will get an asynchronous wakeup if:
   //      - the MCLK  generates a wakeup (only if the MCLK mux selects dco_clk)
   //      - if the DCO wants to be synchronously enabled (i.e dco_enable_nxt=1)
   wire dco_mclk_wkup;
   wire dco_en_wkup;
   omsp_and_gate and_dco_mclk_wkup (.y(dco_mclk_wkup), .a(mclk_wkup),   .b(~bcsctl2[`SELMx]));
   omsp_and_gate and_dco_en_wkup   (.y(dco_en_wkup),   .a(~dco_enable), .b(dco_enable_nxt));

   wire dco_wkup_set = dco_mclk_wkup | dco_en_wkup | cpu_en_wkup;

   // Scan MUX for the asynchronous SET
   wire dco_wkup_set_scan;
   omsp_scan_mux scan_mux_dco_wkup (
				    .scan_mode    (scan_mode),
				    .data_in_scan (por_a),
				    .data_in_func (dco_wkup_set | por),
				    .data_out     (dco_wkup_set_scan)
			           );

   // Scan MUX to increase coverage 
   wire dco_wkup_clear;
   omsp_scan_mux scan_mux_dco_wkup_clear (
			  	          .scan_mode    (scan_mode),
				          .data_in_scan (dco_wkup_set),
				          .data_in_func (1'b1),
		 		          .data_out     (dco_wkup_clear)
			                 );

   // The wakeup is asynchronously set, synchronously released
   wire dco_wkup_n;
   omsp_sync_cell sync_cell_dco_wkup (
       .data_out  (dco_wkup_n),
       .data_in   (dco_wkup_clear),
       .clk       (dco_clk_n),
       .rst       (dco_wkup_set_scan)
   );

   omsp_and_gate and_dco_wkup (.y(dco_wkup), .a(~dco_wkup_n), .b(cpu_en));

`else
   assign dco_enable    = 1'b1;
   assign dco_wkup      = 1'b1;
`endif


//-----------------------------------------------------------
// 5.2) LOW FREQUENCY CRYSTAL CLOCK GENERATOR (LFXT_CLK)
//-----------------------------------------------------------

// ASIC MODE
//------------------------------------------------
// Note: unlike the original MSP430 specification,
//       we allow to switch off the LFXT even
//       if it is selected by MCLK or SMCLK.
`ifdef ASIC

`ifdef OSCOFF_EN

   // The LFXT is synchronously disabled if:
   //      - the cpu pin is disabled (in that case, wait for mclk_enable==0)
   //      - the debug interface is disabled
   //      - OSCOFF is set (in that case, wait for the mclk_enable==0 if selected by SELMx)
   wire cpu_enabled_with_lfxt;
   wire lfxt_not_enabled_by_dbg;
   wire lfxt_disable_by_oscoff;
   wire lfxt_disable_by_cpu_en;
   wire lfxt_enable_nxt;
   omsp_and_gate and_lfxt_dis1 (.y(cpu_enabled_with_lfxt),   .a(bcsctl2[`SELMx]),         .b(cpuoff_and_mclk_enable));
   omsp_and_gate and_lfxt_dis2 (.y(lfxt_not_enabled_by_dbg), .a(~dbg_en_s),               .b(~cpu_enabled_with_lfxt));
   omsp_and_gate and_lfxt_dis3 (.y(lfxt_disable_by_oscoff),  .a(oscoff),                  .b(lfxt_not_enabled_by_dbg));
   omsp_and_gate and_lfxt_dis4 (.y(lfxt_disable_by_cpu_en),  .a(~cpu_en_s),               .b(~mclk_enable));
   omsp_and_gate and_lfxt_dis5 (.y(lfxt_enable_nxt),         .a(~lfxt_disable_by_oscoff), .b(~lfxt_disable_by_cpu_en));

   // Register to prevent glitch propagation
   reg  lfxt_disable;
   always @(posedge nodiv_mclk_n or posedge por)
   if (por) lfxt_disable <= 1'b1;
   else     lfxt_disable <= ~lfxt_enable_nxt;

   // Synchronize the OSCOFF control signal to the LFXT clock domain
   wire lfxt_clk_n  = ~lfxt_clk;
   omsp_sync_cell sync_cell_lfxt_disable (
      .data_out  (lfxt_enable),
      .data_in   (~lfxt_disable),
      .clk       (lfxt_clk_n),
      .rst       (por)
   );

   // The LFXT will get an asynchronous wakeup if:
   //      - the MCLK  generates a wakeup (only if the MCLK  mux selects lfxt_clk)
   //      - if the LFXT wants to be synchronously enabled (i.e lfxt_enable_nxt=1)
   wire lfxt_mclk_wkup;
   wire lfxt_en_wkup;
   omsp_and_gate and_lfxt_mclk_wkup (.y(lfxt_mclk_wkup), .a(mclk_wkup),    .b(bcsctl2[`SELMx]));
   omsp_and_gate and_lfxt_en_wkup   (.y(lfxt_en_wkup),   .a(~lfxt_enable), .b(lfxt_enable_nxt));

   wire   lfxt_wkup_set  = lfxt_mclk_wkup | lfxt_en_wkup | cpu_en_wkup;

   // Scan MUX for the asynchronous SET
   wire lfxt_wkup_set_scan;
   omsp_scan_mux scan_mux_lfxt_wkup (
				     .scan_mode    (scan_mode),
				     .data_in_scan (por_a),
				     .data_in_func (lfxt_wkup_set | por),
				     .data_out     (lfxt_wkup_set_scan)
			            );

   // Scan MUX to increase coverage 
   wire lfxt_wkup_clear;
   omsp_scan_mux scan_mux_lfxt_wkup_clear (
			  	           .scan_mode    (scan_mode),
				           .data_in_scan (lfxt_wkup_set),
				           .data_in_func (1'b1),
		 		           .data_out     (lfxt_wkup_clear)
			                  );

   // The wakeup is asynchronously set, synchronously released
   wire lfxt_wkup_n;
   omsp_sync_cell sync_cell_lfxt_wkup (
       .data_out  (lfxt_wkup_n),
       .data_in   (lfxt_wkup_clear),
       .clk       (lfxt_clk_n),
       .rst       (lfxt_wkup_set_scan)
   );

   omsp_and_gate and_lfxt_wkup (.y(lfxt_wkup), .a(~lfxt_wkup_n), .b(cpu_en));

`else
   assign lfxt_enable    = 1'b1;
   assign lfxt_wkup      = 1'b0;
`endif


// FPGA MODE
//---------------------------------------
// Synchronize LFXT_CLK & edge detection
`else

wire lfxt_clk_s;

omsp_sync_cell sync_cell_lfxt_clk (
    .data_out  (lfxt_clk_s),
    .data_in   (lfxt_clk),
    .clk       (mclk),
    .rst       (por)
);

reg  lfxt_clk_dly;
   
always @ (posedge mclk or posedge por)
  if (por) lfxt_clk_dly <=  1'b0;
  else     lfxt_clk_dly <=  lfxt_clk_s;    

wire   lfxt_clk_en = (lfxt_clk_s & ~lfxt_clk_dly) & ~(oscoff & ~bcsctl2[`SELS]);
assign lfxt_enable = 1'b1;
assign lfxt_wkup   = 1'b0;
`endif     

   
//=============================================================================
// 6)  CLOCK GENERATION
//=============================================================================

//-----------------------------------------------------------
// 6.1) GLOBAL CPU ENABLE
//-----------------------------------------------------------
// ACLK and SMCLK are directly switched-off
// with the cpu_en pin (after synchronization).
// MCLK will be switched off once the CPU reaches
// its IDLE state (through the mclk_enable signal)


// Synchronize CPU_EN signal to the MCLK domain
//----------------------------------------------
`ifdef SYNC_CPU_EN
   omsp_sync_cell sync_cell_cpu_en (
      .data_out  (cpu_en_s),
      .data_in   (cpu_en),
      .clk       (nodiv_mclk),
      .rst       (por)
   );
   omsp_and_gate and_cpu_en_wkup (.y(cpu_en_wkup), .a(cpu_en), .b(~cpu_en_s));
`else
   assign cpu_en_s    = cpu_en;
   assign cpu_en_wkup = 1'b0;
`endif

// Synchronize CPU_EN signal to the ACLK domain
//----------------------------------------------
`ifdef LFXT_DOMAIN
   wire cpu_en_aux_s;
   omsp_sync_cell sync_cell_cpu_aux_en (
      .data_out  (cpu_en_aux_s),
      .data_in   (cpu_en),
      .clk       (lfxt_clk),
      .rst       (por)
   );
`else
   wire   cpu_en_aux_s    = cpu_en_s;
`endif

// Synchronize CPU_EN signal to the SMCLK domain
//----------------------------------------------
// Note: the synchronizer is only required if there is a SMCLK_MUX
`ifdef ASIC
  `ifdef SMCLK_MUX
     wire cpu_en_sm_s;
     omsp_sync_cell sync_cell_cpu_sm_en (
        .data_out  (cpu_en_sm_s),
        .data_in   (cpu_en),
        .clk       (nodiv_smclk),
        .rst       (por)
     );
  `else
   wire   cpu_en_sm_s    = cpu_en_s;
  `endif
`endif


//-----------------------------------------------------------
// 6.2) MCLK GENERATION
//-----------------------------------------------------------

// Clock MUX
//----------------------------
`ifdef MCLK_MUX
omsp_clock_mux clock_mux_mclk (
   .clk_out   (nodiv_mclk),
   .clk_in0   (dco_clk),
   .clk_in1   (lfxt_clk),
   .reset     (por),
   .scan_mode (scan_mode),
   .select    (bcsctl2[`SELMx])
);
`else
assign nodiv_mclk   =  dco_clk;
`endif
assign nodiv_mclk_n = ~nodiv_mclk;
   

// Wakeup synchronizer
//----------------------------
wire mclk_wkup_s;

`ifdef CPUOFF_EN
omsp_sync_cell sync_cell_mclk_wkup (
   .data_out  (mclk_wkup_s),
   .data_in   (mclk_wkup),
   .clk       (nodiv_mclk),
   .rst       (puc_rst)
);
`else
   assign mclk_wkup_s = 1'b0;
`endif


// Clock Divider
//----------------------------
// No need for extra synchronizer as bcsctl2
// comes from the same clock domain.

`ifdef CPUOFF_EN
wire mclk_active = mclk_enable | mclk_wkup_s | (dbg_en_s & cpu_en_s);
`else
wire mclk_active = 1'b1;
`endif
   
`ifdef MCLK_DIVIDER
reg [2:0] mclk_div;
always @ (posedge nodiv_mclk or posedge puc_rst)
  if (puc_rst)                       mclk_div <=  3'h0;
  else if ((bcsctl2[`DIVMx]!=2'b00)) mclk_div <=  mclk_div+3'h1;

  wire  mclk_div_en = mclk_active & ((bcsctl2[`DIVMx]==2'b00) ?  1'b1          :
                                     (bcsctl2[`DIVMx]==2'b01) ?  mclk_div[0]   :
                                     (bcsctl2[`DIVMx]==2'b10) ? &mclk_div[1:0] :
                                                                &mclk_div[2:0]);
`else
  wire  mclk_div_en = mclk_active;
`endif


// Generate main system clock
//----------------------------
`ifdef MCLK_CGATE

omsp_clock_gate clock_gate_mclk (
    .gclk        (mclk),
    .clk         (nodiv_mclk),
    .enable      (mclk_div_en),
    .scan_enable (scan_enable)
);
`else
   assign mclk   = nodiv_mclk;
`endif


//-----------------------------------------------------------
// 6.3) ACLK GENERATION
//-----------------------------------------------------------

// ASIC MODE
//----------------------------
`ifdef ASIC

  `ifdef ACLK_DIVIDER
    `ifdef LFXT_DOMAIN

   wire nodiv_aclk = lfxt_clk;

   // Local Reset synchronizer
   wire puc_lfxt_rst;
   wire puc_lfxt_noscan_n;
   omsp_sync_cell sync_cell_puc_lfxt (
       .data_out     (puc_lfxt_noscan_n),
       .data_in      (1'b1),
       .clk          (nodiv_aclk),
       .rst          (puc_rst)
   );
   omsp_scan_mux scan_mux_puc_lfxt (
       .scan_mode    (scan_mode),
       .data_in_scan (por_a),
       .data_in_func (~puc_lfxt_noscan_n),
       .data_out     (puc_lfxt_rst)
   );

   // Local synchronizer for the bcsctl1.DIVAx configuration
   // (note that we can live with a full bus synchronizer as
   //  it won't hurt if we get a wrong DIVAx value for a single clock cycle)
   reg [1:0] divax_s;
   reg [1:0] divax_ss;
   always @ (posedge nodiv_aclk or posedge puc_lfxt_rst)
     if (puc_lfxt_rst)
       begin
	  divax_s  <=  2'h0;
	  divax_ss <=  2'h0;
       end
     else
       begin
	  divax_s  <=  bcsctl1[`DIVAx];
	  divax_ss <=  divax_s;
       end

     // If the OSCOFF mode is enabled synchronize OSCOFF signal
     wire oscoff_s;
     `ifdef OSCOFF_EN
         omsp_sync_cell sync_cell_oscoff (
           .data_out     (oscoff_s),
           .data_in      (oscoff),
           .clk          (nodiv_aclk),
           .rst          (puc_lfxt_rst)
         );
     `else
     assign oscoff_s = 1'b0;
     `endif
  `else
   wire       puc_lfxt_rst = puc_rst;
   wire       nodiv_aclk   = dco_clk;
   wire [1:0] divax_ss     = bcsctl1[`DIVAx];
   wire       oscoff_s     = oscoff;
  `endif   

   // Divider
   reg [2:0] aclk_div;
   always @ (posedge nodiv_aclk or posedge puc_lfxt_rst)
     if (puc_lfxt_rst)           aclk_div <=  3'h0;
     else if ((divax_ss!=2'b00)) aclk_div <=  aclk_div+3'h1;

   wire      aclk_div_en =  cpu_en_aux_s & ~oscoff_s & ((divax_ss==2'b00) ?  1'b1          :
                                                        (divax_ss==2'b01) ?  aclk_div[0]   :
                                                        (divax_ss==2'b10) ? &aclk_div[1:0] :
                                                                            &aclk_div[2:0]);

   // Clock gate
   omsp_clock_gate clock_gate_aclk (
      .gclk        (aclk),
      .clk         (nodiv_aclk),
      .enable      (aclk_div_en),
      .scan_enable (scan_enable)
   );

 `else
    `ifdef LFXT_DOMAIN
    assign  aclk    = lfxt_clk;
    `else
    assign  aclk    = dco_clk;
    `endif
  `endif
   

    assign  aclk_en = 1'b1;


// FPGA MODE
//----------------------------
`else
  reg       aclk_en;
  reg [2:0] aclk_div;
  wire      aclk_en_nxt =  lfxt_clk_en & ((bcsctl1[`DIVAx]==2'b00) ?  1'b1          :
                                          (bcsctl1[`DIVAx]==2'b01) ?  aclk_div[0]   :
                                          (bcsctl1[`DIVAx]==2'b10) ? &aclk_div[1:0] :
                                                                     &aclk_div[2:0]);

  always @ (posedge mclk or posedge puc_rst)
    if (puc_rst)                                     aclk_div <=  3'h0;
    else if ((bcsctl1[`DIVAx]!=2'b00) & lfxt_clk_en) aclk_div <=  aclk_div+3'h1;

  always @ (posedge mclk or posedge puc_rst)
    if (puc_rst)  aclk_en <=  1'b0;
    else          aclk_en <=  aclk_en_nxt & cpu_en_s;

  assign  aclk   = mclk;
`endif
   
//-----------------------------------------------------------
// 6.4) SMCLK GENERATION
//-----------------------------------------------------------

// Clock MUX
//----------------------------
`ifdef SMCLK_MUX
omsp_clock_mux clock_mux_smclk (
   .clk_out   (nodiv_smclk),
   .clk_in0   (dco_clk),
   .clk_in1   (lfxt_clk),
   .reset     (por),
   .scan_mode (scan_mode),
   .select    (bcsctl2[`SELS])
);
`else
assign nodiv_smclk = dco_clk;
`endif


// ASIC MODE
//----------------------------
`ifdef ASIC
  `ifdef SMCLK_MUX

    // Synchronizers
    //------------------------------------------------------
    // When the SMCLK MUX is enabled, the reset and DIVSx
    // and SCG1 signals must be synchronized, otherwise not.
   
     // Local Reset synchronizer
     wire puc_sm_noscan_n;
     wire puc_sm_rst;
     omsp_sync_cell sync_cell_puc_sm (
         .data_out     (puc_sm_noscan_n),
         .data_in      (1'b1),
         .clk          (nodiv_smclk),
         .rst          (puc_rst)
     );
     omsp_scan_mux scan_mux_puc_sm (
         .scan_mode    (scan_mode),
         .data_in_scan (por_a),
         .data_in_func (~puc_sm_noscan_n),
         .data_out     (puc_sm_rst)
     );

     // SCG1 synchronizer
     `ifdef SCG1_EN
     wire scg1_s;
     omsp_sync_cell sync_cell_scg1 (
         .data_out     (scg1_s),
         .data_in      (scg1),
         .clk          (nodiv_smclk),
         .rst          (puc_sm_rst)
     );
     `else
     wire scg1_s = 1'b0;
     `endif

    `ifdef SMCLK_DIVIDER
     // Local synchronizer for the bcsctl2.DIVSx configuration
     // (note that we can live with a full bus synchronizer as
     //  it won't hurt if we get a wrong DIVSx value for a single clock cycle)
     reg [1:0] divsx_s;
     reg [1:0] divsx_ss;
     always @ (posedge nodiv_smclk or posedge puc_sm_rst)
       if (puc_sm_rst)
         begin
  	    divsx_s  <=  2'h0;
	    divsx_ss <=  2'h0;
	 end
       else
	 begin
	    divsx_s  <=  bcsctl2[`DIVSx];
	    divsx_ss <=  divsx_s;
	 end
    `endif
   
   `else
   
      wire       puc_sm_rst   = puc_rst;
      wire [1:0] divsx_ss     = bcsctl2[`DIVSx];
      wire       scg1_s       = scg1;
  `endif
   
   

   // Clock Divider
   //----------------------------
 `ifdef SMCLK_DIVIDER

   reg [2:0] smclk_div;
   always @ (posedge nodiv_smclk or posedge puc_sm_rst)
     if (puc_sm_rst)             smclk_div <=  3'h0;
     else if ((divsx_ss!=2'b00)) smclk_div <=  smclk_div+3'h1;

   wire  smclk_div_en = cpu_en_sm_s & ~scg1_s & ((divsx_ss==2'b00) ?  1'b1           :
                                                 (divsx_ss==2'b01) ?  smclk_div[0]   :
                                                 (divsx_ss==2'b10) ? &smclk_div[1:0] :
                                                                     &smclk_div[2:0]);
 `else
   `ifdef SCG1_EN
    wire smclk_div_en = cpu_en_sm_s & ~scg1_s;
   `else
    wire smclk_div_en = cpu_en_sm_s;
   `endif
 `endif
   

   // Generate sub-system clock
   //----------------------------
 `ifdef SMCLK_CGATE
   omsp_clock_gate clock_gate_smclk (
      .gclk        (smclk),
      .clk         (nodiv_smclk),
      .enable      (smclk_div_en),
      .scan_enable (scan_enable)
   );
 `else
   assign  smclk    = nodiv_smclk;
 `endif
   
   assign  smclk_en = 1'b1;


// FPGA MODE
//----------------------------
`else
reg       smclk_en;
reg [2:0] smclk_div;

wire      smclk_in     = ~scg1 & (bcsctl2[`SELS] ? lfxt_clk_en : 1'b1);

wire      smclk_en_nxt = smclk_in & ((bcsctl2[`DIVSx]==2'b00) ?  1'b1           :
                                     (bcsctl2[`DIVSx]==2'b01) ?  smclk_div[0]   :
                                     (bcsctl2[`DIVSx]==2'b10) ? &smclk_div[1:0] :
                                                                &smclk_div[2:0]);
   
always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)  smclk_en <=  1'b0;
  else          smclk_en <=  smclk_en_nxt & cpu_en_s;

always @ (posedge mclk or posedge puc_rst)
  if (puc_rst)                                  smclk_div <=  3'h0;
  else if ((bcsctl2[`DIVSx]!=2'b00) & smclk_in) smclk_div <=  smclk_div+3'h1;

wire  smclk  = mclk;

`endif

//-----------------------------------------------------------
// 6.5) DEBUG INTERFACE CLOCK GENERATION (DBG_CLK)
//-----------------------------------------------------------

// Synchronize DBG_EN signal to MCLK domain
//------------------------------------------
`ifdef DBG_EN
`ifdef SYNC_DBG_EN
    wire dbg_en_n_s;
    omsp_sync_cell sync_cell_dbg_en (
       .data_out  (dbg_en_n_s),
       .data_in   (~dbg_en),
       .clk       (mclk),
       .rst       (por)
    );
    assign dbg_en_s    = ~dbg_en_n_s;
    wire   dbg_rst_nxt =  dbg_en_n_s;
`else
    assign dbg_en_s    =  dbg_en;
    wire   dbg_rst_nxt = ~dbg_en;
`endif
`else
    assign dbg_en_s    =  1'b0;
    wire   dbg_rst_nxt =  1'b0;
`endif


// Serial Debug Interface Clock gate
//------------------------------------------------
`ifdef DBG_EN
  `ifdef ASIC
  omsp_clock_gate clock_gate_dbg_clk (
      .gclk        (dbg_clk),
      .clk         (mclk),
      .enable      (dbg_en_s),
      .scan_enable (scan_enable)
  );
  `else
     assign dbg_clk = dco_clk;
  `endif
`else
     assign dbg_clk = 1'b0;
`endif


//=============================================================================
// 7)  RESET GENERATION
//=============================================================================
//
// Whenever the reset pin (reset_n) is deasserted, the internal resets of the
// openMSP430 will be released in the following order:
//                1- POR
//                2- DBG_RST (if the sdi interface is enabled, i.e. dbg_en=1)
//                3- PUC
//
// Note: releasing the DBG_RST before PUC is particularly important in order
//       to allow the sdi interface to halt the cpu immediately after a PUC.
//
   
// Generate synchronized POR to MCLK domain
//------------------------------------------

// Asynchronous reset source
assign    por_a         =  !reset_n;
wire      por_noscan;

// Reset Synchronizer
omsp_sync_reset sync_reset_por (
    .rst_s        (por_noscan),
    .clk          (nodiv_mclk),
    .rst_a        (por_a)
);

// Scan Reset Mux
`ifdef ASIC
omsp_scan_mux scan_mux_por (
    .scan_mode    (scan_mode),
    .data_in_scan (por_a),
    .data_in_func (por_noscan),
    .data_out     (por)
);
`else
 assign por = por_noscan;
`endif

// Generate synchronized reset for the SDI
//------------------------------------------
`ifdef DBG_EN

// Reset Generation
reg  dbg_rst_noscan;
always @ (posedge mclk or posedge por)
  if (por)  dbg_rst_noscan <=  1'b1;
  else      dbg_rst_noscan <=  dbg_rst_nxt;

  // Scan Reset Mux
  `ifdef ASIC
  omsp_scan_mux scan_mux_dbg_rst (
      .scan_mode    (scan_mode),
      .data_in_scan (por_a),
      .data_in_func (dbg_rst_noscan),
      .data_out     (dbg_rst)
  );
  `else
   assign dbg_rst = dbg_rst_noscan;
  `endif

`else
   wire   dbg_rst_noscan = 1'b1;
   assign dbg_rst        = 1'b1;
`endif


// Generate main system reset (PUC_RST)
//--------------------------------------
wire puc_noscan_n;
wire puc_a_scan;

// Asynchronous PUC reset
wire puc_a = por | wdt_reset;

// Synchronous PUC reset
wire puc_s = dbg_cpu_reset |                              // With the debug interface command

            (dbg_en_s & dbg_rst_noscan & ~puc_noscan_n);  // Sequencing making sure PUC is released
                                                          // after DBG_RST if the debug interface is
                                                          // enabled at power-on-reset time
// Scan Reset Mux
`ifdef ASIC
omsp_scan_mux scan_mux_puc_rst_a (
    .scan_mode    (scan_mode),
    .data_in_scan (por_a),
    .data_in_func (puc_a),
    .data_out     (puc_a_scan)
);
`else
  assign puc_a_scan = puc_a;
`endif

// Reset Synchronizer
// (required because of the asynchronous watchdog reset)
omsp_sync_cell sync_cell_puc (
    .data_out  (puc_noscan_n),
    .data_in   (~puc_s),
    .clk       (mclk),
    .rst       (puc_a_scan)
);

// Scan Reset Mux
`ifdef ASIC
omsp_scan_mux scan_mux_puc_rst (
    .scan_mode    (scan_mode),
    .data_in_scan (por_a),
    .data_in_func (~puc_noscan_n),
    .data_out     (puc_rst)
);
`else
  assign puc_rst = ~puc_noscan_n;
`endif

// PUC pending set the serial debug interface
assign puc_pnd_set = ~puc_noscan_n;


endmodule // omsp_clock_module

`ifdef OMSP_NO_INCLUDE
`else
`include "openMSP430_undefines.v"
`endif
