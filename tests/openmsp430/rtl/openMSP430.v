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
// *File Name: openMSP430.v
// 
// *Module Description:
//                       openMSP430 Top level file
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

module  openMSP430 (

// OUTPUTs
    aclk,                          // ASIC ONLY: ACLK
    aclk_en,                       // FPGA ONLY: ACLK enable
    dbg_freeze,                    // Freeze peripherals
    dbg_uart_txd,                  // Debug interface: UART TXD
    dco_enable,                    // ASIC ONLY: Fast oscillator enable
    dco_wkup,                      // ASIC ONLY: Fast oscillator wake-up (asynchronous)
    dmem_addr,                     // Data Memory address
    dmem_cen,                      // Data Memory chip enable (low active)
    dmem_din,                      // Data Memory data input
    dmem_wen,                      // Data Memory write enable (low active)
    irq_acc,                       // Interrupt request accepted (one-hot signal)
    lfxt_enable,                   // ASIC ONLY: Low frequency oscillator enable
    lfxt_wkup,                     // ASIC ONLY: Low frequency oscillator wake-up (asynchronous)
    mclk,                          // Main system clock
    per_addr,                      // Peripheral address
    per_din,                       // Peripheral data input
    per_we,                        // Peripheral write enable (high active)
    per_en,                        // Peripheral enable (high active)
    pmem_addr,                     // Program Memory address
    pmem_cen,                      // Program Memory chip enable (low active)
    pmem_din,                      // Program Memory data input (optional)
    pmem_wen,                      // Program Memory write enable (low active) (optional)
    puc_rst,                       // Main system reset
    smclk,                         // ASIC ONLY: SMCLK
    smclk_en,                      // FPGA ONLY: SMCLK enable

// INPUTs
    cpu_en,                        // Enable CPU code execution (asynchronous and non-glitchy)
    dbg_en,                        // Debug interface enable (asynchronous and non-glitchy)
    dbg_uart_rxd,                  // Debug interface: UART RXD (asynchronous)
    dco_clk,                       // Fast oscillator (fast clock)
    dmem_dout,                     // Data Memory data output
    irq,                           // Maskable interrupts
    lfxt_clk,                      // Low frequency oscillator (typ 32kHz)
    nmi,                           // Non-maskable interrupt (asynchronous)
    per_dout,                      // Peripheral data output
    pmem_dout,                     // Program Memory data output
    reset_n,                       // Reset Pin (low active, asynchronous and non-glitchy)
    scan_enable,                   // ASIC ONLY: Scan enable (active during scan shifting)
    scan_mode,                     // ASIC ONLY: Scan mode
    wkup                           // ASIC ONLY: System Wake-up (asynchronous and non-glitchy)
);

// OUTPUTs
//=========
output               aclk;         // ASIC ONLY: ACLK
output               aclk_en;      // FPGA ONLY: ACLK enable
output               dbg_freeze;   // Freeze peripherals
output               dbg_uart_txd; // Debug interface: UART TXD
output               dco_enable;   // ASIC ONLY: Fast oscillator enable
output               dco_wkup;     // ASIC ONLY: Fast oscillator wake-up (asynchronous)
output [`DMEM_MSB:0] dmem_addr;    // Data Memory address
output               dmem_cen;     // Data Memory chip enable (low active)
output        [15:0] dmem_din;     // Data Memory data input
output         [1:0] dmem_wen;     // Data Memory write enable (low active)
output        [13:0] irq_acc;      // Interrupt request accepted (one-hot signal)
output               lfxt_enable;  // ASIC ONLY: Low frequency oscillator enable
output               lfxt_wkup;    // ASIC ONLY: Low frequency oscillator wake-up (asynchronous)
output               mclk;         // Main system clock
output        [13:0] per_addr;     // Peripheral address
output        [15:0] per_din;      // Peripheral data input
output         [1:0] per_we;       // Peripheral write enable (high active)
output               per_en;       // Peripheral enable (high active)
output [`PMEM_MSB:0] pmem_addr;    // Program Memory address
output               pmem_cen;     // Program Memory chip enable (low active)
output        [15:0] pmem_din;     // Program Memory data input (optional)
output         [1:0] pmem_wen;     // Program Memory write enable (low active) (optional)
output               puc_rst;      // Main system reset
output               smclk;        // ASIC ONLY: SMCLK
output               smclk_en;     // FPGA ONLY: SMCLK enable


// INPUTs
//=========
input                cpu_en;       // Enable CPU code execution (asynchronous and non-glitchy)
input                dbg_en;       // Debug interface enable (asynchronous and non-glitchy)
input                dbg_uart_rxd; // Debug interface: UART RXD (asynchronous)
input                dco_clk;      // Fast oscillator (fast clock)
input         [15:0] dmem_dout;    // Data Memory data output
input  	      [13:0] irq;          // Maskable interrupts
input                lfxt_clk;     // Low frequency oscillator (typ 32kHz)
input  	             nmi;          // Non-maskable interrupt (asynchronous and non-glitchy)
input         [15:0] per_dout;     // Peripheral data output
input         [15:0] pmem_dout;    // Program Memory data output
input                reset_n;      // Reset Pin (active low, asynchronous and non-glitchy)
input                scan_enable;  // ASIC ONLY: Scan enable (active during scan shifting)
input                scan_mode;    // ASIC ONLY: Scan mode
input                wkup;         // ASIC ONLY: System Wake-up (asynchronous and non-glitchy)



//=============================================================================
// 1)  INTERNAL WIRES/REGISTERS/PARAMETERS DECLARATION
//=============================================================================

wire          [7:0] inst_ad;
wire          [7:0] inst_as;
wire         [11:0] inst_alu;
wire                inst_bw;
wire                inst_irq_rst;
wire                inst_mov;
wire         [15:0] inst_dest;
wire         [15:0] inst_dext;
wire         [15:0] inst_sext;
wire          [7:0] inst_so;
wire         [15:0] inst_src;
wire          [2:0] inst_type;
wire          [7:0] inst_jmp;
wire          [3:0] e_state;
wire                exec_done;
wire                decode_noirq;
wire                cpu_en_s;
wire                cpuoff;
wire                oscoff;
wire                scg0;
wire                scg1;
wire                por;
wire                gie;
wire                mclk_enable;
wire                mclk_wkup;
wire         [31:0] cpu_id;

wire         [15:0] eu_mab;
wire         [15:0] eu_mdb_in;
wire         [15:0] eu_mdb_out;
wire          [1:0] eu_mb_wr;
wire                eu_mb_en;
wire         [15:0] fe_mab;
wire         [15:0] fe_mdb_in;
wire                fe_mb_en;
wire                fe_pmem_wait;

wire                pc_sw_wr;
wire         [15:0] pc_sw;
wire         [15:0] pc;
wire         [15:0] pc_nxt;

wire                nmi_acc;
wire                nmi_pnd;
wire                nmi_wkup;

wire                wdtie;
wire                wdtnmies;
wire                wdtifg;
wire                wdt_irq;
wire                wdt_wkup;
wire                wdt_reset;
wire                wdtifg_sw_clr;
wire                wdtifg_sw_set;

wire                dbg_clk;
wire                dbg_rst;
wire                dbg_en_s;
wire                dbg_halt_st;
wire                dbg_halt_cmd;
wire                dbg_mem_en;
wire                dbg_reg_wr;
wire                dbg_cpu_reset;
wire         [15:0] dbg_mem_addr;
wire         [15:0] dbg_mem_dout;
wire         [15:0] dbg_mem_din;
wire         [15:0] dbg_reg_din;
wire          [1:0] dbg_mem_wr;
wire                puc_pnd_set;
   
wire         [15:0] per_dout_or;
wire         [15:0] per_dout_sfr;
wire         [15:0] per_dout_wdog;
wire         [15:0] per_dout_mpy;
wire         [15:0] per_dout_clk;

   
//=============================================================================
// 2)  GLOBAL CLOCK & RESET MANAGEMENT
//=============================================================================

omsp_clock_module clock_module_0 (

// OUTPUTs
    .aclk         (aclk),          // ACLK
    .aclk_en      (aclk_en),       // ACLK enablex
    .cpu_en_s     (cpu_en_s),      // Enable CPU code execution (synchronous)
    .dbg_clk      (dbg_clk),       // Debug unit clock
    .dbg_en_s     (dbg_en_s),      // Debug interface enable (synchronous)
    .dbg_rst      (dbg_rst),       // Debug unit reset
    .dco_enable   (dco_enable),    // Fast oscillator enable
    .dco_wkup     (dco_wkup),      // Fast oscillator wake-up (asynchronous)
    .lfxt_enable  (lfxt_enable),   // Low frequency oscillator enable
    .lfxt_wkup    (lfxt_wkup),     // Low frequency oscillator wake-up (asynchronous)
    .mclk         (mclk),          // Main system clock
    .per_dout     (per_dout_clk),  // Peripheral data output
    .por          (por),           // Power-on reset
    .puc_pnd_set  (puc_pnd_set),   // PUC pending set for the serial debug interface
    .puc_rst      (puc_rst),       // Main system reset
    .smclk        (smclk),         // SMCLK
    .smclk_en     (smclk_en),      // SMCLK enable
	     
// INPUTs
    .cpu_en       (cpu_en),        // Enable CPU code execution (asynchronous)
    .cpuoff       (cpuoff),        // Turns off the CPU
    .dbg_cpu_reset(dbg_cpu_reset), // Reset CPU from debug interface
    .dbg_en       (dbg_en),        // Debug interface enable (asynchronous)
    .dco_clk      (dco_clk),       // Fast oscillator (fast clock)
    .lfxt_clk     (lfxt_clk),      // Low frequency oscillator (typ 32kHz)
    .mclk_enable  (mclk_enable),   // Main System Clock enable
    .mclk_wkup    (mclk_wkup),     // Main System Clock wake-up (asynchronous)
    .oscoff       (oscoff),        // Turns off LFXT1 clock input
    .per_addr     (per_addr),      // Peripheral address
    .per_din      (per_din),       // Peripheral data input
    .per_en       (per_en),        // Peripheral enable (high active)
    .per_we       (per_we),        // Peripheral write enable (high active)
    .reset_n      (reset_n),       // Reset Pin (low active, asynchronous)
    .scan_enable  (scan_enable),   // Scan enable (active during scan shifting)
    .scan_mode    (scan_mode),     // Scan mode
    .scg0         (scg0),          // System clock generator 1. Turns off the DCO
    .scg1         (scg1),          // System clock generator 1. Turns off the SMCLK
    .wdt_reset    (wdt_reset)      // Watchdog-timer reset
);

   
//=============================================================================
// 3)  FRONTEND (<=> FETCH & DECODE)
//=============================================================================

omsp_frontend frontend_0 (

// OUTPUTs
    .dbg_halt_st  (dbg_halt_st),   // Halt/Run status from CPU
    .decode_noirq (decode_noirq),  // Frontend decode instruction
    .e_state      (e_state),       // Execution state
    .exec_done    (exec_done),     // Execution completed
    .inst_ad      (inst_ad),       // Decoded Inst: destination addressing mode
    .inst_as      (inst_as),       // Decoded Inst: source addressing mode
    .inst_alu     (inst_alu),      // ALU control signals
    .inst_bw      (inst_bw),       // Decoded Inst: byte width
    .inst_dest    (inst_dest),     // Decoded Inst: destination (one hot)
    .inst_dext    (inst_dext),     // Decoded Inst: destination extended instruction word
    .inst_irq_rst (inst_irq_rst),  // Decoded Inst: Reset interrupt
    .inst_jmp     (inst_jmp),      // Decoded Inst: Conditional jump
    .inst_mov     (inst_mov),      // Decoded Inst: mov instruction
    .inst_sext    (inst_sext),     // Decoded Inst: source extended instruction word
    .inst_so      (inst_so),       // Decoded Inst: Single-operand arithmetic
    .inst_src     (inst_src),      // Decoded Inst: source (one hot)
    .inst_type    (inst_type),     // Decoded Instruction type
    .irq_acc      (irq_acc),       // Interrupt request accepted
    .mab          (fe_mab),        // Frontend Memory address bus
    .mb_en        (fe_mb_en),      // Frontend Memory bus enable
    .mclk_enable  (mclk_enable),   // Main System Clock enable
    .mclk_wkup    (mclk_wkup),     // Main System Clock wake-up (asynchronous)
    .nmi_acc      (nmi_acc),       // Non-Maskable interrupt request accepted
    .pc           (pc),            // Program counter
    .pc_nxt       (pc_nxt),        // Next PC value (for CALL & IRQ)
			     
// INPUTs
    .cpu_en_s     (cpu_en_s),      // Enable CPU code execution (synchronous)
    .cpuoff       (cpuoff),        // Turns off the CPU
    .dbg_halt_cmd (dbg_halt_cmd),  // Halt CPU command
    .dbg_reg_sel  (dbg_mem_addr[3:0]), // Debug selected register for rd/wr access
    .fe_pmem_wait (fe_pmem_wait),  // Frontend wait for Instruction fetch
    .gie          (gie),           // General interrupt enable
    .irq          (irq),           // Maskable interrupts
    .mclk         (mclk),          // Main system clock
    .mdb_in       (fe_mdb_in),     // Frontend Memory data bus input
    .nmi_pnd      (nmi_pnd),       // Non-maskable interrupt pending
    .nmi_wkup     (nmi_wkup),      // NMI Wakeup
    .pc_sw        (pc_sw),         // Program counter software value
    .pc_sw_wr     (pc_sw_wr),      // Program counter software write
    .puc_rst      (puc_rst),       // Main system reset
    .scan_enable  (scan_enable),   // Scan enable (active during scan shifting)
    .wdt_irq      (wdt_irq),       // Watchdog-timer interrupt
    .wdt_wkup     (wdt_wkup),      // Watchdog Wakeup
    .wkup         (wkup)           // System Wake-up (asynchronous)
);


//=============================================================================
// 4)  EXECUTION UNIT
//=============================================================================

omsp_execution_unit execution_unit_0 (

// OUTPUTs
    .cpuoff       (cpuoff),        // Turns off the CPU
    .dbg_reg_din  (dbg_reg_din),   // Debug unit CPU register data input
    .mab          (eu_mab),        // Memory address bus
    .mb_en        (eu_mb_en),      // Memory bus enable
    .mb_wr        (eu_mb_wr),      // Memory bus write transfer
    .mdb_out      (eu_mdb_out),    // Memory data bus output
    .oscoff       (oscoff),        // Turns off LFXT1 clock input
    .pc_sw        (pc_sw),         // Program counter software value
    .pc_sw_wr     (pc_sw_wr),      // Program counter software write
    .scg0         (scg0),          // System clock generator 1. Turns off the DCO
    .scg1         (scg1),          // System clock generator 1. Turns off the SMCLK

// INPUTs
    .dbg_halt_st  (dbg_halt_st),   // Halt/Run status from CPU
    .dbg_mem_dout (dbg_mem_dout),  // Debug unit data output
    .dbg_reg_wr   (dbg_reg_wr),    // Debug unit CPU register write
    .e_state      (e_state),       // Execution state
    .exec_done    (exec_done),     // Execution completed
    .gie          (gie),           // General interrupt enable
    .inst_ad      (inst_ad),       // Decoded Inst: destination addressing mode
    .inst_as      (inst_as),       // Decoded Inst: source addressing mode
    .inst_alu     (inst_alu),      // ALU control signals
    .inst_bw      (inst_bw),       // Decoded Inst: byte width
    .inst_dest    (inst_dest),     // Decoded Inst: destination (one hot)
    .inst_dext    (inst_dext),     // Decoded Inst: destination extended instruction word
    .inst_irq_rst (inst_irq_rst),  // Decoded Inst: reset interrupt
    .inst_jmp     (inst_jmp),      // Decoded Inst: Conditional jump
    .inst_mov     (inst_mov),      // Decoded Inst: mov instruction
    .inst_sext    (inst_sext),     // Decoded Inst: source extended instruction word
    .inst_so      (inst_so),       // Decoded Inst: Single-operand arithmetic
    .inst_src     (inst_src),      // Decoded Inst: source (one hot)
    .inst_type    (inst_type),     // Decoded Instruction type
    .mclk         (mclk),          // Main system clock
    .mdb_in       (eu_mdb_in),     // Memory data bus input
    .pc           (pc),            // Program counter
    .pc_nxt       (pc_nxt),        // Next PC value (for CALL & IRQ)
    .puc_rst      (puc_rst),       // Main system reset
    .scan_enable  (scan_enable)    // Scan enable (active during scan shifting)
);


//=============================================================================
// 5)  MEMORY BACKBONE
//=============================================================================

omsp_mem_backbone mem_backbone_0 (

// OUTPUTs
    .dbg_mem_din  (dbg_mem_din),   // Debug unit Memory data input
    .dmem_addr    (dmem_addr),     // Data Memory address
    .dmem_cen     (dmem_cen),      // Data Memory chip enable (low active)
    .dmem_din     (dmem_din),      // Data Memory data input
    .dmem_wen     (dmem_wen),      // Data Memory write enable (low active)
    .eu_mdb_in    (eu_mdb_in),     // Execution Unit Memory data bus input
    .fe_mdb_in    (fe_mdb_in),     // Frontend Memory data bus input
    .fe_pmem_wait (fe_pmem_wait),  // Frontend wait for Instruction fetch
    .per_addr     (per_addr),      // Peripheral address
    .per_din      (per_din),       // Peripheral data input
    .per_we       (per_we),        // Peripheral write enable (high active)
    .per_en       (per_en),        // Peripheral enable (high active)
    .pmem_addr    (pmem_addr),     // Program Memory address
    .pmem_cen     (pmem_cen),      // Program Memory chip enable (low active)
    .pmem_din     (pmem_din),      // Program Memory data input (optional)
    .pmem_wen     (pmem_wen),      // Program Memory write enable (low active) (optional)
			     
// INPUTs
    .dbg_halt_st  (dbg_halt_st),   // Halt/Run status from CPU
    .dbg_mem_addr (dbg_mem_addr),  // Debug address for rd/wr access
    .dbg_mem_dout (dbg_mem_dout),  // Debug unit data output
    .dbg_mem_en   (dbg_mem_en),    // Debug unit memory enable
    .dbg_mem_wr   (dbg_mem_wr),    // Debug unit memory write
    .dmem_dout    (dmem_dout),     // Data Memory data output
    .eu_mab       (eu_mab[15:1]),  // Execution Unit Memory address bus
    .eu_mb_en     (eu_mb_en),      // Execution Unit Memory bus enable
    .eu_mb_wr     (eu_mb_wr),      // Execution Unit Memory bus write transfer
    .eu_mdb_out   (eu_mdb_out),    // Execution Unit Memory data bus output
    .fe_mab       (fe_mab[15:1]),  // Frontend Memory address bus
    .fe_mb_en     (fe_mb_en),      // Frontend Memory bus enable
    .mclk         (mclk),          // Main system clock
    .per_dout     (per_dout_or),   // Peripheral data output
    .pmem_dout    (pmem_dout),     // Program Memory data output
    .puc_rst      (puc_rst),       // Main system reset
    .scan_enable  (scan_enable)    // Scan enable (active during scan shifting)
);


//=============================================================================
// 6)  SPECIAL FUNCTION REGISTERS
//=============================================================================
omsp_sfr sfr_0 (

// OUTPUTs
    .cpu_id       (cpu_id),        // CPU ID
    .nmi_pnd      (nmi_pnd),       // NMI Pending
    .nmi_wkup     (nmi_wkup),      // NMI Wakeup
    .per_dout     (per_dout_sfr),  // Peripheral data output
    .wdtie        (wdtie),         // Watchdog-timer interrupt enable
    .wdtifg_sw_clr(wdtifg_sw_clr), // Watchdog-timer interrupt flag software clear
    .wdtifg_sw_set(wdtifg_sw_set), // Watchdog-timer interrupt flag software set
			     
// INPUTs
    .mclk         (mclk),          // Main system clock
    .nmi          (nmi),           // Non-maskable interrupt (asynchronous)
    .nmi_acc      (nmi_acc),       // Non-Maskable interrupt request accepted
    .per_addr     (per_addr),      // Peripheral address
    .per_din      (per_din),       // Peripheral data input
    .per_en       (per_en),        // Peripheral enable (high active)
    .per_we       (per_we),        // Peripheral write enable (high active)
    .puc_rst      (puc_rst),       // Main system reset
    .scan_mode    (scan_mode),     // Scan mode
    .wdtifg       (wdtifg),        // Watchdog-timer interrupt flag
    .wdtnmies     (wdtnmies)       // Watchdog-timer NMI edge selection
);


//=============================================================================
// 7)  WATCHDOG TIMER
//=============================================================================
`ifdef WATCHDOG
omsp_watchdog watchdog_0 (

// OUTPUTs
    .per_dout       (per_dout_wdog), // Peripheral data output
    .wdt_irq        (wdt_irq),       // Watchdog-timer interrupt
    .wdt_reset      (wdt_reset),     // Watchdog-timer reset
    .wdt_wkup       (wdt_wkup),      // Watchdog Wakeup
    .wdtifg         (wdtifg),        // Watchdog-timer interrupt flag
    .wdtnmies       (wdtnmies),      // Watchdog-timer NMI edge selection
			     
// INPUTs
    .aclk           (aclk),          // ACLK
    .aclk_en        (aclk_en),       // ACLK enable
    .dbg_freeze     (dbg_freeze),    // Freeze Watchdog counter
    .mclk           (mclk),          // Main system clock
    .per_addr       (per_addr),      // Peripheral address
    .per_din        (per_din),       // Peripheral data input
    .per_en         (per_en),        // Peripheral enable (high active)
    .per_we         (per_we),        // Peripheral write enable (high active)
    .por            (por),           // Power-on reset
    .puc_rst        (puc_rst),       // Main system reset
    .scan_enable    (scan_enable),   // Scan enable (active during scan shifting)
    .scan_mode      (scan_mode),     // Scan mode
    .smclk          (smclk),         // SMCLK
    .smclk_en       (smclk_en),      // SMCLK enable
    .wdtie          (wdtie),         // Watchdog-timer interrupt enable
    .wdtifg_irq_clr (irq_acc[10]),   // Clear Watchdog-timer interrupt flag
    .wdtifg_sw_clr  (wdtifg_sw_clr), // Watchdog-timer interrupt flag software clear
    .wdtifg_sw_set  (wdtifg_sw_set)  // Watchdog-timer interrupt flag software set
);
`else
assign per_dout_wdog = 16'h0000;
assign wdt_irq       =  1'b0;
assign wdt_reset     =  1'b0;
assign wdt_wkup      =  1'b0;
assign wdtifg        =  1'b0;
assign wdtnmies      =  1'b0;
`endif


//=============================================================================
// 8)  HARDWARE MULTIPLIER
//=============================================================================
`ifdef MULTIPLIER
omsp_multiplier multiplier_0 (

// OUTPUTs
    .per_dout     (per_dout_mpy),  // Peripheral data output
			     
// INPUTs
    .mclk         (mclk),          // Main system clock
    .per_addr     (per_addr),      // Peripheral address
    .per_din      (per_din),       // Peripheral data input
    .per_en       (per_en),        // Peripheral enable (high active)
    .per_we       (per_we),        // Peripheral write enable (high active)
    .puc_rst      (puc_rst),       // Main system reset
    .scan_enable  (scan_enable)    // Scan enable (active during scan shifting)
);
`else
assign per_dout_mpy = 16'h0000;
`endif
   
//=============================================================================
// 9)  PERIPHERALS' OUTPUT BUS
//=============================================================================

assign  per_dout_or  =  per_dout      |
                        per_dout_clk  |
                        per_dout_sfr  |
                        per_dout_wdog |
                        per_dout_mpy;

   
//=============================================================================
// 10)  DEBUG INTERFACE
//=============================================================================

`ifdef DBG_EN
omsp_dbg dbg_0 (

// OUTPUTs
    .dbg_freeze   (dbg_freeze),    // Freeze peripherals
    .dbg_halt_cmd (dbg_halt_cmd),  // Halt CPU command
    .dbg_mem_addr (dbg_mem_addr),  // Debug address for rd/wr access
    .dbg_mem_dout (dbg_mem_dout),  // Debug unit data output
    .dbg_mem_en   (dbg_mem_en),    // Debug unit memory enable
    .dbg_mem_wr   (dbg_mem_wr),    // Debug unit memory write
    .dbg_reg_wr   (dbg_reg_wr),    // Debug unit CPU register write
    .dbg_cpu_reset(dbg_cpu_reset), // Reset CPU from debug interface
    .dbg_uart_txd (dbg_uart_txd),  // Debug interface: UART TXD
			     
// INPUTs
    .cpu_en_s     (cpu_en_s),      // Enable CPU code execution (synchronous)
    .cpu_id       (cpu_id),        // CPU ID
    .dbg_clk      (dbg_clk),       // Debug unit clock
    .dbg_en_s     (dbg_en_s),      // Debug interface enable (synchronous)
    .dbg_halt_st  (dbg_halt_st),   // Halt/Run status from CPU
    .dbg_mem_din  (dbg_mem_din),   // Debug unit Memory data input
    .dbg_reg_din  (dbg_reg_din),   // Debug unit CPU register data input
    .dbg_rst      (dbg_rst),       // Debug unit reset
    .dbg_uart_rxd (dbg_uart_rxd),  // Debug interface: UART RXD (asynchronous)
    .decode_noirq (decode_noirq),  // Frontend decode instruction
    .eu_mab       (eu_mab),        // Execution-Unit Memory address bus
    .eu_mb_en     (eu_mb_en),      // Execution-Unit Memory bus enable
    .eu_mb_wr     (eu_mb_wr),      // Execution-Unit Memory bus write transfer
    .eu_mdb_in    (eu_mdb_in),     // Memory data bus input
    .eu_mdb_out   (eu_mdb_out),    // Memory data bus output
    .exec_done    (exec_done),     // Execution completed
    .fe_mb_en     (fe_mb_en),      // Frontend Memory bus enable
    .fe_mdb_in    (fe_mdb_in),     // Frontend Memory data bus input
    .pc           (pc),            // Program counter
    .puc_pnd_set  (puc_pnd_set)    // PUC pending set for the serial debug interface
);

`else
assign dbg_freeze    =  ~cpu_en_s;
assign dbg_halt_cmd  =  1'b0;
assign dbg_mem_addr  = 16'h0000;
assign dbg_mem_dout  = 16'h0000;
assign dbg_mem_en    =  1'b0;
assign dbg_mem_wr    =  2'b00;
assign dbg_reg_wr    =  1'b0;
assign dbg_cpu_reset =  1'b0;
assign dbg_uart_txd  =  1'b0;
`endif

   
endmodule // openMSP430

`ifdef OMSP_NO_INCLUDE
`else
`include "openMSP430_undefines.v"
`endif
