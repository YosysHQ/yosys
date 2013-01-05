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
// *File Name: omsp_register_file.v
// 
// *Module Description:
//                       openMSP430 Register files
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

module  omsp_register_file (

// OUTPUTs
    cpuoff,                       // Turns off the CPU
    gie,                          // General interrupt enable
    oscoff,                       // Turns off LFXT1 clock input
    pc_sw,                        // Program counter software value
    pc_sw_wr,                     // Program counter software write
    reg_dest,                     // Selected register destination content
    reg_src,                      // Selected register source content
    scg0,                         // System clock generator 1. Turns off the DCO
    scg1,                         // System clock generator 1. Turns off the SMCLK
    status,                       // R2 Status {V,N,Z,C}

// INPUTs
    alu_stat,                     // ALU Status {V,N,Z,C}
    alu_stat_wr,                  // ALU Status write {V,N,Z,C}
    inst_bw,                      // Decoded Inst: byte width
    inst_dest,                    // Register destination selection
    inst_src,                     // Register source selection
    mclk,                         // Main system clock
    pc,                           // Program counter
    puc_rst,                      // Main system reset
    reg_dest_val,                 // Selected register destination value
    reg_dest_wr,                  // Write selected register destination
    reg_pc_call,                  // Trigger PC update for a CALL instruction
    reg_sp_val,                   // Stack Pointer next value
    reg_sp_wr,                    // Stack Pointer write
    reg_sr_wr,                    // Status register update for RETI instruction
    reg_sr_clr,                   // Status register clear for interrupts
    reg_incr,                     // Increment source register
    scan_enable                   // Scan enable (active during scan shifting)
);

// OUTPUTs
//=========
output 	            cpuoff;       // Turns off the CPU
output 	            gie;          // General interrupt enable
output 	            oscoff;       // Turns off LFXT1 clock input
output       [15:0] pc_sw;        // Program counter software value
output              pc_sw_wr;     // Program counter software write
output       [15:0] reg_dest;     // Selected register destination content
output       [15:0] reg_src;      // Selected register source content
output              scg0;         // System clock generator 1. Turns off the DCO
output              scg1;         // System clock generator 1. Turns off the SMCLK
output        [3:0] status;       // R2 Status {V,N,Z,C}

// INPUTs
//=========
input         [3:0] alu_stat;     // ALU Status {V,N,Z,C}
input         [3:0] alu_stat_wr;  // ALU Status write {V,N,Z,C}
input               inst_bw;      // Decoded Inst: byte width
input        [15:0] inst_dest;    // Register destination selection
input        [15:0] inst_src;     // Register source selection
input               mclk;         // Main system clock
input        [15:0] pc;           // Program counter
input               puc_rst;      // Main system reset
input        [15:0] reg_dest_val; // Selected register destination value
input               reg_dest_wr;  // Write selected register destination
input               reg_pc_call;  // Trigger PC update for a CALL instruction
input        [15:0] reg_sp_val;   // Stack Pointer next value
input               reg_sp_wr;    // Stack Pointer write
input               reg_sr_wr;    // Status register update for RETI instruction
input               reg_sr_clr;   // Status register clear for interrupts
input               reg_incr;     // Increment source register
input               scan_enable;  // Scan enable (active during scan shifting)


//=============================================================================
// 1)  AUTOINCREMENT UNIT
//=============================================================================

wire [15:0] inst_src_in;
wire [15:0] incr_op         = (inst_bw & ~inst_src_in[1]) ? 16'h0001 : 16'h0002;
wire [15:0] reg_incr_val    = reg_src+incr_op;

wire [15:0] reg_dest_val_in = inst_bw ? {8'h00,reg_dest_val[7:0]} : reg_dest_val;


//=============================================================================
// 2)  SPECIAL REGISTERS (R1/R2/R3)
//=============================================================================

// Source input selection mask (for interrupt support)
//-----------------------------------------------------

assign inst_src_in = reg_sr_clr ? 16'h0004 : inst_src;


// R0: Program counter
//---------------------

wire [15:0] r0       = pc;

wire [15:0] pc_sw    = reg_dest_val_in;
wire        pc_sw_wr = (inst_dest[0] & reg_dest_wr) | reg_pc_call;


// R1: Stack pointer
//-------------------
reg [15:0] r1;
wire       r1_wr  = inst_dest[1] & reg_dest_wr;
wire       r1_inc = inst_src_in[1]  & reg_incr;

`ifdef CLOCK_GATING
wire       r1_en  = r1_wr | reg_sp_wr | r1_inc;
wire       mclk_r1;
omsp_clock_gate clock_gate_r1 (.gclk(mclk_r1),
                               .clk (mclk), .enable(r1_en), .scan_enable(scan_enable));
`else
wire       mclk_r1 = mclk;
`endif

always @(posedge mclk_r1 or posedge puc_rst)
  if (puc_rst)        r1 <= 16'h0000;
  else if (r1_wr)     r1 <= reg_dest_val_in & 16'hfffe;
  else if (reg_sp_wr) r1 <= reg_sp_val      & 16'hfffe;
`ifdef CLOCK_GATING
  else                r1 <= reg_incr_val    & 16'hfffe;
`else
  else if (r1_inc)    r1 <= reg_incr_val    & 16'hfffe;
`endif


// R2: Status register
//---------------------
reg  [15:0] r2;
wire        r2_wr  = (inst_dest[2] & reg_dest_wr) | reg_sr_wr;

`ifdef CLOCK_GATING                                                              //      -- WITH CLOCK GATING --
wire        r2_c   = alu_stat_wr[0] ? alu_stat[0]          : reg_dest_val_in[0]; // C

wire        r2_z   = alu_stat_wr[1] ? alu_stat[1]          : reg_dest_val_in[1]; // Z

wire        r2_n   = alu_stat_wr[2] ? alu_stat[2]          : reg_dest_val_in[2]; // N

wire  [7:3] r2_nxt = r2_wr          ? reg_dest_val_in[7:3] : r2[7:3];

wire        r2_v   = alu_stat_wr[3] ? alu_stat[3]          : reg_dest_val_in[8]; // V

wire        r2_en  = |alu_stat_wr | r2_wr | reg_sr_clr;
wire        mclk_r2;
omsp_clock_gate clock_gate_r2 (.gclk(mclk_r2),
                               .clk (mclk), .enable(r2_en), .scan_enable(scan_enable));

`else                                                                            //      -- WITHOUT CLOCK GATING --
wire        r2_c   = alu_stat_wr[0] ? alu_stat[0]          :
                     r2_wr          ? reg_dest_val_in[0]   : r2[0];              // C

wire        r2_z   = alu_stat_wr[1] ? alu_stat[1]          :
                     r2_wr          ? reg_dest_val_in[1]   : r2[1];              // Z

wire        r2_n   = alu_stat_wr[2] ? alu_stat[2]          :
                     r2_wr          ? reg_dest_val_in[2]   : r2[2];              // N

wire  [7:3] r2_nxt = r2_wr          ? reg_dest_val_in[7:3] : r2[7:3];

wire        r2_v   = alu_stat_wr[3] ? alu_stat[3]          :
                     r2_wr          ? reg_dest_val_in[8]   : r2[8];              // V


wire        mclk_r2 = mclk;
`endif

`ifdef ASIC
   `ifdef CPUOFF_EN
   wire [15:0] cpuoff_mask = 16'h0010;
   `else
   wire [15:0] cpuoff_mask = 16'h0000;
   `endif
   `ifdef OSCOFF_EN
   wire [15:0] oscoff_mask = 16'h0020;
   `else
   wire [15:0] oscoff_mask = 16'h0000;
   `endif
   `ifdef SCG0_EN
   wire [15:0] scg0_mask   = 16'h0040;
   `else
   wire [15:0] scg0_mask   = 16'h0000;
   `endif
   `ifdef SCG1_EN
   wire [15:0] scg1_mask   = 16'h0080;
   `else
   wire [15:0] scg1_mask   = 16'h0000;
   `endif
`else
   wire [15:0] cpuoff_mask = 16'h0010; // For the FPGA version: - the CPUOFF mode is emulated
   wire [15:0] oscoff_mask = 16'h0020; //                       - the SCG1 mode is emulated
   wire [15:0] scg0_mask   = 16'h0000; //                       - the SCG0 is not supported
   wire [15:0] scg1_mask   = 16'h0080; //                       - the SCG1 mode is emulated
`endif
   
   wire [15:0] r2_mask     = cpuoff_mask | oscoff_mask | scg0_mask | scg1_mask | 16'h010f;
 
always @(posedge mclk_r2 or posedge puc_rst)
  if (puc_rst)         r2 <= 16'h0000;
  else if (reg_sr_clr) r2 <= 16'h0000;
  else                 r2 <= {7'h00, r2_v, r2_nxt, r2_n, r2_z, r2_c} & r2_mask;

assign status = {r2[8], r2[2:0]};
assign gie    =  r2[3];
assign cpuoff =  r2[4] | (r2_nxt[4] & r2_wr & cpuoff_mask[4]);
assign oscoff =  r2[5];
assign scg0   =  r2[6];
assign scg1   =  r2[7];


// R3: Constant generator
//-------------------------------------------------------------
// Note: the auto-increment feature is not implemented for R3
//       because the @R3+ addressing mode is used for constant
//       generation (#-1).
reg [15:0] r3;
wire       r3_wr  = inst_dest[3] & reg_dest_wr;

`ifdef CLOCK_GATING
wire       r3_en   = r3_wr;
wire       mclk_r3;
omsp_clock_gate clock_gate_r3 (.gclk(mclk_r3),
                               .clk (mclk), .enable(r3_en), .scan_enable(scan_enable));
`else
wire       mclk_r3 = mclk;
`endif

always @(posedge mclk_r3 or posedge puc_rst)
  if (puc_rst)     r3 <= 16'h0000;
`ifdef CLOCK_GATING
  else             r3 <= reg_dest_val_in;
`else
  else if (r3_wr)  r3 <= reg_dest_val_in;
`endif


//=============================================================================
// 4)  GENERAL PURPOSE REGISTERS (R4...R15)
//=============================================================================

// R4
//------------
reg [15:0] r4;
wire       r4_wr  = inst_dest[4] & reg_dest_wr;
wire       r4_inc = inst_src_in[4]  & reg_incr;

`ifdef CLOCK_GATING
wire       r4_en  = r4_wr | r4_inc;
wire       mclk_r4;
omsp_clock_gate clock_gate_r4 (.gclk(mclk_r4),
                               .clk (mclk), .enable(r4_en), .scan_enable(scan_enable));
`else
wire       mclk_r4 = mclk;
`endif

always @(posedge mclk_r4 or posedge puc_rst)
  if (puc_rst)      r4  <= 16'h0000;
  else if (r4_wr)   r4  <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r4  <= reg_incr_val;
`else
  else if (r4_inc)  r4  <= reg_incr_val;
`endif

// R5
//------------
reg [15:0] r5;
wire       r5_wr  = inst_dest[5] & reg_dest_wr;
wire       r5_inc = inst_src_in[5]  & reg_incr;

`ifdef CLOCK_GATING
wire       r5_en  = r5_wr | r5_inc;
wire       mclk_r5;
omsp_clock_gate clock_gate_r5 (.gclk(mclk_r5),
                               .clk (mclk), .enable(r5_en), .scan_enable(scan_enable));
`else
wire       mclk_r5 = mclk;
`endif

always @(posedge mclk_r5 or posedge puc_rst)
  if (puc_rst)      r5  <= 16'h0000;
  else if (r5_wr)   r5  <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r5  <= reg_incr_val;
`else
  else if (r5_inc)  r5  <= reg_incr_val;
`endif

// R6
//------------
reg [15:0] r6;
wire       r6_wr  = inst_dest[6] & reg_dest_wr;
wire       r6_inc = inst_src_in[6]  & reg_incr;

`ifdef CLOCK_GATING
wire       r6_en  = r6_wr | r6_inc;
wire       mclk_r6;
omsp_clock_gate clock_gate_r6 (.gclk(mclk_r6),
                               .clk (mclk), .enable(r6_en), .scan_enable(scan_enable));
`else
wire       mclk_r6 = mclk;
`endif

always @(posedge mclk_r6 or posedge puc_rst)
  if (puc_rst)      r6  <= 16'h0000;
  else if (r6_wr)   r6  <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r6  <= reg_incr_val;
`else
  else if (r6_inc)  r6  <= reg_incr_val;
`endif

// R7
//------------
reg [15:0] r7;
wire       r7_wr  = inst_dest[7] & reg_dest_wr;
wire       r7_inc = inst_src_in[7]  & reg_incr;

`ifdef CLOCK_GATING
wire       r7_en  = r7_wr | r7_inc;
wire       mclk_r7;
omsp_clock_gate clock_gate_r7 (.gclk(mclk_r7),
                               .clk (mclk), .enable(r7_en), .scan_enable(scan_enable));
`else
wire       mclk_r7 = mclk;
`endif

always @(posedge mclk_r7 or posedge puc_rst)
  if (puc_rst)      r7  <= 16'h0000;
  else if (r7_wr)   r7  <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r7  <= reg_incr_val;
`else
  else if (r7_inc)  r7  <= reg_incr_val;
`endif

// R8
//------------
reg [15:0] r8;
wire       r8_wr  = inst_dest[8] & reg_dest_wr;
wire       r8_inc = inst_src_in[8]  & reg_incr;

`ifdef CLOCK_GATING
wire       r8_en  = r8_wr | r8_inc;
wire       mclk_r8;
omsp_clock_gate clock_gate_r8 (.gclk(mclk_r8),
                               .clk (mclk), .enable(r8_en), .scan_enable(scan_enable));
`else
wire       mclk_r8 = mclk;
`endif

always @(posedge mclk_r8 or posedge puc_rst)
  if (puc_rst)      r8  <= 16'h0000;
  else if (r8_wr)   r8  <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r8  <= reg_incr_val;
`else
  else if (r8_inc)  r8  <= reg_incr_val;
`endif

// R9
//------------
reg [15:0] r9;
wire       r9_wr  = inst_dest[9] & reg_dest_wr;
wire       r9_inc = inst_src_in[9]  & reg_incr;

`ifdef CLOCK_GATING
wire       r9_en  = r9_wr | r9_inc;
wire       mclk_r9;
omsp_clock_gate clock_gate_r9 (.gclk(mclk_r9),
                               .clk (mclk), .enable(r9_en), .scan_enable(scan_enable));
`else
wire       mclk_r9 = mclk;
`endif

always @(posedge mclk_r9 or posedge puc_rst)
  if (puc_rst)      r9  <= 16'h0000;
  else if (r9_wr)   r9  <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r9  <= reg_incr_val;
`else
  else if (r9_inc)  r9  <= reg_incr_val;
`endif

// R10
//------------
reg [15:0] r10;
wire       r10_wr  = inst_dest[10] & reg_dest_wr;
wire       r10_inc = inst_src_in[10]  & reg_incr;

`ifdef CLOCK_GATING
wire       r10_en  = r10_wr | r10_inc;
wire       mclk_r10;
omsp_clock_gate clock_gate_r10 (.gclk(mclk_r10),
                                .clk (mclk), .enable(r10_en), .scan_enable(scan_enable));
`else
wire       mclk_r10 = mclk;
`endif

always @(posedge mclk_r10 or posedge puc_rst)
  if (puc_rst)      r10 <= 16'h0000;
  else if (r10_wr)  r10 <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r10 <= reg_incr_val;
`else
  else if (r10_inc) r10 <= reg_incr_val;
`endif

// R11
//------------
reg [15:0] r11;
wire       r11_wr  = inst_dest[11] & reg_dest_wr;
wire       r11_inc = inst_src_in[11]  & reg_incr;

`ifdef CLOCK_GATING
wire       r11_en  = r11_wr | r11_inc;
wire       mclk_r11;
omsp_clock_gate clock_gate_r11 (.gclk(mclk_r11),
                                .clk (mclk), .enable(r11_en), .scan_enable(scan_enable));
`else
wire       mclk_r11 = mclk;
`endif

always @(posedge mclk_r11 or posedge puc_rst)
  if (puc_rst)      r11 <= 16'h0000;
  else if (r11_wr)  r11 <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r11 <= reg_incr_val;
`else
  else if (r11_inc) r11 <= reg_incr_val;
`endif

// R12
//------------
reg [15:0] r12;
wire       r12_wr  = inst_dest[12] & reg_dest_wr;
wire       r12_inc = inst_src_in[12]  & reg_incr;

`ifdef CLOCK_GATING
wire       r12_en  = r12_wr | r12_inc;
wire       mclk_r12;
omsp_clock_gate clock_gate_r12 (.gclk(mclk_r12),
                                .clk (mclk), .enable(r12_en), .scan_enable(scan_enable));
`else
wire       mclk_r12 = mclk;
`endif

always @(posedge mclk_r12 or posedge puc_rst)
  if (puc_rst)      r12 <= 16'h0000;
  else if (r12_wr)  r12 <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r12 <= reg_incr_val;
`else
  else if (r12_inc) r12 <= reg_incr_val;
`endif

// R13
//------------
reg [15:0] r13;
wire       r13_wr  = inst_dest[13] & reg_dest_wr;
wire       r13_inc = inst_src_in[13]  & reg_incr;

`ifdef CLOCK_GATING
wire       r13_en  = r13_wr | r13_inc;
wire       mclk_r13;
omsp_clock_gate clock_gate_r13 (.gclk(mclk_r13),
                                .clk (mclk), .enable(r13_en), .scan_enable(scan_enable));
`else
wire       mclk_r13 = mclk;
`endif

always @(posedge mclk_r13 or posedge puc_rst)
  if (puc_rst)      r13 <= 16'h0000;
  else if (r13_wr)  r13 <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r13 <= reg_incr_val;
`else
  else if (r13_inc) r13 <= reg_incr_val;
`endif

// R14
//------------
reg [15:0] r14;
wire       r14_wr  = inst_dest[14] & reg_dest_wr;
wire       r14_inc = inst_src_in[14]  & reg_incr;

`ifdef CLOCK_GATING
wire       r14_en  = r14_wr | r14_inc;
wire       mclk_r14;
omsp_clock_gate clock_gate_r14 (.gclk(mclk_r14),
                                .clk (mclk), .enable(r14_en), .scan_enable(scan_enable));
`else
wire       mclk_r14 = mclk;
`endif

always @(posedge mclk_r14 or posedge puc_rst)
  if (puc_rst)      r14 <= 16'h0000;
  else if (r14_wr)  r14 <= reg_dest_val_in;
`ifdef CLOCK_GATING
  else              r14 <= reg_incr_val;
`else
  else if (r14_inc) r14 <= reg_incr_val;
`endif

// R15
//------------
reg [15:0] r15;
wire       r15_wr  = inst_dest[15] & reg_dest_wr;
wire       r15_inc = inst_src_in[15]  & reg_incr;

`ifdef CLOCK_GATING
wire       r15_en  = r15_wr | r15_inc;
wire       mclk_r15;
omsp_clock_gate clock_gate_r15 (.gclk(mclk_r15),
                                .clk (mclk), .enable(r15_en), .scan_enable(scan_enable));
`else
wire       mclk_r15 = mclk;
`endif

always @(posedge mclk_r15 or posedge puc_rst)
  if (puc_rst)      r15 <= 16'h0000;
  else if (r15_wr)  r15 <= reg_dest_val_in;
 `ifdef CLOCK_GATING
  else              r15 <= reg_incr_val;
`else
 else if (r15_inc)  r15 <= reg_incr_val;
`endif


//=============================================================================
// 5)  READ MUX
//=============================================================================

assign reg_src  = (r0      & {16{inst_src_in[0]}})   | 
                  (r1      & {16{inst_src_in[1]}})   | 
                  (r2      & {16{inst_src_in[2]}})   | 
                  (r3      & {16{inst_src_in[3]}})   | 
                  (r4      & {16{inst_src_in[4]}})   | 
                  (r5      & {16{inst_src_in[5]}})   | 
                  (r6      & {16{inst_src_in[6]}})   | 
                  (r7      & {16{inst_src_in[7]}})   | 
                  (r8      & {16{inst_src_in[8]}})   | 
                  (r9      & {16{inst_src_in[9]}})   | 
                  (r10     & {16{inst_src_in[10]}})  | 
                  (r11     & {16{inst_src_in[11]}})  | 
                  (r12     & {16{inst_src_in[12]}})  | 
                  (r13     & {16{inst_src_in[13]}})  | 
                  (r14     & {16{inst_src_in[14]}})  | 
                  (r15     & {16{inst_src_in[15]}});

assign reg_dest = (r0      & {16{inst_dest[0]}})  | 
                  (r1      & {16{inst_dest[1]}})  | 
                  (r2      & {16{inst_dest[2]}})  | 
                  (r3      & {16{inst_dest[3]}})  | 
                  (r4      & {16{inst_dest[4]}})  | 
                  (r5      & {16{inst_dest[5]}})  | 
                  (r6      & {16{inst_dest[6]}})  | 
                  (r7      & {16{inst_dest[7]}})  | 
                  (r8      & {16{inst_dest[8]}})  | 
                  (r9      & {16{inst_dest[9]}})  | 
                  (r10     & {16{inst_dest[10]}}) | 
                  (r11     & {16{inst_dest[11]}}) | 
                  (r12     & {16{inst_dest[12]}}) | 
                  (r13     & {16{inst_dest[13]}}) | 
                  (r14     & {16{inst_dest[14]}}) | 
                  (r15     & {16{inst_dest[15]}});


endmodule // omsp_register_file

`ifdef OMSP_NO_INCLUDE
`else
`include "openMSP430_undefines.v"
`endif
