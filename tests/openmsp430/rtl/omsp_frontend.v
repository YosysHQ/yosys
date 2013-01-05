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
// *File Name: omsp_frontend.v
// 
// *Module Description:
//                       openMSP430 Instruction fetch and decode unit
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

module  omsp_frontend (

// OUTPUTs
    dbg_halt_st,                   // Halt/Run status from CPU
    decode_noirq,                  // Frontend decode instruction
    e_state,                       // Execution state
    exec_done,                     // Execution completed
    inst_ad,                       // Decoded Inst: destination addressing mode
    inst_as,                       // Decoded Inst: source addressing mode
    inst_alu,                      // ALU control signals
    inst_bw,                       // Decoded Inst: byte width
    inst_dest,                     // Decoded Inst: destination (one hot)
    inst_dext,                     // Decoded Inst: destination extended instruction word
    inst_irq_rst,                  // Decoded Inst: Reset interrupt
    inst_jmp,                      // Decoded Inst: Conditional jump
    inst_mov,                      // Decoded Inst: mov instruction
    inst_sext,                     // Decoded Inst: source extended instruction word
    inst_so,                       // Decoded Inst: Single-operand arithmetic
    inst_src,                      // Decoded Inst: source (one hot)
    inst_type,                     // Decoded Instruction type
    irq_acc,                       // Interrupt request accepted (one-hot signal)
    mab,                           // Frontend Memory address bus
    mb_en,                         // Frontend Memory bus enable
    mclk_enable,                   // Main System Clock enable
    mclk_wkup,                     // Main System Clock wake-up (asynchronous)
    nmi_acc,                       // Non-Maskable interrupt request accepted
    pc,                            // Program counter
    pc_nxt,                        // Next PC value (for CALL & IRQ)

// INPUTs
    cpu_en_s,                      // Enable CPU code execution (synchronous)
    cpuoff,                        // Turns off the CPU
    dbg_halt_cmd,                  // Halt CPU command
    dbg_reg_sel,                   // Debug selected register for rd/wr access
    fe_pmem_wait,                  // Frontend wait for Instruction fetch
    gie,                           // General interrupt enable
    irq,                           // Maskable interrupts
    mclk,                          // Main system clock
    mdb_in,                        // Frontend Memory data bus input
    nmi_pnd,                       // Non-maskable interrupt pending
    nmi_wkup,                      // NMI Wakeup
    pc_sw,                         // Program counter software value
    pc_sw_wr,                      // Program counter software write
    puc_rst,                       // Main system reset
    scan_enable,                   // Scan enable (active during scan shifting)
    wdt_irq,                       // Watchdog-timer interrupt
    wdt_wkup,                      // Watchdog Wakeup
    wkup                           // System Wake-up (asynchronous)
);

// OUTPUTs
//=========
output              dbg_halt_st;   // Halt/Run status from CPU
output              decode_noirq;  // Frontend decode instruction
output        [3:0] e_state;       // Execution state
output              exec_done;     // Execution completed
output        [7:0] inst_ad;       // Decoded Inst: destination addressing mode
output        [7:0] inst_as;       // Decoded Inst: source addressing mode
output       [11:0] inst_alu;      // ALU control signals
output              inst_bw;       // Decoded Inst: byte width
output       [15:0] inst_dest;     // Decoded Inst: destination (one hot)
output       [15:0] inst_dext;     // Decoded Inst: destination extended instruction word
output              inst_irq_rst;  // Decoded Inst: Reset interrupt
output        [7:0] inst_jmp;      // Decoded Inst: Conditional jump
output              inst_mov;      // Decoded Inst: mov instruction
output       [15:0] inst_sext;     // Decoded Inst: source extended instruction word
output        [7:0] inst_so;       // Decoded Inst: Single-operand arithmetic
output       [15:0] inst_src;      // Decoded Inst: source (one hot)
output        [2:0] inst_type;     // Decoded Instruction type
output       [13:0] irq_acc;       // Interrupt request accepted (one-hot signal)
output       [15:0] mab;           // Frontend Memory address bus
output              mb_en;         // Frontend Memory bus enable
output              mclk_enable;   // Main System Clock enable
output              mclk_wkup;     // Main System Clock wake-up (asynchronous)
output              nmi_acc;       // Non-Maskable interrupt request accepted
output       [15:0] pc;            // Program counter
output       [15:0] pc_nxt;        // Next PC value (for CALL & IRQ)

// INPUTs
//=========
input               cpu_en_s;      // Enable CPU code execution (synchronous)
input               cpuoff;        // Turns off the CPU
input               dbg_halt_cmd;  // Halt CPU command
input         [3:0] dbg_reg_sel;   // Debug selected register for rd/wr access
input               fe_pmem_wait;  // Frontend wait for Instruction fetch
input               gie;           // General interrupt enable
input        [13:0] irq;           // Maskable interrupts
input               mclk;          // Main system clock
input        [15:0] mdb_in;        // Frontend Memory data bus input
input               nmi_pnd;       // Non-maskable interrupt pending
input               nmi_wkup;      // NMI Wakeup
input        [15:0] pc_sw;         // Program counter software value
input               pc_sw_wr;      // Program counter software write
input               puc_rst;       // Main system reset
input               scan_enable;   // Scan enable (active during scan shifting)
input               wdt_irq;       // Watchdog-timer interrupt
input               wdt_wkup;      // Watchdog Wakeup
input               wkup;          // System Wake-up (asynchronous)


//=============================================================================
// 1)  UTILITY FUNCTIONS
//=============================================================================

// 16 bits one-hot decoder
function [15:0] one_hot16;
   input  [3:0] binary;
   begin
      one_hot16         = 16'h0000;
      one_hot16[binary] =  1'b1;
   end
endfunction
   
// 8 bits one-hot decoder
function [7:0] one_hot8;
   input  [2:0] binary;
   begin
      one_hot8         = 8'h00;
      one_hot8[binary] = 1'b1;
   end
endfunction
   

//=============================================================================
// 2)  PARAMETER DEFINITIONS
//=============================================================================

//
// 2.1) Instruction State machine definitons
//-------------------------------------------

parameter I_IRQ_FETCH = `I_IRQ_FETCH;
parameter I_IRQ_DONE  = `I_IRQ_DONE;
parameter I_DEC       = `I_DEC;        // New instruction ready for decode
parameter I_EXT1      = `I_EXT1;       // 1st Extension word
parameter I_EXT2      = `I_EXT2;       // 2nd Extension word
parameter I_IDLE      = `I_IDLE;       // CPU is in IDLE mode

//
// 2.2) Execution State machine definitons
//-------------------------------------------

parameter E_IRQ_0     = `E_IRQ_0;
parameter E_IRQ_1     = `E_IRQ_1;
parameter E_IRQ_2     = `E_IRQ_2;
parameter E_IRQ_3     = `E_IRQ_3;
parameter E_IRQ_4     = `E_IRQ_4;
parameter E_SRC_AD    = `E_SRC_AD;
parameter E_SRC_RD    = `E_SRC_RD;
parameter E_SRC_WR    = `E_SRC_WR;
parameter E_DST_AD    = `E_DST_AD;
parameter E_DST_RD    = `E_DST_RD;
parameter E_DST_WR    = `E_DST_WR;
parameter E_EXEC      = `E_EXEC;
parameter E_JUMP      = `E_JUMP;
parameter E_IDLE      = `E_IDLE;


//=============================================================================
// 3)  FRONTEND STATE MACHINE
//=============================================================================

// The wire "conv" is used as state bits to calculate the next response
reg  [2:0] i_state;
reg  [2:0] i_state_nxt;

reg  [1:0] inst_sz;
wire [1:0] inst_sz_nxt;
wire       irq_detect;
wire [2:0] inst_type_nxt;
wire       is_const;
reg [15:0] sconst_nxt;
reg  [3:0] e_state_nxt;
           
// CPU on/off through the debug interface or cpu_en port
wire   cpu_halt_cmd = dbg_halt_cmd | ~cpu_en_s;
   
// States Transitions
always @(i_state    or inst_sz  or inst_sz_nxt  or pc_sw_wr or exec_done or
         irq_detect or cpuoff   or cpu_halt_cmd or e_state)
    case(i_state)
      I_IDLE     : i_state_nxt = (irq_detect & ~cpu_halt_cmd) ? I_IRQ_FETCH :
                                 (~cpuoff    & ~cpu_halt_cmd) ? I_DEC       : I_IDLE;
      I_IRQ_FETCH: i_state_nxt =  I_IRQ_DONE;
      I_IRQ_DONE : i_state_nxt =  I_DEC;
      I_DEC      : i_state_nxt =  irq_detect                  ? I_IRQ_FETCH :
                          (cpuoff | cpu_halt_cmd) & exec_done ? I_IDLE      :
                            cpu_halt_cmd & (e_state==E_IDLE)  ? I_IDLE      :
                                  pc_sw_wr                    ? I_DEC       :
                             ~exec_done & ~(e_state==E_IDLE)  ? I_DEC       :        // Wait in decode state
                                  (inst_sz_nxt!=2'b00)        ? I_EXT1      : I_DEC; // until execution is completed
      I_EXT1     : i_state_nxt =  pc_sw_wr                    ? I_DEC       : 
                                  (inst_sz!=2'b01)            ? I_EXT2      : I_DEC;
      I_EXT2     : i_state_nxt =  I_DEC;
    // pragma coverage off
      default    : i_state_nxt =  I_IRQ_FETCH;
    // pragma coverage on
    endcase

// State machine
always @(posedge mclk or posedge puc_rst)
  if (puc_rst) i_state  <= I_IRQ_FETCH;
  else         i_state  <= i_state_nxt;

// Utility signals
wire   decode_noirq =  ((i_state==I_DEC) &  (exec_done | (e_state==E_IDLE)));
wire   decode       =  decode_noirq | irq_detect;
wire   fetch        = ~((i_state==I_DEC) & ~(exec_done | (e_state==E_IDLE))) & ~(e_state_nxt==E_IDLE);

// Debug interface cpu status
reg    dbg_halt_st;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)  dbg_halt_st <= 1'b0;
  else          dbg_halt_st <= cpu_halt_cmd & (i_state_nxt==I_IDLE);


//=============================================================================
// 4)  INTERRUPT HANDLING & SYSTEM WAKEUP
//=============================================================================

//
// 4.1) INTERRUPT HANDLING
//-----------------------------------------

// Detect reset interrupt
reg         inst_irq_rst;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                  inst_irq_rst <= 1'b1;
  else if (exec_done)           inst_irq_rst <= 1'b0;

//  Detect other interrupts
assign  irq_detect = (nmi_pnd | ((|irq | wdt_irq) & gie)) & ~cpu_halt_cmd & ~dbg_halt_st & (exec_done | (i_state==I_IDLE));

`ifdef CLOCK_GATING
wire       mclk_irq_num;
omsp_clock_gate clock_gate_irq_num (.gclk(mclk_irq_num),
                                    .clk (mclk), .enable(irq_detect), .scan_enable(scan_enable));
`else
wire       mclk_irq_num = mclk;
`endif

// Select interrupt vector
reg  [3:0] irq_num;
always @(posedge mclk_irq_num or posedge puc_rst)
  if (puc_rst)         irq_num <= 4'hf;
`ifdef CLOCK_GATING
  else                 irq_num <= nmi_pnd            ?  4'he :
`else
  else if (irq_detect) irq_num <= nmi_pnd            ?  4'he :
`endif
                                  irq[13]            ?  4'hd :
                                  irq[12]            ?  4'hc :
                                  irq[11]            ?  4'hb :
                                 (irq[10] | wdt_irq) ?  4'ha :
                                  irq[9]             ?  4'h9 :
                                  irq[8]             ?  4'h8 :
                                  irq[7]             ?  4'h7 :
                                  irq[6]             ?  4'h6 :
                                  irq[5]             ?  4'h5 :
                                  irq[4]             ?  4'h4 :
                                  irq[3]             ?  4'h3 :
                                  irq[2]             ?  4'h2 :
                                  irq[1]             ?  4'h1 :
                                  irq[0]             ?  4'h0 : 4'hf;

wire [15:0] irq_addr    = {11'h7ff, irq_num, 1'b0};

// Interrupt request accepted
wire [15:0] irq_acc_all = one_hot16(irq_num) & {16{(i_state==I_IRQ_FETCH)}};
wire [13:0] irq_acc     = irq_acc_all[13:0];
wire        nmi_acc     = irq_acc_all[14];

//
// 4.2) SYSTEM WAKEUP
//-----------------------------------------
`ifdef CPUOFF_EN

// Generate the main system clock enable signal
                                                    // Keep the clock running if:
wire mclk_enable = inst_irq_rst ? cpu_en_s :        //      - the RESET interrupt is currently executing
                                                    //        and if the CPU is enabled
                                                    // otherwise if:
                  ~((cpuoff | ~cpu_en_s) &          //      - the CPUOFF flag, cpu_en command, instruction
                   (i_state==I_IDLE) &              //        and execution state machines are all two
                   (e_state==E_IDLE));              //        not idle.

   
// Wakeup condition from maskable interrupts
wire mirq_wkup;
omsp_and_gate and_mirq_wkup (.y(mirq_wkup), .a(wkup | wdt_wkup), .b(gie));

// Combined asynchronous wakeup detection from nmi & irq (masked if the cpu is disabled)
omsp_and_gate and_mclk_wkup (.y(mclk_wkup), .a(nmi_wkup | mirq_wkup), .b(cpu_en_s));

`else

// In the CPUOFF feature is disabled, the wake-up and enable signals are always 1
assign  mclk_wkup   = 1'b1;
assign  mclk_enable = 1'b1;
`endif

//=============================================================================
// 5)  FETCH INSTRUCTION
//=============================================================================

//
// 5.1) PROGRAM COUNTER & MEMORY INTERFACE
//-----------------------------------------

// Program counter
reg  [15:0] pc;

// Compute next PC value
wire [15:0] pc_incr = pc + {14'h0000, fetch, 1'b0};
wire [15:0] pc_nxt  = pc_sw_wr               ? pc_sw    :
                      (i_state==I_IRQ_FETCH) ? irq_addr :
                      (i_state==I_IRQ_DONE)  ? mdb_in   :  pc_incr;

`ifdef CLOCK_GATING
wire       pc_en  = fetch                  |
                    pc_sw_wr               |
                    (i_state==I_IRQ_FETCH) |
                    (i_state==I_IRQ_DONE);
wire       mclk_pc;
omsp_clock_gate clock_gate_pc (.gclk(mclk_pc),
                               .clk (mclk), .enable(pc_en), .scan_enable(scan_enable));
`else
wire       mclk_pc = mclk;
`endif

always @(posedge mclk_pc or posedge puc_rst)
  if (puc_rst)  pc <= 16'h0000;
  else          pc <= pc_nxt;

// Check if ROM has been busy in order to retry ROM access
reg pmem_busy;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)  pmem_busy <= 1'b0;
  else          pmem_busy <= fe_pmem_wait;
   
// Memory interface
wire [15:0] mab      = pc_nxt;
wire        mb_en    = fetch | pc_sw_wr | (i_state==I_IRQ_FETCH) | pmem_busy | (dbg_halt_st & ~cpu_halt_cmd);


//
// 5.2) INSTRUCTION REGISTER
//--------------------------------

// Instruction register
wire [15:0] ir  = mdb_in;

// Detect if source extension word is required
wire is_sext = (inst_as[`IDX] | inst_as[`SYMB] | inst_as[`ABS] | inst_as[`IMM]);

// For the Symbolic addressing mode, add -2 to the extension word in order
// to make up for the PC address
wire [15:0] ext_incr = ((i_state==I_EXT1)     &  inst_as[`SYMB]) |
                       ((i_state==I_EXT2)     &  inst_ad[`SYMB]) |
                       ((i_state==I_EXT1)     & ~inst_as[`SYMB] &
                       ~(i_state_nxt==I_EXT2) &  inst_ad[`SYMB])   ? 16'hfffe : 16'h0000;

wire [15:0] ext_nxt  = ir + ext_incr;

// Store source extension word
reg [15:0] inst_sext;

`ifdef CLOCK_GATING
wire       inst_sext_en  = (decode & is_const)                 |
                           (decode & inst_type_nxt[`INST_JMP]) |
                           ((i_state==I_EXT1) & is_sext);
wire       mclk_inst_sext;
omsp_clock_gate clock_gate_inst_sext (.gclk(mclk_inst_sext),
                                      .clk (mclk), .enable(inst_sext_en), .scan_enable(scan_enable));
`else
wire       mclk_inst_sext = mclk;
`endif

always @(posedge mclk_inst_sext or posedge puc_rst)
  if (puc_rst)                                 inst_sext <= 16'h0000;
  else if (decode & is_const)                  inst_sext <= sconst_nxt;
  else if (decode & inst_type_nxt[`INST_JMP])  inst_sext <= {{5{ir[9]}},ir[9:0],1'b0};
`ifdef CLOCK_GATING
  else                                         inst_sext <= ext_nxt;
`else
  else if ((i_state==I_EXT1) & is_sext)        inst_sext <= ext_nxt;
`endif

// Source extension word is ready
wire inst_sext_rdy = (i_state==I_EXT1) & is_sext;


// Store destination extension word
reg [15:0] inst_dext;

`ifdef CLOCK_GATING
wire       inst_dext_en  = ((i_state==I_EXT1) & ~is_sext) |
                            (i_state==I_EXT2);
wire       mclk_inst_dext;
omsp_clock_gate clock_gate_inst_dext (.gclk(mclk_inst_dext),
                                      .clk (mclk), .enable(inst_dext_en), .scan_enable(scan_enable));
`else
wire       mclk_inst_dext = mclk;
`endif

always @(posedge mclk_inst_dext or posedge puc_rst)
  if (puc_rst)                           inst_dext <= 16'h0000;
  else if ((i_state==I_EXT1) & ~is_sext) inst_dext <= ext_nxt;
`ifdef CLOCK_GATING
  else                                   inst_dext <= ext_nxt;
`else
  else if  (i_state==I_EXT2)             inst_dext <= ext_nxt;
`endif

// Destination extension word is ready
wire inst_dext_rdy = (((i_state==I_EXT1) & ~is_sext) | (i_state==I_EXT2));


//=============================================================================
// 6)  DECODE INSTRUCTION
//=============================================================================

`ifdef CLOCK_GATING
wire       mclk_decode;
omsp_clock_gate clock_gate_decode (.gclk(mclk_decode),
                                   .clk (mclk), .enable(decode), .scan_enable(scan_enable));
`else
wire       mclk_decode = mclk;
`endif

//
// 6.1) OPCODE: INSTRUCTION TYPE
//----------------------------------------
// Instructions type is encoded in a one hot fashion as following:
//
// 3'b001: Single-operand arithmetic
// 3'b010: Conditional jump
// 3'b100: Two-operand arithmetic

reg  [2:0] inst_type;
assign     inst_type_nxt = {(ir[15:14]!=2'b00),
                            (ir[15:13]==3'b001),
                            (ir[15:13]==3'b000)} & {3{~irq_detect}};
   
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)      inst_type <= 3'b000;
`ifdef CLOCK_GATING
  else              inst_type <= inst_type_nxt;
`else
  else if (decode)  inst_type <= inst_type_nxt;
`endif

//
// 6.2) OPCODE: SINGLE-OPERAND ARITHMETIC
//----------------------------------------
// Instructions are encoded in a one hot fashion as following:
//
// 8'b00000001: RRC
// 8'b00000010: SWPB
// 8'b00000100: RRA
// 8'b00001000: SXT
// 8'b00010000: PUSH
// 8'b00100000: CALL
// 8'b01000000: RETI
// 8'b10000000: IRQ

reg   [7:0] inst_so;
wire  [7:0] inst_so_nxt = irq_detect ? 8'h80 : (one_hot8(ir[9:7]) & {8{inst_type_nxt[`INST_SO]}});

always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_so <= 8'h00;
`ifdef CLOCK_GATING
  else             inst_so <= inst_so_nxt;
`else
  else if (decode) inst_so <= inst_so_nxt;
`endif

//
// 6.3) OPCODE: CONDITIONAL JUMP
//--------------------------------
// Instructions are encoded in a one hot fashion as following:
//
// 8'b00000001: JNE/JNZ
// 8'b00000010: JEQ/JZ
// 8'b00000100: JNC/JLO
// 8'b00001000: JC/JHS
// 8'b00010000: JN
// 8'b00100000: JGE
// 8'b01000000: JL
// 8'b10000000: JMP

reg   [2:0] inst_jmp_bin;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_jmp_bin <= 3'h0;
`ifdef CLOCK_GATING
  else             inst_jmp_bin <= ir[12:10];
`else
  else if (decode) inst_jmp_bin <= ir[12:10];
`endif

wire [7:0] inst_jmp = one_hot8(inst_jmp_bin) & {8{inst_type[`INST_JMP]}};


//
// 6.4) OPCODE: TWO-OPERAND ARITHMETIC
//-------------------------------------
// Instructions are encoded in a one hot fashion as following:
//
// 12'b000000000001: MOV
// 12'b000000000010: ADD
// 12'b000000000100: ADDC
// 12'b000000001000: SUBC
// 12'b000000010000: SUB
// 12'b000000100000: CMP
// 12'b000001000000: DADD
// 12'b000010000000: BIT
// 12'b000100000000: BIC
// 12'b001000000000: BIS
// 12'b010000000000: XOR
// 12'b100000000000: AND

wire [15:0] inst_to_1hot = one_hot16(ir[15:12]) & {16{inst_type_nxt[`INST_TO]}};
wire [11:0] inst_to_nxt  = inst_to_1hot[15:4];

reg         inst_mov;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_mov <= 1'b0;
`ifdef CLOCK_GATING
  else             inst_mov <= inst_to_nxt[`MOV];
`else
  else if (decode) inst_mov <= inst_to_nxt[`MOV];
`endif


//
// 6.5) SOURCE AND DESTINATION REGISTERS
//---------------------------------------

// Destination register
reg [3:0] inst_dest_bin;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_dest_bin <= 4'h0;
`ifdef CLOCK_GATING
  else             inst_dest_bin <= ir[3:0];
`else
  else if (decode) inst_dest_bin <= ir[3:0];
`endif

wire  [15:0] inst_dest = dbg_halt_st          ? one_hot16(dbg_reg_sel) :
                         inst_type[`INST_JMP] ? 16'h0001               :
                         inst_so[`IRQ]  |
                         inst_so[`PUSH] |
                         inst_so[`CALL]       ? 16'h0002               :
                                                one_hot16(inst_dest_bin);


// Source register
reg [3:0] inst_src_bin;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_src_bin <= 4'h0;
`ifdef CLOCK_GATING
  else             inst_src_bin <= ir[11:8];
`else
  else if (decode) inst_src_bin <= ir[11:8];
`endif

wire  [15:0] inst_src = inst_type[`INST_TO] ? one_hot16(inst_src_bin)  :
                        inst_so[`RETI]      ? 16'h0002                 :
                        inst_so[`IRQ]       ? 16'h0001                 :
                        inst_type[`INST_SO] ? one_hot16(inst_dest_bin) : 16'h0000;


//
// 6.6) SOURCE ADDRESSING MODES
//--------------------------------
// Source addressing modes are encoded in a one hot fashion as following:
//
// 13'b0000000000001: Register direct.
// 13'b0000000000010: Register indexed.
// 13'b0000000000100: Register indirect.
// 13'b0000000001000: Register indirect autoincrement.
// 13'b0000000010000: Symbolic (operand is in memory at address PC+x).
// 13'b0000000100000: Immediate (operand is next word in the instruction stream).
// 13'b0000001000000: Absolute (operand is in memory at address x).
// 13'b0000010000000: Constant 4.
// 13'b0000100000000: Constant 8.
// 13'b0001000000000: Constant 0.
// 13'b0010000000000: Constant 1.
// 13'b0100000000000: Constant 2.
// 13'b1000000000000: Constant -1.

reg [12:0] inst_as_nxt;

wire [3:0] src_reg = inst_type_nxt[`INST_SO] ? ir[3:0] : ir[11:8];

always @(src_reg or ir or inst_type_nxt)
  begin
     if (inst_type_nxt[`INST_JMP])
       inst_as_nxt =  13'b0000000000001;
     else if (src_reg==4'h3) // Addressing mode using R3
       case (ir[5:4])
         2'b11  : inst_as_nxt =  13'b1000000000000;
         2'b10  : inst_as_nxt =  13'b0100000000000;
         2'b01  : inst_as_nxt =  13'b0010000000000;
         default: inst_as_nxt =  13'b0001000000000;
       endcase
     else if (src_reg==4'h2) // Addressing mode using R2
       case (ir[5:4])
         2'b11  : inst_as_nxt =  13'b0000100000000;
         2'b10  : inst_as_nxt =  13'b0000010000000;
         2'b01  : inst_as_nxt =  13'b0000001000000;
         default: inst_as_nxt =  13'b0000000000001;
       endcase
     else if (src_reg==4'h0) // Addressing mode using R0
       case (ir[5:4])
         2'b11  : inst_as_nxt =  13'b0000000100000;
         2'b10  : inst_as_nxt =  13'b0000000000100;
         2'b01  : inst_as_nxt =  13'b0000000010000;
         default: inst_as_nxt =  13'b0000000000001;
       endcase
     else                    // General Addressing mode
       case (ir[5:4])
         2'b11  : inst_as_nxt =  13'b0000000001000;
         2'b10  : inst_as_nxt =  13'b0000000000100;
         2'b01  : inst_as_nxt =  13'b0000000000010;
         default: inst_as_nxt =  13'b0000000000001;
       endcase
  end
assign    is_const = |inst_as_nxt[12:7];

reg [7:0] inst_as;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_as <= 8'h00;
`ifdef CLOCK_GATING
  else             inst_as <= {is_const, inst_as_nxt[6:0]};
`else
  else if (decode) inst_as <= {is_const, inst_as_nxt[6:0]};
`endif


// 13'b0000010000000: Constant 4.
// 13'b0000100000000: Constant 8.
// 13'b0001000000000: Constant 0.
// 13'b0010000000000: Constant 1.
// 13'b0100000000000: Constant 2.
// 13'b1000000000000: Constant -1.
always @(inst_as_nxt)
  begin
     if (inst_as_nxt[7])        sconst_nxt = 16'h0004;
     else if (inst_as_nxt[8])   sconst_nxt = 16'h0008;
     else if (inst_as_nxt[9])   sconst_nxt = 16'h0000;
     else if (inst_as_nxt[10])  sconst_nxt = 16'h0001;
     else if (inst_as_nxt[11])  sconst_nxt = 16'h0002;
     else if (inst_as_nxt[12])  sconst_nxt = 16'hffff;
     else                       sconst_nxt = 16'h0000;
  end


//
// 6.7) DESTINATION ADDRESSING MODES
//-----------------------------------
// Destination addressing modes are encoded in a one hot fashion as following:
//
// 8'b00000001: Register direct.
// 8'b00000010: Register indexed.
// 8'b00010000: Symbolic (operand is in memory at address PC+x).
// 8'b01000000: Absolute (operand is in memory at address x).

reg  [7:0] inst_ad_nxt;

wire [3:0] dest_reg = ir[3:0];

always @(dest_reg or ir or inst_type_nxt)
  begin
     if (~inst_type_nxt[`INST_TO])
       inst_ad_nxt =  8'b00000000;
     else if (dest_reg==4'h2)   // Addressing mode using R2
       case (ir[7])
         1'b1   : inst_ad_nxt =  8'b01000000;
         default: inst_ad_nxt =  8'b00000001;
       endcase
     else if (dest_reg==4'h0)   // Addressing mode using R0
       case (ir[7])
         1'b1   : inst_ad_nxt =  8'b00010000;
         default: inst_ad_nxt =  8'b00000001;
       endcase
     else                       // General Addressing mode
       case (ir[7])
         1'b1   : inst_ad_nxt =  8'b00000010;
         default: inst_ad_nxt =  8'b00000001;
       endcase
  end

reg [7:0] inst_ad;
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_ad <= 8'h00;
`ifdef CLOCK_GATING
  else             inst_ad <= inst_ad_nxt;
`else
  else if (decode) inst_ad <= inst_ad_nxt;
`endif


//
// 6.8) REMAINING INSTRUCTION DECODING
//-------------------------------------

// Operation size
reg       inst_bw;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)     inst_bw     <= 1'b0;
  else if (decode) inst_bw     <= ir[6] & ~inst_type_nxt[`INST_JMP] & ~irq_detect & ~cpu_halt_cmd;

// Extended instruction size
assign    inst_sz_nxt = {1'b0,  (inst_as_nxt[`IDX] | inst_as_nxt[`SYMB] | inst_as_nxt[`ABS] | inst_as_nxt[`IMM])} +
                        {1'b0, ((inst_ad_nxt[`IDX] | inst_ad_nxt[`SYMB] | inst_ad_nxt[`ABS]) & ~inst_type_nxt[`INST_SO])};
always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_sz     <= 2'b00;
`ifdef CLOCK_GATING
  else             inst_sz     <= inst_sz_nxt;
`else
  else if (decode) inst_sz     <= inst_sz_nxt;
`endif


//=============================================================================
// 7)  EXECUTION-UNIT STATE MACHINE
//=============================================================================

// State machine registers
reg  [3:0] e_state;


// State machine control signals
//--------------------------------

wire src_acalc_pre =  inst_as_nxt[`IDX]   | inst_as_nxt[`SYMB]    | inst_as_nxt[`ABS];
wire src_rd_pre    =  inst_as_nxt[`INDIR] | inst_as_nxt[`INDIR_I] | inst_as_nxt[`IMM]  | inst_so_nxt[`RETI];
wire dst_acalc_pre =  inst_ad_nxt[`IDX]   | inst_ad_nxt[`SYMB]    | inst_ad_nxt[`ABS];
wire dst_acalc     =  inst_ad[`IDX]       | inst_ad[`SYMB]        | inst_ad[`ABS];
wire dst_rd_pre    =  inst_ad_nxt[`IDX]   | inst_so_nxt[`PUSH]    | inst_so_nxt[`CALL] | inst_so_nxt[`RETI];
wire dst_rd        =  inst_ad[`IDX]       | inst_so[`PUSH]        | inst_so[`CALL]     | inst_so[`RETI];

wire inst_branch   =  (inst_ad_nxt[`DIR] & (ir[3:0]==4'h0)) | inst_type_nxt[`INST_JMP] | inst_so_nxt[`RETI];

reg exec_jmp;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                   exec_jmp <= 1'b0;
  else if (inst_branch & decode) exec_jmp <= 1'b1;
  else if (e_state==E_JUMP)      exec_jmp <= 1'b0;

reg exec_dst_wr;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                exec_dst_wr <= 1'b0;
  else if (e_state==E_DST_RD) exec_dst_wr <= 1'b1;
  else if (e_state==E_DST_WR) exec_dst_wr <= 1'b0;

reg exec_src_wr;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                                         exec_src_wr <= 1'b0;
  else if (inst_type[`INST_SO] & (e_state==E_SRC_RD))  exec_src_wr <= 1'b1;
  else if ((e_state==E_SRC_WR) || (e_state==E_DST_WR)) exec_src_wr <= 1'b0;

reg exec_dext_rdy;
always @(posedge mclk or posedge puc_rst)
  if (puc_rst)                exec_dext_rdy <= 1'b0;
  else if (e_state==E_DST_RD) exec_dext_rdy <= 1'b0;
  else if (inst_dext_rdy)     exec_dext_rdy <= 1'b1;

// Execution first state
wire [3:0] e_first_state = ~dbg_halt_st  & inst_so_nxt[`IRQ] ? E_IRQ_0  :
                            cpu_halt_cmd | (i_state==I_IDLE) ? E_IDLE   :
                            cpuoff                           ? E_IDLE   :
                            src_acalc_pre                    ? E_SRC_AD :
                            src_rd_pre                       ? E_SRC_RD :
                            dst_acalc_pre                    ? E_DST_AD :
                            dst_rd_pre                       ? E_DST_RD : E_EXEC;


// State machine
//--------------------------------

// States Transitions
always @(e_state       or dst_acalc     or dst_rd   or inst_sext_rdy or
         inst_dext_rdy or exec_dext_rdy or exec_jmp or exec_dst_wr   or
         e_first_state or exec_src_wr)
    case(e_state)
      E_IDLE   : e_state_nxt =  e_first_state;
      E_IRQ_0  : e_state_nxt =  E_IRQ_1;
      E_IRQ_1  : e_state_nxt =  E_IRQ_2;
      E_IRQ_2  : e_state_nxt =  E_IRQ_3;
      E_IRQ_3  : e_state_nxt =  E_IRQ_4;
      E_IRQ_4  : e_state_nxt =  E_EXEC;

      E_SRC_AD : e_state_nxt =  inst_sext_rdy     ? E_SRC_RD : E_SRC_AD;

      E_SRC_RD : e_state_nxt =  dst_acalc         ? E_DST_AD : 
                                 dst_rd           ? E_DST_RD : E_EXEC;

      E_DST_AD : e_state_nxt =  (inst_dext_rdy |
                                 exec_dext_rdy)   ? E_DST_RD : E_DST_AD;

      E_DST_RD : e_state_nxt =  E_EXEC;

      E_EXEC   : e_state_nxt =  exec_dst_wr       ? E_DST_WR :
                                exec_jmp          ? E_JUMP   :
                                exec_src_wr       ? E_SRC_WR : e_first_state;

      E_JUMP   : e_state_nxt =  e_first_state;
      E_DST_WR : e_state_nxt =  exec_jmp          ? E_JUMP   : e_first_state;
      E_SRC_WR : e_state_nxt =  e_first_state;
    // pragma coverage off
      default  : e_state_nxt =  E_IRQ_0;
    // pragma coverage on
    endcase

// State machine
always @(posedge mclk or posedge puc_rst)
  if (puc_rst) e_state  <= E_IRQ_1;
  else         e_state  <= e_state_nxt;


// Frontend State machine control signals
//----------------------------------------

wire exec_done = exec_jmp        ? (e_state==E_JUMP)   :
                 exec_dst_wr     ? (e_state==E_DST_WR) :
                 exec_src_wr     ? (e_state==E_SRC_WR) : (e_state==E_EXEC);


//=============================================================================
// 8)  EXECUTION-UNIT STATE CONTROL
//=============================================================================

//
// 8.1) ALU CONTROL SIGNALS
//-------------------------------------
//
// 12'b000000000001: Enable ALU source inverter
// 12'b000000000010: Enable Incrementer
// 12'b000000000100: Enable Incrementer on carry bit
// 12'b000000001000: Select Adder
// 12'b000000010000: Select AND
// 12'b000000100000: Select OR
// 12'b000001000000: Select XOR
// 12'b000010000000: Select DADD
// 12'b000100000000: Update N, Z & C (C=~Z)
// 12'b001000000000: Update all status bits
// 12'b010000000000: Update status bit for XOR instruction
// 12'b100000000000: Don't write to destination

reg  [11:0] inst_alu;

wire        alu_src_inv   = inst_to_nxt[`SUB]  | inst_to_nxt[`SUBC] |
                            inst_to_nxt[`CMP]  | inst_to_nxt[`BIC] ;

wire        alu_inc       = inst_to_nxt[`SUB]  | inst_to_nxt[`CMP];

wire        alu_inc_c     = inst_to_nxt[`ADDC] | inst_to_nxt[`DADD] |
                            inst_to_nxt[`SUBC];

wire        alu_add       = inst_to_nxt[`ADD]  | inst_to_nxt[`ADDC]       |
                            inst_to_nxt[`SUB]  | inst_to_nxt[`SUBC]       |
                            inst_to_nxt[`CMP]  | inst_type_nxt[`INST_JMP] |
                            inst_so_nxt[`RETI];

 
wire        alu_and       = inst_to_nxt[`AND]  | inst_to_nxt[`BIC]  |
                            inst_to_nxt[`BIT];

wire        alu_or        = inst_to_nxt[`BIS];

wire        alu_xor       = inst_to_nxt[`XOR];

wire        alu_dadd      = inst_to_nxt[`DADD];

wire        alu_stat_7    = inst_to_nxt[`BIT]  | inst_to_nxt[`AND]  |
                            inst_so_nxt[`SXT];

wire        alu_stat_f    = inst_to_nxt[`ADD]  | inst_to_nxt[`ADDC] |
                            inst_to_nxt[`SUB]  | inst_to_nxt[`SUBC] |
                            inst_to_nxt[`CMP]  | inst_to_nxt[`DADD] |
                            inst_to_nxt[`BIT]  | inst_to_nxt[`XOR]  |
                            inst_to_nxt[`AND]  |
                            inst_so_nxt[`RRC]  | inst_so_nxt[`RRA]  |
                            inst_so_nxt[`SXT];

wire        alu_shift     = inst_so_nxt[`RRC]  | inst_so_nxt[`RRA];

wire        exec_no_wr    = inst_to_nxt[`CMP] | inst_to_nxt[`BIT];

wire [11:0] inst_alu_nxt  = {exec_no_wr,
                             alu_shift,
                             alu_stat_f,
                             alu_stat_7,
                             alu_dadd,
                             alu_xor,
                             alu_or,
                             alu_and,
                             alu_add,
                             alu_inc_c,
                             alu_inc,
                             alu_src_inv};

always @(posedge mclk_decode or posedge puc_rst)
  if (puc_rst)     inst_alu <= 12'h000;
`ifdef CLOCK_GATING
  else             inst_alu <= inst_alu_nxt;
`else
  else if (decode) inst_alu <= inst_alu_nxt;
`endif


endmodule // omsp_frontend

`ifdef OMSP_NO_INCLUDE
`else
`include "openMSP430_undefines.v"
`endif
