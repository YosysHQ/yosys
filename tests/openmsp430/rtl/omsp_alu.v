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
// *File Name: omsp_alu.v
// 
// *Module Description:
//                       openMSP430 ALU
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

module  omsp_alu (

// OUTPUTs
    alu_out,                       // ALU output value
    alu_out_add,                   // ALU adder output value
    alu_stat,                      // ALU Status {V,N,Z,C}
    alu_stat_wr,                   // ALU Status write {V,N,Z,C}

// INPUTs
    dbg_halt_st,                   // Halt/Run status from CPU
    exec_cycle,                    // Instruction execution cycle
    inst_alu,                      // ALU control signals
    inst_bw,                       // Decoded Inst: byte width
    inst_jmp,                      // Decoded Inst: Conditional jump
    inst_so,                       // Single-operand arithmetic
    op_dst,                        // Destination operand
    op_src,                        // Source operand
    status                         // R2 Status {V,N,Z,C}
);

// OUTPUTs
//=========
output       [15:0] alu_out;       // ALU output value
output       [15:0] alu_out_add;   // ALU adder output value
output        [3:0] alu_stat;      // ALU Status {V,N,Z,C}
output        [3:0] alu_stat_wr;   // ALU Status write {V,N,Z,C}

// INPUTs
//=========
input               dbg_halt_st;   // Halt/Run status from CPU
input               exec_cycle;    // Instruction execution cycle
input        [11:0] inst_alu;      // ALU control signals
input               inst_bw;       // Decoded Inst: byte width
input         [7:0] inst_jmp;      // Decoded Inst: Conditional jump
input         [7:0] inst_so;       // Single-operand arithmetic
input        [15:0] op_dst;        // Destination operand
input        [15:0] op_src;        // Source operand
input         [3:0] status;        // R2 Status {V,N,Z,C}


//=============================================================================
// 1)  FUNCTIONS
//=============================================================================

function [4:0] bcd_add;

   input [3:0] X;
   input [3:0] Y;
   input       C_;

   reg   [4:0] Z_;
   begin
      Z_ = {1'b0,X}+{1'b0,Y}+{4'b0,C_};
      if (Z_<5'd10) bcd_add = Z_;
      else          bcd_add = Z_+5'd6;
   end

endfunction


//=============================================================================
// 2)  INSTRUCTION FETCH/DECODE CONTROL STATE MACHINE
//=============================================================================
// SINGLE-OPERAND ARITHMETIC:
//-----------------------------------------------------------------------------
//   Mnemonic   S-Reg,   Operation                               Status bits
//              D-Reg,                                            V  N  Z  C
//
//   RRC         dst     C->MSB->...LSB->C                        *  *  *  *
//   RRA         dst     MSB->MSB->...LSB->C                      0  *  *  *
//   SWPB        dst     Swap bytes                               -  -  -  -
//   SXT         dst     Bit7->Bit8...Bit15                       0  *  *  *
//   PUSH        src     SP-2->SP, src->@SP                       -  -  -  -
//   CALL        dst     SP-2->SP, PC+2->@SP, dst->PC             -  -  -  -
//   RETI                TOS->SR, SP+2->SP, TOS->PC, SP+2->SP     *  *  *  *
//
//-----------------------------------------------------------------------------
// TWO-OPERAND ARITHMETIC:
//-----------------------------------------------------------------------------
//   Mnemonic   S-Reg,   Operation                               Status bits
//              D-Reg,                                            V  N  Z  C
//
//   MOV       src,dst    src            -> dst                   -  -  -  -
//   ADD       src,dst    src +  dst     -> dst                   *  *  *  *
//   ADDC      src,dst    src +  dst + C -> dst                   *  *  *  *
//   SUB       src,dst    dst + ~src + 1 -> dst                   *  *  *  *
//   SUBC      src,dst    dst + ~src + C -> dst                   *  *  *  *
//   CMP       src,dst    dst + ~src + 1                          *  *  *  *
//   DADD      src,dst    src +  dst + C -> dst (decimaly)        *  *  *  *
//   BIT       src,dst    src &  dst                              0  *  *  *
//   BIC       src,dst   ~src &  dst     -> dst                   -  -  -  -
//   BIS       src,dst    src |  dst     -> dst                   -  -  -  -
//   XOR       src,dst    src ^  dst     -> dst                   *  *  *  *
//   AND       src,dst    src &  dst     -> dst                   0  *  *  *
//
//-----------------------------------------------------------------------------
// * the status bit is affected
// - the status bit is not affected
// 0 the status bit is cleared
// 1 the status bit is set
//-----------------------------------------------------------------------------

// Invert source for substract and compare instructions.
wire        op_src_inv_cmd = exec_cycle & (inst_alu[`ALU_SRC_INV]);
wire [15:0] op_src_inv     = {16{op_src_inv_cmd}} ^ op_src;


// Mask the bit 8 for the Byte instructions for correct flags generation
wire        op_bit8_msk     = ~exec_cycle | ~inst_bw;
wire [16:0] op_src_in       = {1'b0, {op_src_inv[15:8] & {8{op_bit8_msk}}}, op_src_inv[7:0]};
wire [16:0] op_dst_in       = {1'b0, {op_dst[15:8]     & {8{op_bit8_msk}}}, op_dst[7:0]};

// Clear the source operand (= jump offset) for conditional jumps
wire        jmp_not_taken  = (inst_jmp[`JL]  & ~(status[3]^status[2])) |
                             (inst_jmp[`JGE] &  (status[3]^status[2])) |
                             (inst_jmp[`JN]  &  ~status[2])            |
                             (inst_jmp[`JC]  &  ~status[0])            |
                             (inst_jmp[`JNC] &   status[0])            |
                             (inst_jmp[`JEQ] &  ~status[1])            |
                             (inst_jmp[`JNE] &   status[1]);
wire [16:0] op_src_in_jmp  = op_src_in & {17{~jmp_not_taken}};

// Adder / AND / OR / XOR
wire [16:0] alu_add        = op_src_in_jmp + op_dst_in;
wire [16:0] alu_and        = op_src_in     & op_dst_in;
wire [16:0] alu_or         = op_src_in     | op_dst_in;
wire [16:0] alu_xor        = op_src_in     ^ op_dst_in;


// Incrementer
wire        alu_inc         = exec_cycle & ((inst_alu[`ALU_INC_C] & status[0]) |
                                             inst_alu[`ALU_INC]);
wire [16:0] alu_add_inc    = alu_add + {16'h0000, alu_inc};



// Decimal adder (DADD)
wire  [4:0] alu_dadd0      = bcd_add(op_src_in[3:0],   op_dst_in[3:0],  status[0]);
wire  [4:0] alu_dadd1      = bcd_add(op_src_in[7:4],   op_dst_in[7:4],  alu_dadd0[4]);
wire  [4:0] alu_dadd2      = bcd_add(op_src_in[11:8],  op_dst_in[11:8], alu_dadd1[4]);
wire  [4:0] alu_dadd3      = bcd_add(op_src_in[15:12], op_dst_in[15:12],alu_dadd2[4]);
wire [16:0] alu_dadd       = {alu_dadd3, alu_dadd2[3:0], alu_dadd1[3:0], alu_dadd0[3:0]};


// Shifter for rotate instructions (RRC & RRA)
wire        alu_shift_msb  = inst_so[`RRC] ? status[0]     :
	                     inst_bw       ? op_src[7]     : op_src[15];
wire        alu_shift_7    = inst_bw       ? alu_shift_msb : op_src[8];
wire [16:0] alu_shift      = {1'b0, alu_shift_msb, op_src[15:9], alu_shift_7, op_src[7:1]};


// Swap bytes / Extend Sign
wire [16:0] alu_swpb       = {1'b0, op_src[7:0],op_src[15:8]};
wire [16:0] alu_sxt        = {1'b0, {8{op_src[7]}},op_src[7:0]};


// Combine short paths toghether to simplify final ALU mux
wire        alu_short_thro = ~(inst_alu[`ALU_AND]   |
                               inst_alu[`ALU_OR]    |
                               inst_alu[`ALU_XOR]   |
                               inst_alu[`ALU_SHIFT] |
                               inst_so[`SWPB]       |
                               inst_so[`SXT]);

wire [16:0] alu_short      = ({17{inst_alu[`ALU_AND]}}   & alu_and)   |
                             ({17{inst_alu[`ALU_OR]}}    & alu_or)    |
                             ({17{inst_alu[`ALU_XOR]}}   & alu_xor)   |
                             ({17{inst_alu[`ALU_SHIFT]}} & alu_shift) |
                             ({17{inst_so[`SWPB]}}       & alu_swpb)  |
                             ({17{inst_so[`SXT]}}        & alu_sxt)   |
                             ({17{alu_short_thro}}       & op_src_in);


// ALU output mux
wire [16:0] alu_out_nxt    = (inst_so[`IRQ] | dbg_halt_st |
                              inst_alu[`ALU_ADD]) ? alu_add_inc :
                              inst_alu[`ALU_DADD] ? alu_dadd    : alu_short;

assign      alu_out        =  alu_out_nxt[15:0];
assign      alu_out_add    =  alu_add[15:0];


//-----------------------------------------------------------------------------
// STATUS FLAG GENERATION
//-----------------------------------------------------------------------------

wire    V_xor       = inst_bw ? (op_src_in[7]  & op_dst_in[7])  :
                                (op_src_in[15] & op_dst_in[15]);

wire    V           = inst_bw ? ((~op_src_in[7]  & ~op_dst_in[7]  &  alu_out[7])  |
                                 ( op_src_in[7]  &  op_dst_in[7]  & ~alu_out[7])) :
                                ((~op_src_in[15] & ~op_dst_in[15] &  alu_out[15]) |
                                 ( op_src_in[15] &  op_dst_in[15] & ~alu_out[15]));

wire    N           = inst_bw ?  alu_out[7]       : alu_out[15];
wire    Z           = inst_bw ? (alu_out[7:0]==0) : (alu_out==0);
wire    C           = inst_bw ?  alu_out[8]       : alu_out_nxt[16];

assign  alu_stat    = inst_alu[`ALU_SHIFT]  ? {1'b0, N,Z,op_src_in[0]} :
                      inst_alu[`ALU_STAT_7] ? {1'b0, N,Z,~Z}           :
                      inst_alu[`ALU_XOR]    ? {V_xor,N,Z,~Z}           : {V,N,Z,C};

assign  alu_stat_wr = (inst_alu[`ALU_STAT_F] & exec_cycle) ? 4'b1111 : 4'b0000;


endmodule // omsp_alu

`ifdef OMSP_NO_INCLUDE
`else
`include "openMSP430_undefines.v"
`endif
