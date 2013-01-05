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
// *File Name: openMSP430_undefines.v
// 
// *Module Description:
//                      openMSP430 Verilog `undef file
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 23 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2009-08-30 18:39:26 +0200 (Sun, 30 Aug 2009) $
//----------------------------------------------------------------------------

//----------------------------------------------------------------------------
// BASIC SYSTEM CONFIGURATION
//----------------------------------------------------------------------------

// Program Memory sizes
`ifdef PMEM_SIZE_59_KB
`undef PMEM_SIZE_59_KB
`endif
`ifdef PMEM_SIZE_55_KB
`undef PMEM_SIZE_55_KB
`endif
`ifdef PMEM_SIZE_54_KB
`undef PMEM_SIZE_54_KB
`endif
`ifdef PMEM_SIZE_51_KB
`undef PMEM_SIZE_51_KB
`endif
`ifdef PMEM_SIZE_48_KB
`undef PMEM_SIZE_48_KB
`endif
`ifdef PMEM_SIZE_41_KB
`undef PMEM_SIZE_41_KB
`endif
`ifdef PMEM_SIZE_32_KB
`undef PMEM_SIZE_32_KB
`endif
`ifdef PMEM_SIZE_24_KB
`undef PMEM_SIZE_24_KB
`endif
`ifdef PMEM_SIZE_16_KB
`undef PMEM_SIZE_16_KB
`endif
`ifdef PMEM_SIZE_12_KB
`undef PMEM_SIZE_12_KB
`endif
`ifdef PMEM_SIZE_8_KB
`undef PMEM_SIZE_8_KB
`endif
`ifdef PMEM_SIZE_4_KB
`undef PMEM_SIZE_4_KB
`endif
`ifdef PMEM_SIZE_2_KB
`undef PMEM_SIZE_2_KB
`endif
`ifdef PMEM_SIZE_1_KB
`undef PMEM_SIZE_1_KB
`endif

// Data Memory sizes
`ifdef DMEM_SIZE_32_KB
`undef DMEM_SIZE_32_KB
`endif
`ifdef DMEM_SIZE_24_KB
`undef DMEM_SIZE_24_KB
`endif
`ifdef DMEM_SIZE_16_KB
`undef DMEM_SIZE_16_KB
`endif
`ifdef DMEM_SIZE_10_KB
`undef DMEM_SIZE_10_KB
`endif
`ifdef DMEM_SIZE_8_KB
`undef DMEM_SIZE_8_KB
`endif
`ifdef DMEM_SIZE_5_KB
`undef DMEM_SIZE_5_KB
`endif
`ifdef DMEM_SIZE_4_KB
`undef DMEM_SIZE_4_KB
`endif
`ifdef DMEM_SIZE_2p5_KB
`undef DMEM_SIZE_2p5_KB
`endif
`ifdef DMEM_SIZE_2_KB
`undef DMEM_SIZE_2_KB
`endif
`ifdef DMEM_SIZE_1_KB
`undef DMEM_SIZE_1_KB
`endif
`ifdef DMEM_SIZE_512_B
`undef DMEM_SIZE_512_B
`endif
`ifdef DMEM_SIZE_256_B
`undef DMEM_SIZE_256_B
`endif
`ifdef DMEM_SIZE_128_B
`undef DMEM_SIZE_128_B
`endif

// Include/Exclude Hardware Multiplier
`ifdef MULTIPLIER
`undef MULTIPLIER
`endif

// Include Debug interface
`ifdef DBG_EN
`undef DBG_EN
`endif


//----------------------------------------------------------------------------
// ADVANCED SYSTEM CONFIGURATION (FOR EXPERIENCED USERS)
//----------------------------------------------------------------------------

// Peripheral Memory Space:
`ifdef PER_SIZE_32_KB
`undef PER_SIZE_32_KB
`endif
`ifdef PER_SIZE_16_KB
`undef PER_SIZE_16_KB
`endif
`ifdef PER_SIZE_8_KB
`undef PER_SIZE_8_KB
`endif
`ifdef PER_SIZE_4_KB
`undef PER_SIZE_4_KB
`endif
`ifdef PER_SIZE_2_KB
`undef PER_SIZE_2_KB
`endif
`ifdef PER_SIZE_1_KB
`undef PER_SIZE_1_KB
`endif
`ifdef PER_SIZE_512_B
`undef PER_SIZE_512_B
`endif

// Let the CPU break after a PUC occurrence by default
`ifdef DBG_RST_BRK_EN
`undef DBG_RST_BRK_EN
`endif

// Custom user version number
`ifdef USER_VERSION
`undef USER_VERSION
`endif

// Include/Exclude Watchdog timer
`ifdef WATCHDOG
`undef WATCHDOG
`endif

// Include/Exclude Non-Maskable-Interrupt support
`ifdef NMI
`undef NMI
`endif

//----------------------------------------------------------------------------
// EXPERT SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Number of hardware breakpoint units
`ifdef DBG_HWBRK_0
`undef DBG_HWBRK_0
`endif
`ifdef DBG_HWBRK_1
`undef DBG_HWBRK_1
`endif
`ifdef DBG_HWBRK_2
`undef DBG_HWBRK_2
`endif
`ifdef DBG_HWBRK_3
`undef DBG_HWBRK_3
`endif

// Enable/Disable the hardware breakpoint RANGE mode
`ifdef DBG_HWBRK_RANGE
`undef DBG_HWBRK_RANGE
`endif

// Input synchronizers
`ifdef SYNC_CPU_EN
`undef SYNC_CPU_EN
`endif
`ifdef SYNC_DBG_EN
`undef SYNC_DBG_EN
`endif
`ifdef SYNC_DBG_UART_RXD
`undef SYNC_DBG_UART_RXD
`endif
`ifdef SYNC_NMI
`undef SYNC_NMI
`endif

// ASIC version
`ifdef ASIC
`undef ASIC
`endif


//----------------------------------------------------------------------------
// ASIC SYSTEM CONFIGURATION ( !!!! EXPERTS ONLY !!!! )
//----------------------------------------------------------------------------

// Fine grained clock gating
`ifdef CLOCK_GATING
`undef CLOCK_GATING
`endif

// LFXT clock domain
`ifdef LFXT_DOMAIN
`undef LFXT_DOMAIN
`endif

// MCLK: Clock Mux
`ifdef MCLK_MUX
`undef MCLK_MUX
`endif

// SMCLK: Clock Mux
`ifdef SMCLK_MUX
`undef SMCLK_MUX
`endif

// WATCHDOG: Clock Mux
`ifdef WATCHDOG_MUX
`undef WATCHDOG_MUX
`endif

// MCLK: Clock divider
`ifdef MCLK_DIVIDER
`undef MCLK_DIVIDER
`endif

// SMCLK: Clock divider (/1/2/4/8)
`ifdef SMCLK_DIVIDER
`undef SMCLK_DIVIDER
`endif

// ACLK: Clock divider (/1/2/4/8)
`ifdef ACLK_DIVIDER
`undef ACLK_DIVIDER
`endif

// LOW POWER MODE: CPUOFF
`ifdef CPUOFF_EN
`undef CPUOFF_EN
`endif

// LOW POWER MODE: OSCOFF
`ifdef OSCOFF_EN
`undef OSCOFF_EN
`endif

// LOW POWER MODE: SCG0
`ifdef SCG0_EN
`undef SCG0_EN
`endif

// LOW POWER MODE: SCG1
`ifdef SCG1_EN
`undef SCG1_EN
`endif


//==========================================================================//
//==========================================================================//
//==========================================================================//
//==========================================================================//
//=====        SYSTEM CONSTANTS --- !!!!!!!! DO NOT EDIT !!!!!!!!      =====//
//==========================================================================//
//==========================================================================//
//==========================================================================//
//==========================================================================//

// Program Memory Size
`ifdef PMEM_AWIDTH
`undef PMEM_AWIDTH
`endif
`ifdef PMEM_SIZE
`undef PMEM_SIZE
`endif

// Data Memory Size
`ifdef DMEM_AWIDTH
`undef DMEM_AWIDTH
`endif
`ifdef DMEM_SIZE
`undef DMEM_SIZE
`endif

// Peripheral Memory Size
`ifdef PER_AWIDTH
`undef PER_AWIDTH
`endif
`ifdef PER_SIZE
`undef PER_SIZE
`endif

// Data Memory Base Adresses
`ifdef DMEM_BASE
`undef DMEM_BASE
`endif

// Program & Data Memory most significant address bit (for 16 bit words)
`ifdef PMEM_MSB
`undef PMEM_MSB
`endif
`ifdef DMEM_MSB
`undef DMEM_MSB
`endif
`ifdef PER_MSB
`undef PER_MSB
`endif

// Instructions type
`ifdef INST_SO
`undef INST_SO
`endif
`ifdef INST_JMP
`undef INST_JMP
`endif
`ifdef INST_TO
`undef INST_TO
`endif

// Single-operand arithmetic
`ifdef RRC
`undef RRC
`endif
`ifdef SWPB
`undef SWPB
`endif
`ifdef RRA
`undef RRA
`endif
`ifdef SXT
`undef SXT
`endif
`ifdef PUSH
`undef PUSH
`endif
`ifdef CALL
`undef CALL
`endif
`ifdef RETI
`undef RETI
`endif
`ifdef IRQ
`undef IRQ
`endif

// Conditional jump
`ifdef JNE
`undef JNE
`endif
`ifdef JEQ
`undef JEQ
`endif
`ifdef JNC
`undef JNC
`endif
`ifdef JC
`undef JC
`endif
`ifdef JN
`undef JN
`endif
`ifdef JGE
`undef JGE
`endif
`ifdef JL
`undef JL
`endif
`ifdef JMP
`undef JMP
`endif

// Two-operand arithmetic
`ifdef MOV
`undef MOV
`endif
`ifdef ADD
`undef ADD
`endif
`ifdef ADDC
`undef ADDC
`endif
`ifdef SUBC
`undef SUBC
`endif
`ifdef SUB
`undef SUB
`endif
`ifdef CMP
`undef CMP
`endif
`ifdef DADD
`undef DADD
`endif
`ifdef BIT
`undef BIT
`endif
`ifdef BIC
`undef BIC
`endif
`ifdef BIS
`undef BIS
`endif
`ifdef XOR
`undef XOR
`endif
`ifdef AND
`undef AND
`endif

// Addressing modes
`ifdef DIR
`undef DIR
`endif
`ifdef IDX
`undef IDX
`endif
`ifdef INDIR
`undef INDIR
`endif
`ifdef INDIR_I
`undef INDIR_I
`endif
`ifdef SYMB
`undef SYMB
`endif
`ifdef IMM
`undef IMM
`endif
`ifdef ABS
`undef ABS
`endif
`ifdef CONST
`undef CONST
`endif

// Instruction state machine
`ifdef I_IRQ_FETCH
`undef I_IRQ_FETCH
`endif
`ifdef I_IRQ_DONE
`undef I_IRQ_DONE
`endif
`ifdef I_DEC
`undef I_DEC
`endif
`ifdef I_EXT1
`undef I_EXT1
`endif
`ifdef I_EXT2
`undef I_EXT2
`endif
`ifdef I_IDLE
`undef I_IDLE
`endif

// Execution state machine
`ifdef E_IRQ_0
`undef E_IRQ_0
`endif
`ifdef E_IRQ_1
`undef E_IRQ_1
`endif
`ifdef E_IRQ_2
`undef E_IRQ_2
`endif
`ifdef E_IRQ_3
`undef E_IRQ_3
`endif
`ifdef E_IRQ_4
`undef E_IRQ_4
`endif
`ifdef E_SRC_AD
`undef E_SRC_AD
`endif
`ifdef E_SRC_RD
`undef E_SRC_RD
`endif
`ifdef E_SRC_WR
`undef E_SRC_WR
`endif
`ifdef E_DST_AD
`undef E_DST_AD
`endif
`ifdef E_DST_RD
`undef E_DST_RD
`endif
`ifdef E_DST_WR
`undef E_DST_WR
`endif
`ifdef E_EXEC
`undef E_EXEC
`endif
`ifdef E_JUMP
`undef E_JUMP
`endif
`ifdef E_IDLE
`undef E_IDLE
`endif

// ALU control signals
`ifdef ALU_SRC_INV
`undef ALU_SRC_INV
`endif
`ifdef ALU_INC
`undef ALU_INC
`endif
`ifdef ALU_INC_C
`undef ALU_INC_C
`endif
`ifdef ALU_ADD
`undef ALU_ADD
`endif
`ifdef ALU_AND
`undef ALU_AND
`endif
`ifdef ALU_OR
`undef ALU_OR
`endif
`ifdef ALU_XOR
`undef ALU_XOR
`endif
`ifdef ALU_DADD
`undef ALU_DADD
`endif
`ifdef ALU_STAT_7
`undef ALU_STAT_7
`endif
`ifdef ALU_STAT_F
`undef ALU_STAT_F
`endif
`ifdef ALU_SHIFT
`undef ALU_SHIFT
`endif
`ifdef EXEC_NO_WR
`undef EXEC_NO_WR
`endif

// Debug interface
`ifdef DBG_UART_WR
`undef DBG_UART_WR
`endif
`ifdef DBG_UART_BW
`undef DBG_UART_BW
`endif
`ifdef DBG_UART_ADDR
`undef DBG_UART_ADDR
`endif

// Debug interface CPU_CTL register
`ifdef HALT
`undef HALT
`endif
`ifdef RUN
`undef RUN
`endif
`ifdef ISTEP
`undef ISTEP
`endif
`ifdef SW_BRK_EN
`undef SW_BRK_EN
`endif
`ifdef FRZ_BRK_EN
`undef FRZ_BRK_EN
`endif
`ifdef RST_BRK_EN
`undef RST_BRK_EN
`endif
`ifdef CPU_RST
`undef CPU_RST
`endif

// Debug interface CPU_STAT register
`ifdef HALT_RUN
`undef HALT_RUN
`endif
`ifdef PUC_PND
`undef PUC_PND
`endif
`ifdef SWBRK_PND
`undef SWBRK_PND
`endif
`ifdef HWBRK0_PND
`undef HWBRK0_PND
`endif
`ifdef HWBRK1_PND
`undef HWBRK1_PND
`endif

// Debug interface BRKx_CTL register
`ifdef BRK_MODE_RD
`undef BRK_MODE_RD
`endif
`ifdef BRK_MODE_WR
`undef BRK_MODE_WR
`endif
`ifdef BRK_MODE
`undef BRK_MODE
`endif
`ifdef BRK_EN
`undef BRK_EN
`endif
`ifdef BRK_I_EN
`undef BRK_I_EN
`endif
`ifdef BRK_RANGE
`undef BRK_RANGE
`endif

// Basic clock module: BCSCTL1 Control Register
`ifdef DIVAx
`undef DIVAx
`endif

// Basic clock module: BCSCTL2 Control Register
`ifdef SELMx
`undef SELMx
`endif
`ifdef DIVMx
`undef DIVMx
`endif
`ifdef SELS
`undef SELS
`endif
`ifdef DIVSx
`undef DIVSx
`endif

// MCLK Clock gate
`ifdef MCLK_CGATE
`undef MCLK_CGATE
`endif

// SMCLK Clock gate
`ifdef SMCLK_CGATE
`undef SMCLK_CGATE
`endif

//
// DEBUG INTERFACE EXTRA CONFIGURATION
//======================================

// Debug interface: CPU version
`ifdef CPU_VERSION
`undef CPU_VERSION
`endif

// Debug interface: Software breakpoint opcode
`ifdef DBG_SWBRK_OP
`undef DBG_SWBRK_OP
`endif

// Debug UART interface auto data synchronization
`ifdef DBG_UART_AUTO_SYNC
`undef DBG_UART_AUTO_SYNC
`endif

// Debug UART interface data rate
`ifdef DBG_UART_BAUD
`undef DBG_UART_BAUD
`endif
`ifdef DBG_DCO_FREQ
`undef DBG_DCO_FREQ
`endif
`ifdef DBG_UART_CNT
`undef DBG_UART_CNT
`endif

// Debug interface selection
`ifdef DBG_UART
`undef DBG_UART
`endif
`ifdef DBG_JTAG
`undef DBG_JTAG
`endif

// Enable/Disable the hardware breakpoint RANGE mode
`ifdef HWBRK_RANGE
`undef HWBRK_RANGE
`endif

// Counter width for the debug interface UART
`ifdef DBG_UART_XFER_CNT_W
`undef DBG_UART_XFER_CNT_W
`endif

//
// MULTIPLIER CONFIGURATION
//======================================

`ifdef MPY_16x16
`undef MPY_16x16
`endif
