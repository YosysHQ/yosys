/*
 *  NERV -- Naive Educational RISC-V Processor
 *
 *  Copyright (C) 2020  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

`define NERV_CSR

`ifdef NERV_CSR
	/**********************
	 *  CSR DECLARATIONS  *
	 **********************/

	// Note: The Memory-Mapped Machine Timers (mtime and timecmp) are not
	// part of the processor core itself. It's up to the SoC to provide
	// this part of the RISC-V M-Mode Spec.

	// FIXME: Additional instructions: ECALL, EBREAK, MRET, WFI

`define NERV_MACHINE_CSRS /* Machine Information CSRs */				\
	/* all of these CSRs are mandatory but can legally be all 0 */			\
	`NERV_CSR_VAL_MRO(mvendorid,         12'h F11, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRO(marchid,           12'h F12, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRO(mimpid,            12'h F13, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRO(mhartid,           12'h F14, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRO(mconfigptr,        12'h F15, 32'h 0000_0000)

`define NERV_TRAP_SETUP_CSRS /* Machine Trap Setup CSRs */				\
	`NERV_CSR_REG_MRW(mstatus,           12'h 300, 32'h 0000_0000)			\
											\
	/* misa can legally return all zeros */						\
	`NERV_CSR_REG_MRW(misa,              12'h 301, 32'h 0000_0000)			\
											\
	/* medeleg and mideleg should only exist if S mode is available */		\
/*	`NERV_CSR_REG_MRW(medeleg,           12'h 302, 32'h 0000_0000) */  		\
/*	`NERV_CSR_REG_MRW(mideleg,           12'h 303, 32'h 0000_0000) */  		\
											\
	`NERV_CSR_REG_MRW(mie,               12'h 304, 32'h 0000_0000)			\
											\
	/* mtvec can be implemented as read-only */					\
	`NERV_CSR_REG_MRW(mtvec,             12'h 305, 32'h 0000_0000)			\
											\
	/* mcounteren should only exist if U mode is available */			\
/*	`NERV_CSR_REG_MRW(mcounteren,        12'h 306, 32'h 0000_0000) */		\
											\
	`NERV_CSR_REG_MRW(mstatush,          12'h 310, 32'h 0000_0000)

`define NERV_TRAP_HANDLING_CSRS /* Machine Trap Handling CSRs */			\
	`NERV_CSR_REG_MRW(mscratch,          12'h 340, 32'h 0000_0000)	 		\
	`NERV_CSR_REG_MRW(mepc,              12'h 341, 32'h 0000_0000)			\
	`NERV_CSR_REG_MRW(mcause,            12'h 342, 32'h 0000_0000)			\
	`NERV_CSR_REG_MRW(mtval,             12'h 343, 32'h 0000_0000)			\
	`NERV_CSR_REG_MRW(mip,               12'h 344, 32'h 0000_0000)			\
											\
	/* mtinst and mtval2 added by hypervisor extension */				\
/*	`NERV_CSR_REG_MRW(mtinst,            12'h 34A, 32'h 0000_0000) */		\
/*	`NERV_CSR_REG_MRW(mtval2,            12'h 34B, 32'h 0000_0000) */

`define NERV_MACHINE_CONFIG_CSRS /* machine configuration CSRs */			\
	/* menvcfg should only exist if U mode is available */				\
/*	`NERV_CSR_REG_MRW(menvcfg,           12'h 30A, 32'h 0000_0000) */		\
/*	`NERV_CSR_REG_MRW(menvcfgh,          12'h 31A, 32'h 0000_0000) */		\
											\
	/* mseccfg not yet fully defined, and is not currently required */		\
/*	`NERV_CSR_REG_MRW(mseccfg,           12'h 747, 32'h 0000_0000) */		\
/*	`NERV_CSR_REG_MRW(mseccfgh,          12'h 757, 32'h 0000_0000) */

`ifdef NERV_PMP
/* PMP is optional and can be implemented with 0, 16, or 64 address CSRS */
`define NERV_PMP_CFG_CSRS /* Machine Memory Protection Config CSRs */			\
	/* PMP configuration is 8-bits long, */						\
	/* so each cfg controls four PMPs in RV32 */					\
	`NERV_CSR_VAL_MRW(pmpcfg0,           12'h 3A0, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg1,           12'h 3A1, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg2,           12'h 3A2, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg3,           12'h 3A3, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg4,           12'h 3A4, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg5,           12'h 3A5, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg6,           12'h 3A6, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg7,           12'h 3A7, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg8,           12'h 3A8, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg9,           12'h 3A9, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg10,          12'h 3AA, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg11,          12'h 3AB, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg12,          12'h 3AC, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg13,          12'h 3AD, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg14,          12'h 3AE, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpcfg15,          12'h 3AF, 32'h 0000_0000)

`define NERV_PMP_ADDR_CSRS /* Machine Memory Protection Addr CSRs */			\
	`NERV_CSR_VAL_MRW(pmpaddr0,          12'h 3B0, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr1,          12'h 3B1, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr2,          12'h 3B2, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr3,          12'h 3B3, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr4,          12'h 3B4, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr5,          12'h 3B5, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr6,          12'h 3B6, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr7,          12'h 3B7, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr8,          12'h 3B8, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr9,          12'h 3B9, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr10,         12'h 3BA, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr11,         12'h 3BB, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr12,         12'h 3BC, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr13,         12'h 3BD, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr14,         12'h 3BE, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr15,         12'h 3BF, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr16,         12'h 3C0, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr17,         12'h 3C1, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr18,         12'h 3C2, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr19,         12'h 3C3, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr20,         12'h 3C4, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr21,         12'h 3C5, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr22,         12'h 3C6, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr23,         12'h 3C7, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr24,         12'h 3C8, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr25,         12'h 3C9, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr26,         12'h 3CA, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr27,         12'h 3CB, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr28,         12'h 3CC, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr29,         12'h 3CD, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr30,         12'h 3CE, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr31,         12'h 3CF, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr32,         12'h 3D0, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr33,         12'h 3D1, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr34,         12'h 3D2, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr35,         12'h 3D3, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr36,         12'h 3D4, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr37,         12'h 3D5, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr38,         12'h 3D6, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr39,         12'h 3D7, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr40,         12'h 3D8, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr41,         12'h 3D9, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr42,         12'h 3DA, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr43,         12'h 3DB, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr44,         12'h 3DC, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr45,         12'h 3DD, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr46,         12'h 3DE, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr47,         12'h 3DF, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr48,         12'h 3E0, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr49,         12'h 3E1, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr50,         12'h 3E2, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr51,         12'h 3E3, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr52,         12'h 3E4, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr53,         12'h 3E5, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr54,         12'h 3E6, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr55,         12'h 3E7, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr56,         12'h 3E8, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr57,         12'h 3E9, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr58,         12'h 3EA, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr59,         12'h 3EB, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr60,         12'h 3EC, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr61,         12'h 3ED, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr62,         12'h 3EE, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRW(pmpaddr63,         12'h 3EF, 32'h 0000_0000)

`else
`define NERV_PMP_CFG_CSRS
`define NERV_PMP_ADDR_CSRS
`endif

`define NERV_COUNTER_CSRS /* Machine Counter/Timers CSRs */				\
	`NERV_CSR_ARR_DEF(hpm_counter, 32)						\
	`NERV_CSR_ARR_MRW(hpm_counter, 0, mcycle,            12'h B00)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 2, minstret,          12'h B02)			\
											\
	/* mhpmcounter3..31 provide hardware performance monitoring */ 			\
	/* the counted event is defined by the corresponding hpm_event CSR */		\
	`NERV_CSR_ARR_MRW(hpm_counter, 3,  mhpmcounter3,     12'h B03)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 4,  mhpmcounter4,     12'h B04)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 5,  mhpmcounter5,     12'h B05)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 6,  mhpmcounter6,     12'h B06)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 7,  mhpmcounter7,     12'h B07)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 8,  mhpmcounter8,     12'h B08)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 9,  mhpmcounter9,     12'h B09)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 10, mhpmcounter10,    12'h B0A)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 11, mhpmcounter11,    12'h B0B)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 12, mhpmcounter12,    12'h B0C)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 13, mhpmcounter13,    12'h B0D)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 14, mhpmcounter14,    12'h B0E)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 15, mhpmcounter15,    12'h B0F)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 16, mhpmcounter16,    12'h B10)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 17, mhpmcounter17,    12'h B11)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 18, mhpmcounter18,    12'h B12)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 19, mhpmcounter19,    12'h B13)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 20, mhpmcounter20,    12'h B14)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 21, mhpmcounter21,    12'h B15)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 22, mhpmcounter22,    12'h B16)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 23, mhpmcounter23,    12'h B17)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 24, mhpmcounter24,    12'h B18)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 25, mhpmcounter25,    12'h B19)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 26, mhpmcounter26,    12'h B1A)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 27, mhpmcounter27,    12'h B1B)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 28, mhpmcounter28,    12'h B1C)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 29, mhpmcounter29,    12'h B1D)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 30, mhpmcounter30,    12'h B1E)			\
	`NERV_CSR_ARR_MRW(hpm_counter, 31, mhpmcounter31,    12'h B1F)			\
											\
	`NERV_CSR_ARR_DEF(hpm_counterh, 32)						\
	`NERV_CSR_ARR_MRW(hpm_counterh, 0, mcycleh,          12'h B80)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 2, minstreth,        12'h B82)			\
											\
	`NERV_CSR_ARR_MRW(hpm_counterh, 3,  mhpmcounter3h,   12'h B83)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 4,  mhpmcounter4h,   12'h B84)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 5,  mhpmcounter5h,   12'h B85)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 6,  mhpmcounter6h,   12'h B86)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 7,  mhpmcounter7h,   12'h B87)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 8,  mhpmcounter8h,   12'h B88)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 9,  mhpmcounter9h,   12'h B89)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 10, mhpmcounter10h,  12'h B8A)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 11, mhpmcounter11h,  12'h B8B)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 12, mhpmcounter12h,  12'h B8C)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 13, mhpmcounter13h,  12'h B8D)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 14, mhpmcounter14h,  12'h B8E)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 15, mhpmcounter15h,  12'h B8F)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 16, mhpmcounter16h,  12'h B90)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 17, mhpmcounter17h,  12'h B91)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 18, mhpmcounter18h,  12'h B92)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 19, mhpmcounter19h,  12'h B93)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 20, mhpmcounter20h,  12'h B94)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 21, mhpmcounter21h,  12'h B95)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 22, mhpmcounter22h,  12'h B96)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 23, mhpmcounter23h,  12'h B97)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 24, mhpmcounter24h,  12'h B98)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 25, mhpmcounter25h,  12'h B99)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 26, mhpmcounter26h,  12'h B9A)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 27, mhpmcounter27h,  12'h B9B)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 28, mhpmcounter28h,  12'h B9C)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 29, mhpmcounter29h,  12'h B9D)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 30, mhpmcounter30h,  12'h B9E)			\
	`NERV_CSR_ARR_MRW(hpm_counterh, 31, mhpmcounter31h,  12'h B9F)		

`define NERV_COUNTER_SETUP_CSRS /* Machine Counter Setup CSRs */			\
	/* mcountinhibit is optional */							\
/*	`NERV_CSR_REG_MRW(mcountinhibit,     12'h 320, 32'h 0000_0000) */		\
											\
	/* mhpmevent3..31 select which hardware event the corresponding */		\
	/* mhpmcounter should be triggered by and thus count */				\
	`NERV_CSR_ARR_DEF(hpm_event, 32)						\
	`NERV_CSR_ARR_MRW(hpm_event, 3,  mhpmevent3,         12'h 323)			\
	`NERV_CSR_ARR_MRW(hpm_event, 4,  mhpmevent4,         12'h 324)			\
	`NERV_CSR_ARR_MRW(hpm_event, 5,  mhpmevent5,         12'h 325)			\
	`NERV_CSR_ARR_MRW(hpm_event, 6,  mhpmevent6,         12'h 326)			\
	`NERV_CSR_ARR_MRW(hpm_event, 7,  mhpmevent7,         12'h 327)			\
	`NERV_CSR_ARR_MRW(hpm_event, 8,  mhpmevent8,         12'h 328)			\
	`NERV_CSR_ARR_MRW(hpm_event, 9,  mhpmevent9,         12'h 329)			\
	`NERV_CSR_ARR_MRW(hpm_event, 10, mhpmevent10,        12'h 32A)			\
	`NERV_CSR_ARR_MRW(hpm_event, 11, mhpmevent11,        12'h 32B)			\
	`NERV_CSR_ARR_MRW(hpm_event, 12, mhpmevent12,        12'h 32C)			\
	`NERV_CSR_ARR_MRW(hpm_event, 13, mhpmevent13,        12'h 32D)			\
	`NERV_CSR_ARR_MRW(hpm_event, 14, mhpmevent14,        12'h 32E)			\
	`NERV_CSR_ARR_MRW(hpm_event, 15, mhpmevent15,        12'h 32F)			\
	`NERV_CSR_ARR_MRW(hpm_event, 16, mhpmevent16,        12'h 330)			\
	`NERV_CSR_ARR_MRW(hpm_event, 17, mhpmevent17,        12'h 331)			\
	`NERV_CSR_ARR_MRW(hpm_event, 18, mhpmevent18,        12'h 332)			\
	`NERV_CSR_ARR_MRW(hpm_event, 19, mhpmevent19,        12'h 333)			\
	`NERV_CSR_ARR_MRW(hpm_event, 20, mhpmevent20,        12'h 334)			\
	`NERV_CSR_ARR_MRW(hpm_event, 21, mhpmevent21,        12'h 335)			\
	`NERV_CSR_ARR_MRW(hpm_event, 22, mhpmevent22,        12'h 336)			\
	`NERV_CSR_ARR_MRW(hpm_event, 23, mhpmevent23,        12'h 337)			\
	`NERV_CSR_ARR_MRW(hpm_event, 24, mhpmevent24,        12'h 338)			\
	`NERV_CSR_ARR_MRW(hpm_event, 25, mhpmevent25,        12'h 339)			\
	`NERV_CSR_ARR_MRW(hpm_event, 26, mhpmevent26,        12'h 33A)			\
	`NERV_CSR_ARR_MRW(hpm_event, 27, mhpmevent27,        12'h 33B)			\
	`NERV_CSR_ARR_MRW(hpm_event, 28, mhpmevent28,        12'h 33C)			\
	`NERV_CSR_ARR_MRW(hpm_event, 29, mhpmevent29,        12'h 33D)			\
	`NERV_CSR_ARR_MRW(hpm_event, 30, mhpmevent30,        12'h 33E)			\
	`NERV_CSR_ARR_MRW(hpm_event, 31, mhpmevent31,        12'h 33F)
 
`define NERV_CUSTOM_CSRS /* Custom CSR for testing */					\
	`NERV_CSR_REG_MRW(custom,            12'h BC0, 32'h 0000_0000)			\
	`NERV_CSR_VAL_MRO(custom_ro,         12'h FC0, 32'h dead_beef)

`define NERV_CSRS			\
	`NERV_MACHINE_CSRS		\
	`NERV_TRAP_SETUP_CSRS		\
	`NERV_TRAP_HANDLING_CSRS	\
	`NERV_MACHINE_CONFIG_CSRS	\
	`NERV_PMP_CFG_CSRS		\
	`NERV_PMP_ADDR_CSRS		\
	`NERV_COUNTER_CSRS		\
	`NERV_COUNTER_SETUP_CSRS	\
	`NERV_CUSTOM_CSRS
`endif

module nerv #(
	parameter [31:0] RESET_ADDR = 32'h 0000_0000,
	parameter integer NUMREGS = 32
) (
	input clock,
	input reset,
	input stall,
	output trap,

`ifdef NERV_RVFI
	output reg        rvfi_valid,
	output reg [63:0] rvfi_order,
	output reg [31:0] rvfi_insn,
	output reg        rvfi_trap,
	output reg        rvfi_halt,
	output reg        rvfi_intr,
	output reg [ 1:0] rvfi_mode,
	output reg [ 1:0] rvfi_ixl,
	output reg [ 4:0] rvfi_rs1_addr,
	output reg [ 4:0] rvfi_rs2_addr,
	output reg [31:0] rvfi_rs1_rdata,
	output reg [31:0] rvfi_rs2_rdata,
	output reg [ 4:0] rvfi_rd_addr,
	output reg [31:0] rvfi_rd_wdata,
	output reg [31:0] rvfi_pc_rdata,
	output reg [31:0] rvfi_pc_wdata,

`ifdef NERV_CSR
`define NERV_CSR_REG_MRW(NAME, ADDR, VALUE)			\
	output reg [31:0] rvfi_csr_``NAME``_rmask,		\
	output reg [31:0] rvfi_csr_``NAME``_wmask,		\
	output reg [31:0] rvfi_csr_``NAME``_rdata,		\
	output reg [31:0] rvfi_csr_``NAME``_wdata,

`define NERV_CSR_VAL_MRW(NAME, ADDR, VALUE)			\
	`NERV_CSR_REG_MRW(NAME, ADDR, VALUE)

`define NERV_CSR_VAL_MRO(NAME, ADDR, VALUE)			\
	`NERV_CSR_REG_MRW(NAME, ADDR, VALUE)

`define NERV_CSR_ARR_DEF(ARRAY, DEPTH)

`define NERV_CSR_ARR_MRW(ARRAY, INDEX, NAME, ADDR)		\
	output reg [31:0] rvfi_csr_``NAME``_rmask,			\
	output reg [31:0] rvfi_csr_``NAME``_wmask,			\
	output reg [31:0] rvfi_csr_``NAME``_rdata,			\
	output reg [31:0] rvfi_csr_``NAME``_wdata,

`NERV_CSRS
`undef NERV_CSR_REG_MRW
`undef NERV_CSR_VAL_MRW
`undef NERV_CSR_VAL_MRO
`undef NERV_CSR_ARR_DEF
`undef NERV_CSR_ARR_MRW
`endif

	output reg [31:0] rvfi_mem_addr,
	output reg [ 3:0] rvfi_mem_rmask,
	output reg [ 3:0] rvfi_mem_wmask,
	output reg [31:0] rvfi_mem_rdata,
	output reg [31:0] rvfi_mem_wdata,

`ifdef NERV_FAULT
	output reg        rvfi_mem_fault,
	output reg [ 3:0] rvfi_mem_fault_rmask,
	output reg [ 3:0] rvfi_mem_fault_wmask,
`endif
`endif

	// we have 2 external memories
	// one is instruction memory
	output [31:0] imem_addr,
	input  [31:0] imem_data,

	// the other is data memory
	output        dmem_valid,
	output [31:0] dmem_addr,
	output [ 3:0] dmem_wstrb,
	output [31:0] dmem_wdata,
	input  [31:0] dmem_rdata,

`ifdef NERV_FAULT
	input         imem_fault,
	input         dmem_fault,
`endif
	// interrupt inputs
	input  [31:0] irq
);

`ifndef NERV_FAULT
	wire imem_fault = 0;
	wire dmem_fault = 0;
`endif

	reg mem_wr_enable;
	reg [31:0] mem_wr_addr;
	reg [31:0] mem_wr_data;
	reg [3:0] mem_wr_strb;

	reg mem_rd_enable;
	reg [31:0] mem_rd_addr;
	reg [4:0] mem_rd_reg;
	reg [4:0] mem_rd_func;

	reg mem_rd_enable_q;
	reg [4:0] mem_rd_reg_q;
	reg [4:0] mem_rd_func_q;

	reg mem_wr_enable_q;

	// delayed copies of mem_rd (and mem_wr for NERV_FAULTS)
	always @(posedge clock) begin
		if (!stall) begin
			mem_rd_enable_q <= mem_rd_enable;
			mem_rd_reg_q <= mem_rd_reg;
			mem_rd_func_q <= mem_rd_func;
			mem_wr_enable_q <= mem_wr_enable;
		end
		if (reset) begin
			mem_rd_enable_q <= 0;
		end
	end

	// memory signals
	assign dmem_valid = mem_wr_enable || mem_rd_enable;
	assign dmem_addr  = mem_wr_enable ? mem_wr_addr : mem_rd_enable ? mem_rd_addr : 32'h x;
	assign dmem_wstrb = mem_wr_enable ? mem_wr_strb : mem_rd_enable ? 4'h 0 : 4'h x;
	assign dmem_wdata = mem_wr_enable ? mem_wr_data : 32'h x;

	// registers, instruction reg, program counter, next pc
	reg [31:0] regfile [0:NUMREGS-1];
	wire [31:0] insn;
	reg [31:0] npc;
	reg [31:0] pc;

	reg [31:0] imem_addr_q;

	always @(posedge clock) begin
		imem_addr_q <= imem_addr;
	end

	// instruction memory pointer
	assign imem_addr = npc;
	assign insn = imem_data;

	// components of the instruction
	wire [6:0] insn_funct7;
	wire [4:0] insn_rs2;
	wire [4:0] insn_rs1;
	wire [2:0] insn_funct3;
	wire [4:0] insn_rd;
	wire [6:0] insn_opcode;

	// rs1 and rs2 are source for the instruction
	wire [31:0] rs1_value = !insn_rs1 ? 0 : regfile[insn_rs1];
	wire [31:0] rs2_value = !insn_rs2 ? 0 : regfile[insn_rs2];

	// split R-type instruction - see section 2.2 of RiscV spec
	assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn;

	// setup for I, S, B & J type instructions
	// I - short immediates and loads
	wire [11:0] imm_i;
	assign imm_i = insn[31:20];

	// S - stores
	wire [11:0] imm_s;
	assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

	// B - conditionals
	wire [12:0] imm_b;
	assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

	// J - unconditional jumps
	wire [20:0] imm_j;
	assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn[31:12], 1'b0};

	wire [31:0] imm_i_sext = $signed(imm_i);
	wire [31:0] imm_s_sext = $signed(imm_s);
	wire [31:0] imm_b_sext = $signed(imm_b);
	wire [31:0] imm_j_sext = $signed(imm_j);

	// opcodes - see section 19 of RiscV spec
	localparam OPCODE_LOAD       = 7'b 00_000_11;
	localparam OPCODE_STORE      = 7'b 01_000_11;
	localparam OPCODE_MADD       = 7'b 10_000_11;
	localparam OPCODE_BRANCH     = 7'b 11_000_11;

	localparam OPCODE_LOAD_FP    = 7'b 00_001_11;
	localparam OPCODE_STORE_FP   = 7'b 01_001_11;
	localparam OPCODE_MSUB       = 7'b 10_001_11;
	localparam OPCODE_JALR       = 7'b 11_001_11;

	localparam OPCODE_CUSTOM_0   = 7'b 00_010_11;
	localparam OPCODE_CUSTOM_1   = 7'b 01_010_11;
	localparam OPCODE_NMSUB      = 7'b 10_010_11;
	localparam OPCODE_RESERVED_0 = 7'b 11_010_11;

	localparam OPCODE_MISC_MEM   = 7'b 00_011_11;
	localparam OPCODE_AMO        = 7'b 01_011_11;
	localparam OPCODE_NMADD      = 7'b 10_011_11;
	localparam OPCODE_JAL        = 7'b 11_011_11;

	localparam OPCODE_OP_IMM     = 7'b 00_100_11;
	localparam OPCODE_OP         = 7'b 01_100_11;
	localparam OPCODE_OP_FP      = 7'b 10_100_11;
	localparam OPCODE_SYSTEM     = 7'b 11_100_11;

	localparam OPCODE_AUIPC      = 7'b 00_101_11;
	localparam OPCODE_LUI        = 7'b 01_101_11;
	localparam OPCODE_RESERVED_1 = 7'b 10_101_11;
	localparam OPCODE_RESERVED_2 = 7'b 11_101_11;

	localparam OPCODE_OP_IMM_32  = 7'b 00_110_11;
	localparam OPCODE_OP_32      = 7'b 01_110_11;
	localparam OPCODE_CUSTOM_2   = 7'b 10_110_11;
	localparam OPCODE_CUSTOM_3   = 7'b 11_110_11;

	localparam MCAUSE_MACHINE_SOFTWARE_INTERRUPT = 32'h80000003;
	localparam MCAUSE_MACHINE_TIMER_INTERRUPT    = 32'h80000007;
	localparam MCAUSE_MACHINE_EXTERNAL_INTERRUPT = 32'h8000000b;

	localparam MCAUSE_INSN_ADDRESS_MISALIGNED  = 32'h00000000;
	localparam MCAUSE_INSN_ACCESS_FAULT        = 32'h00000001;
	localparam MCAUSE_INVALID_INSTRUCTION      = 32'h00000002;
	localparam MCAUSE_BREAKPOINT               = 32'h00000003;
	localparam MCAUSE_LOAD_ADDRESS_MISALIGNED  = 32'h00000004;
	localparam MCAUSE_LOAD_ACCESS_FAULT        = 32'h00000005;
	localparam MCAUSE_STORE_ADDRESS_MISALIGNED = 32'h00000006;
	localparam MCAUSE_STORE_ACCESS_FAULT       = 32'h00000007;
	localparam MCAUSE_ECALL_M_MODE             = 32'h0000000b;

	localparam IRQ_MASK = 32'hFFFF0888;

	// next write, next destination (rd) value & register
	reg next_wr;
	reg [31:0] next_rd;
	reg [4:0] wr_rd;

	// illegal instruction registers
	reg illinsn;

	reg reset_q;
	wire running = !stall && !reset && !reset_q;

	// action to perform this cycle
	reg cycle_intr; // cycle to start fetching new PC for interrupts
	reg cycle_insn; // first non-trapping cycle of an instruction
	reg cycle_trap; // trap in the first cycle of an instruction
	reg cycle_late_wr; // 2nd cycle for mem_rd_enable instructions

`ifdef NERV_FAULT
	reg cycle_dmem_fault;
`endif

	assign trap = cycle_trap;

`ifdef NERV_CSR
	/*********************
	 *  CSR DEFINITIONS  *
	 *********************/

	reg        csr_ack;
	reg [31:0] csr_rdval;
	reg [31:0] csr_next;

	wire imem_valid = !mem_rd_enable_q && !mem_wr_enable_q && !imem_fault;
	wire [ 1:0] csr_mode = (running && imem_valid && !irq_num && insn_opcode == OPCODE_SYSTEM) ? insn_funct3[1:0] : 2'b 00; // 00=None, 01=RW, 10=RS, 11=RC
	wire [11:0] csr_addr = imm_i;
	wire [31:0] csr_rsval = insn_funct3[2] ? insn_rs1 : rs1_value;
	wire csr_ro = csr_mode && (csr_mode != 2'b01 && !insn_rs1);

	integer hpm_idx, hpm_increment, hpm_event;

`define NERV_CSR_REG_MRW(NAME, ADDR, VALUE)				\
	wire csr_``NAME``_sel = csr_mode && csr_addr == ADDR;		\
	reg [31:0] csr_``NAME``_value;					\
	reg [31:0] csr_``NAME``_wdata;					\
	reg [31:0] csr_``NAME``_next;					\
	always @(posedge clock) begin					\
		csr_``NAME``_value <= csr_``NAME``_next;		\
		if (reset || reset_q)					\
			csr_``NAME``_value <= VALUE;			\
	end

`define NERV_CSR_VAL_MRW(NAME, ADDR, VALUE)				\
	wire csr_``NAME``_sel = csr_mode && csr_addr == ADDR;		\
	wire [31:0] csr_``NAME``_wdata = csr_``NAME``_sel ? csr_next : csr_``NAME``_value; \
	localparam [31:0] csr_``NAME``_value = VALUE;

`define NERV_CSR_VAL_MRO(NAME, ADDR, VALUE)				\
	wire csr_``NAME``_sel = csr_ro && csr_addr == ADDR;		\
	localparam [31:0] csr_``NAME``_value = VALUE;

`define NERV_CSR_ARR_DEF(ARRAY, DEPTH)					\
	integer ARRAY``_idx;						\
	wire [DEPTH-1:0] csr_``ARRAY``_sel;			\
	reg [(DEPTH*32)-1:0] csr_``ARRAY``_value;			\
	reg [(DEPTH*32)-1:0] csr_``ARRAY``_wdata;			\
	reg [(DEPTH*32)-1:0] csr_``ARRAY``_next;			\
	always @(posedge clock) begin					\
		csr_``ARRAY``_value <= csr_``ARRAY``_next;		\
		if (reset || reset_q)					\
			csr_``ARRAY``_value <= 'b0;			\
	end

`define NERV_CSR_ARR_MRW(ARRAY, INDEX, NAME, ADDR)				\
	wire csr_``NAME``_sel = csr_mode && csr_addr == ADDR;			\
	wire [31:0] csr_``NAME``_value = csr_``ARRAY``_value[(INDEX)*32 +: 32];	\
	wire [31:0] csr_``NAME``_wdata = csr_``ARRAY``_wdata[(INDEX)*32 +: 32];	\
	wire [31:0] csr_``NAME``_next  = csr_``ARRAY``_next[(INDEX)*32 +: 32];  \
	assign csr_``ARRAY``_sel[INDEX] = csr_``NAME``_sel;

	// dummy out missing select lines
	assign csr_hpm_event_sel[2:0] = 0;
	assign csr_hpm_counter_sel[1] = 0;
	assign csr_hpm_counterh_sel[1] = 0;

`NERV_CSRS
`undef NERV_CSR_REG_MRW
`undef NERV_CSR_VAL_MRW
`undef NERV_CSR_VAL_MRO
`undef NERV_CSR_ARR_DEF
`undef NERV_CSR_ARR_MRW
`endif // NERV_CSR

	wire [31:0] irq_en;
	reg [4:0] irq_num;
	assign irq_en = irq & csr_mie_value;

	// resolve interrupt priority
	always @* begin
		if (irq_en[31]) irq_num = 5'd31;
		else if (irq_en[30]) irq_num = 5'd30;
		else if (irq_en[29]) irq_num = 5'd29;
		else if (irq_en[28]) irq_num = 5'd28;
		else if (irq_en[27]) irq_num = 5'd27;
		else if (irq_en[26]) irq_num = 5'd26;
		else if (irq_en[25]) irq_num = 5'd25;
		else if (irq_en[24]) irq_num = 5'd24;
		else if (irq_en[23]) irq_num = 5'd23;
		else if (irq_en[22]) irq_num = 5'd22;
		else if (irq_en[21]) irq_num = 5'd21;
		else if (irq_en[20]) irq_num = 5'd20;
		else if (irq_en[19]) irq_num = 5'd19;
		else if (irq_en[18]) irq_num = 5'd18;
		else if (irq_en[17]) irq_num = 5'd17;
		else if (irq_en[16]) irq_num = 5'd16;
		else if (irq_en[11]) irq_num = 5'd11;
		else if (irq_en[7]) irq_num = 5'd7;
		else if (irq_en[3]) irq_num = 5'd3;
		else irq_num = 5'd0;
	end

	always @* begin
		// advance pc
		npc = pc + 4;

		// defaults for read, write
		next_wr = 0;
		next_rd = 0;
		cycle_intr = 0;
		cycle_trap = 0;
		cycle_insn = 0;
		cycle_late_wr = 0;
`ifdef NERV_FAULT
		cycle_dmem_fault = 0;
`endif
		wr_rd = insn_rd;

		illinsn = 0;

		mem_wr_enable = 0;
		mem_wr_addr = 32'hx;
		mem_wr_data = 32'hx;
		mem_wr_strb = 4'hx;

		mem_rd_enable = 0;
		mem_rd_addr = 32'hx;
		mem_rd_reg = 5'hx;
		mem_rd_func = 5'hx;

`ifdef NERV_CSR
		csr_ack = 0;
		csr_rdval = 'hx;

		unique case (1'b1)
`define NERV_CSR_REG_MRW(NAME, ADDR, VALUE)		\
			csr_mode && csr_``NAME``_sel: begin		\
				csr_ack = 1;				\
				csr_rdval = csr_``NAME``_value;	\
			end

`define NERV_CSR_VAL_MRW(NAME, ADDR, VALUE)		\
			csr_mode && csr_``NAME``_sel: begin		\
				csr_ack = 1;				\
				csr_rdval = csr_``NAME``_value;	\
			end

`define NERV_CSR_VAL_MRO(NAME, ADDR, VALUE)		\
			csr_ro && csr_``NAME``_sel: begin		\
				csr_ack = 1;				\
				csr_rdval = csr_``NAME``_value;	\
			end
`define NERV_CSR_ARR_DEF(ARRAY, DEPTH)
`define NERV_CSR_ARR_MRW(ARRAY, INDEX, NAME, ADDR)		\
	`NERV_CSR_REG_MRW(NAME, ADDR, 32'h 0000_0000)

`NERV_CSRS
`undef NERV_CSR_REG_MRW
`undef NERV_CSR_VAL_MRW
`undef NERV_CSR_VAL_MRO
`undef NERV_CSR_ARR_DEF
`undef NERV_CSR_ARR_MRW

			default: /* nothing */;
		endcase

		csr_next = csr_rdval;
		case (csr_mode)
			2'b 01 /* RW */: csr_next = csr_rsval;
			2'b 10 /* RS */: csr_next = csr_next | csr_rsval;
			2'b 11 /* RC */: csr_next = csr_next & ~csr_rsval;
		endcase

`define NERV_CSR_REG_MRW(NAME, ADDR, VALUE) \
		csr_``NAME``_wdata = csr_``NAME``_sel ? csr_next : csr_``NAME``_value; \
		csr_``NAME``_next = csr_``NAME``_wdata;

`define NERV_CSR_VAL_MRW(NAME, ADDR, VALUE)
`define NERV_CSR_VAL_MRO(NAME, ADDR, VALUE)
`define NERV_CSR_ARR_DEF(ARRAY, DEPTH)								\
		for (ARRAY``_idx=0; ARRAY``_idx < DEPTH; ARRAY``_idx=ARRAY``_idx+1) begin 	\
			csr_``ARRAY``_wdata[(ARRAY``_idx)*32 +: 32] = 				\
				csr_``ARRAY``_sel[ARRAY``_idx] 					\
				? csr_next 							\
				: csr_``ARRAY``_value[(ARRAY``_idx)*32 +: 32];			\
		end										\
		csr_``ARRAY``_next = csr_``ARRAY``_wdata;

`define NERV_CSR_ARR_MRW(ARRAY, INDEX, NAME, ADDR)

`NERV_CSRS
`undef NERV_CSR_REG_MRW
`undef NERV_CSR_VAL_MRW
`undef NERV_CSR_VAL_MRO
`undef NERV_CSR_ARR_DEF
`undef NERV_CSR_ARR_MRW

		for (hpm_idx=0; hpm_idx < 32; hpm_idx=hpm_idx+1) begin
			case (hpm_idx)
				0 /* mcycle */ : hpm_event = 32'h 1;
				2 /* minstret */ : hpm_event = 32'h 2;
				default:
					hpm_event = csr_hpm_event_next[(hpm_idx)*32 +: 32];
			endcase
			case (hpm_event)
				32'h 1 /* cycle counter */: hpm_increment = 1;
				32'h 2 /* instruction counter */: hpm_increment = running ? 1 : 0;
				32'h 3 /* memory writes */: hpm_increment = mem_wr_enable_q ? 1 : 0;
				default: begin
					csr_hpm_event_next[(hpm_idx)*32 +: 32] = 0;
					hpm_increment = 0;
				end
			endcase
			{csr_hpm_counterh_next[(hpm_idx)*32 +: 32], csr_hpm_counter_next[(hpm_idx)*32 +: 32]} = 
				{csr_hpm_counterh_next[(hpm_idx)*32 +: 32], csr_hpm_counter_next[(hpm_idx)*32 +: 32]} + hpm_increment;
		end

	// mstatus & mstatush - Machine Status
	csr_mstatus_next[31] = 'b0; // SD is always 0 if FS, VS, and XS are not enabled
	csr_mstatus_next[30:23] = 'b0; // WPRI
	csr_mstatus_next[22] = 'b0; // TSR = 0 if no S
	csr_mstatus_next[21] = 'b0; // TW = 0 if no U or S
	csr_mstatus_next[20] = 'b0; // TVM = 0 if no S
	csr_mstatus_next[19] = 'b0; // MXR = 0 if no S
	csr_mstatus_next[18] = 'b0; // SUM = 0 if no S
	csr_mstatus_next[17] = 'b0; // MPRV = 0 if no U
	csr_mstatus_next[16:15] = 'b0; // XS = 0 if no user extensions
	csr_mstatus_next[14:13] = 'b0; // FS = 0 if no S and no floating point extension
	csr_mstatus_next[12:11] = 2'b11; // MPP = b11 if no U
	csr_mstatus_next[10:9] = 'b0; // VS = 0 if no vector extension
	csr_mstatus_next[8] = 'b0; // SPP = 0 if no S
	//csr_mstatus_next[7] = ; // MPIE controlled by trap handling
	csr_mstatus_next[6] = 'b0; // UBE = 0 if no U
	csr_mstatus_next[5] = 'b0; // SPIE = 0 if no S
	csr_mstatus_next[4] = 'b0; // WPRI
	//csr_mstatus_next[3] = ; // MIE controlled by code
	csr_mstatus_next[2] = 'b0; // WPRI
	csr_mstatus_next[1] = 'b0; // SIE = 0 if no S
	csr_mstatus_next[0] = 'b0; // WPRI

	csr_mstatush_next[31:6] = 'b0; // WPRI
	csr_mstatush_next[5] = 1'b0; // MBE = 1 if big endian, 0 if little endian
	csr_mstatush_next[4] = 'b0; // SBE = 0 if no S
	csr_mstatush_next[3:0] = 'b0; // WPRI

	// misa - Machine ISA
	// read-only 0 for unimplemented register
	csr_misa_next[31:20] = 'b0; // MXL = 1 for XLEN=32
	csr_misa_next[29:26] = 'b0; // 0
	csr_misa_next[25:0] = 'b0; // Extensions enabled

	// mie - Machine Interrupt-Enable
	// A bit in mie must be writable if the corresponding interrupt can ever become pending.
	// Bits of mie that are not writable must be read-only 0.
	//csr_mie_next[31:16] = 'b0; // bits 16 and above for custom/platform interrupts
	csr_mie_next[15:12] = 'b0; // 0
	//csr_mie_next[11] = 'b0; // MEIE - Machine-level External Interrupt Enable
	csr_mie_next[10] = 'b0; // 0
	csr_mie_next[9] = 'b0; // SEIE = 0 if no S
	csr_mie_next[8] = 'b0; // 0
	//csr_mie_next[7] = 'b0; // MTIE - Machine Timer Interrupt Enable
	csr_mie_next[6] = 'b0; // 0
	csr_mie_next[5] = 'b0; // STIE = 0 if no S
	csr_mie_next[4] = 'b0; // 0
	//csr_mie_next[3] = 'b0; // MSIE - Machine-level Software Interrupt Enable
	csr_mie_next[2] = 'b0; // 0
	csr_mie_next[1] = 'b0; // SSIE = 0 if no S
	csr_mie_next[0] = 'b0; // 0

	// mip - Machine Interrupt-Pending
	//csr_mip_next[31:16] = 'b0; // bits 16 and above for custom/platform interrupts
	//csr_mip_next[15:12] = 'b0; // 0
	//csr_mip_next[11] = 'b0; // MEIE - Machine-level External Interrupt Pending
	//csr_mip_next[10] = 'b0; // 0
	//csr_mip_next[9] = 'b0; // SEIE = 0 if no S
	//csr_mip_next[8] = 'b0; // 0
	//csr_mip_next[7] = 'b0; // MTIE - Machine Timer Interrupt Pending
	//csr_mip_next[6] = 'b0; // 0
	//csr_mip_next[5] = 'b0; // STIE = 0 if no S
	//csr_mip_next[4] = 'b0; // 0
	//csr_mip_next[3] = 'b0; // MSIE - Machine-level Software Interrupt Pending
	//csr_mip_next[2] = 'b0; // 0
	//csr_mip_next[1] = 'b0; // SSIE = 0 if no S
	//csr_mip_next[0] = 'b0; // 0
	csr_mip_next = irq & IRQ_MASK;

	// mtvec - Machine Trap-Vector Base-Address
	csr_mtvec_next[1] = 'b0; // MODE - keep high bit always 0

	// mcause - keep these bits at 0
	csr_mcause_next[30:5] ='b0;

	// mepc - keep alignment
	csr_mepc_next[1:0] = 'b0;

`endif // NERV_CSR

		// act on opcodes
		case (insn_opcode)
			// Load Upper Immediate
			OPCODE_LUI: begin
				next_wr = 1;
				next_rd = insn[31:12] << 12;
			end
			// Add Upper Immediate to Program Counter
			OPCODE_AUIPC: begin
				next_wr = 1;
				next_rd = (insn[31:12] << 12) + pc;
			end
			// Jump And Link (unconditional jump)
			OPCODE_JAL: begin
				next_wr = 1;
				next_rd = npc;
				npc = pc + imm_j_sext;
				if (npc & 32'b 11) begin
					illinsn = 1;
					npc = npc & ~32'b 11;
				end
			end
			// Jump And Link Register (indirect jump)
			OPCODE_JALR: begin
				case (insn_funct3)
					3'b 000 /* JALR */: begin
						next_wr = 1;
						next_rd = npc;
						npc = (rs1_value + imm_i_sext) & ~32'b 1;
					end
					default: illinsn = 1;
				endcase
				if (npc & 32'b 11) begin
					illinsn = 1;
					npc = npc & ~32'b 11;
				end
			end
			// branch instructions: Branch If Equal, Branch Not Equal, Branch Less Than, Branch Greater Than, Branch Less Than Unsigned, Branch Greater Than Unsigned
			OPCODE_BRANCH: begin
				case (insn_funct3)
					3'b 000 /* BEQ  */: begin if (rs1_value == rs2_value) npc = pc + imm_b_sext; end
					3'b 001 /* BNE  */: begin if (rs1_value != rs2_value) npc = pc + imm_b_sext; end
					3'b 100 /* BLT  */: begin if ($signed(rs1_value) < $signed(rs2_value)) npc = pc + imm_b_sext; end
					3'b 101 /* BGE  */: begin if ($signed(rs1_value) >= $signed(rs2_value)) npc = pc + imm_b_sext; end
					3'b 110 /* BLTU */: begin if (rs1_value < rs2_value) npc = pc + imm_b_sext; end
					3'b 111 /* BGEU */: begin if (rs1_value >= rs2_value) npc = pc + imm_b_sext; end
					default: illinsn = 1;
				endcase
				if (npc & 32'b 11) begin
					illinsn = 1;
					npc = npc & ~32'b 11;
				end
			end
			// load from memory into rd: Load Byte, Load Halfword, Load Word, Load Byte Unsigned, Load Halfword Unsigned
			OPCODE_LOAD: begin
				mem_rd_addr = rs1_value + imm_i_sext;
				casez ({insn_funct3, mem_rd_addr[1:0]})
					5'b 000_zz /* LB  */,
					5'b 001_z0 /* LH  */,
					5'b 010_00 /* LW  */,
					5'b 100_zz /* LBU */,
					5'b 101_z0 /* LHU */: begin
						mem_rd_enable = 1;
						mem_rd_reg = insn_rd;
						mem_rd_func = {mem_rd_addr[1:0], insn_funct3};
						mem_rd_addr = {mem_rd_addr[31:2], 2'b 00};
					end
					default: illinsn = 1;
				endcase
			end
			// store to memory instructions: Store Byte, Store Halfword, Store Word
			OPCODE_STORE: begin
				mem_wr_addr = rs1_value + imm_s_sext;
				casez ({insn_funct3, mem_wr_addr[1:0]})
					5'b 000_zz /* SB */,
					5'b 001_z0 /* SH */,
					5'b 010_00 /* SW */: begin
						mem_wr_enable = 1;
						mem_wr_data = rs2_value;
						mem_wr_strb = 4'b 1111;
						case (insn_funct3)
							3'b 000 /* SB  */: begin mem_wr_strb = 4'b 0001; end
							3'b 001 /* SH  */: begin mem_wr_strb = 4'b 0011; end
							3'b 010 /* SW  */: begin mem_wr_strb = 4'b 1111; end
						endcase
						mem_wr_data = mem_wr_data << (8*mem_wr_addr[1:0]);
						mem_wr_strb = mem_wr_strb << mem_wr_addr[1:0];
						mem_wr_addr = {mem_wr_addr[31:2], 2'b 00};
					end
					default: illinsn = 1;
				endcase
			end
			// immediate ALU instructions: Add Immediate, Set Less Than Immediate, Set Less Than Immediate Unsigned, XOR Immediate,
			// OR Immediate, And Immediate, Shift Left Logical Immediate, Shift Right Logical Immediate, Shift Right Arithmetic Immediate
			OPCODE_OP_IMM: begin
				casez ({insn_funct7, insn_funct3})
					10'b zzzzzzz_000 /* ADDI  */: begin next_wr = 1; next_rd = rs1_value + imm_i_sext; end
					10'b zzzzzzz_010 /* SLTI  */: begin next_wr = 1; next_rd = $signed(rs1_value) < $signed(imm_i_sext); end
					10'b zzzzzzz_011 /* SLTIU */: begin next_wr = 1; next_rd = rs1_value < imm_i_sext; end
					10'b zzzzzzz_100 /* XORI  */: begin next_wr = 1; next_rd = rs1_value ^ imm_i_sext; end
					10'b zzzzzzz_110 /* ORI   */: begin next_wr = 1; next_rd = rs1_value | imm_i_sext; end
					10'b zzzzzzz_111 /* ANDI  */: begin next_wr = 1; next_rd = rs1_value & imm_i_sext; end
					10'b 0000000_001 /* SLLI  */: begin next_wr = 1; next_rd = rs1_value << insn[24:20]; end
					10'b 0000000_101 /* SRLI  */: begin next_wr = 1; next_rd = rs1_value >> insn[24:20]; end
					10'b 0100000_101 /* SRAI  */: begin next_wr = 1; next_rd = $signed(rs1_value) >>> insn[24:20]; end
					// Zbb: Basic bit-manipulation
					10'b 0110000_001: begin
						casez (insn[24:20])
							5'b 00000 /* CLZ    */: begin next_wr = 1; next_rd = 0; for (int i=0; i<32; i=i+1) next_rd = rs1_value[i] ? 0 : next_rd + 1; end
							5'b 00001 /* CTZ    */: begin next_wr = 1; next_rd = 0; for (int i=32; i>0; i=i-1) next_rd = rs1_value[i-1] ? 0 : next_rd + 1; end
							5'b 00010 /* CPOP   */: begin next_wr = 1; next_rd = 0; for (int i=0; i<32; i=i+1) next_rd = next_rd + rs1_value[i]; end
							5'b 00100 /* SEXT.B */: begin next_wr = 1; next_rd = $signed(rs1_value[7:0]); end
							5'b 00101 /* SEXT.H */: begin next_wr = 1; next_rd = $signed(rs1_value[15:0]); end
							default: illinsn = 1;
						endcase
					end
					10'b 0110000_101 /* RORI  */: begin next_wr = 1; next_rd = rs1_value >> insn[24:20] | (rs1_value << (32 - insn[24:20])); end
					10'b 0010100_101 /* ORC.B */: begin next_wr = insn[24:20] == 5'b 00111; illinsn = !next_wr; next_rd = 0; for (int i=0; i<4; i=i+1) next_rd[i*8 +: 8] = {8{|rs1_value[i*8 +: 8]}}; end
					10'b 0110100_101: begin
						casez (insn[24:20])
							5'b 11000 /* REV8  */: begin next_wr = 1; next_rd = 0; for (int i=0; i<4; i=i+1) next_rd[i*8 +: 8] = rs1_value[(4-i)*8 - 1 -: 8]; end
							5'b 00111 /* BREV8 */: begin next_wr = 1; next_rd = 0; for (int i=0; i<4; i=i+1) for (int j=0; j<8; j=j+1) next_rd[i*8 + j] = rs1_value[i*8 + 7 - j]; end
							default: illinsn = 1;
						endcase
					end
					10'b 0000100_001 /* ZIP   */: begin next_wr = insn[24:20] == 5'b 01111; illinsn = !next_wr; next_rd = 0; for (int i=0; i<16; i=i+1) begin next_rd[2*i] = rs1_value[i]; next_rd[2*i+1] = rs1_value[i+16]; end end
					10'b 0000100_101 /* UNZIP */: begin next_wr = insn[24:20] == 5'b 01111; illinsn = !next_wr; next_rd = 0; for (int i=0; i<16; i=i+1) begin next_rd[i] = rs1_value[2*i]; next_rd[i+16] = rs1_value[2*i+1]; end end
					// Zbs: Single-bit instructions
					10'b 0100100_001 /* BCLRI */: begin next_wr = 1; next_rd = rs1_value & ~(1 << insn[24:20]); end
					10'b 0100100_101 /* BEXTI */: begin next_wr = 1; next_rd = (rs1_value >> insn[24:20]) & 1; end
					10'b 0110100_001 /* BINVI */: begin next_wr = 1; next_rd = rs1_value ^ (1 << insn[24:20]); end
					10'b 0010100_001 /* BSETI */: begin next_wr = 1; next_rd = rs1_value | (1 << insn[24:20]); end
					default: illinsn = 1;
				endcase
			end
			OPCODE_OP: begin
			// ALU instructions: Add, Subtract, Shift Left Logical, Set Left Than, Set Less Than Unsigned, XOR, Shift Right Logical,
			// Shift Right Arithmetic, OR, AND
				case ({insn_funct7, insn_funct3})
					10'b 0000000_000 /* ADD  */: begin next_wr = 1; next_rd = rs1_value + rs2_value; end
					10'b 0100000_000 /* SUB  */: begin next_wr = 1; next_rd = rs1_value - rs2_value; end
					10'b 0000000_001 /* SLL  */: begin next_wr = 1; next_rd = rs1_value << rs2_value[4:0]; end
					10'b 0000000_010 /* SLT  */: begin next_wr = 1; next_rd = $signed(rs1_value) < $signed(rs2_value); end
					10'b 0000000_011 /* SLTU */: begin next_wr = 1; next_rd = rs1_value < rs2_value; end
					10'b 0000000_100 /* XOR  */: begin next_wr = 1; next_rd = rs1_value ^ rs2_value; end
					10'b 0000000_101 /* SRL  */: begin next_wr = 1; next_rd = rs1_value >> rs2_value[4:0]; end
					10'b 0100000_101 /* SRA  */: begin next_wr = 1; next_rd = $signed(rs1_value) >>> rs2_value[4:0]; end
					10'b 0000000_110 /* OR   */: begin next_wr = 1; next_rd = rs1_value | rs2_value; end
					10'b 0000000_111 /* AND  */: begin next_wr = 1; next_rd = rs1_value & rs2_value; end
					// Zba: Address generation
					10'b 0010000_010 /* SH1ADD */: begin next_wr = 1; next_rd = rs2_value + {rs1_value[30:0], 1'b 0}; end
					10'b 0010000_100 /* SH2ADD */: begin next_wr = 1; next_rd = rs2_value + {rs1_value[29:0], 2'b 0}; end
					10'b 0010000_110 /* SH3ADD */: begin next_wr = 1; next_rd = rs2_value + {rs1_value[28:0], 3'b 0}; end
					// Zbb: Basic bit-manipulation
					10'b 0100000_111 /* ANDN   */: begin next_wr = 1; next_rd = rs1_value & ~rs2_value; end
					10'b 0100000_110 /* ORN    */: begin next_wr = 1; next_rd = rs1_value | ~rs2_value; end
					10'b 0100000_100 /* XNOR   */: begin next_wr = 1; next_rd = ~(rs1_value ^ rs2_value); end
					10'b 0000101_110 /* MAX    */: begin next_wr = 1; next_rd = ($signed(rs1_value) < $signed(rs2_value)) ? rs2_value : rs1_value; end
					10'b 0000101_111 /* MAXU   */: begin next_wr = 1; next_rd = (rs1_value < rs2_value) ? rs2_value : rs1_value; end
					10'b 0000101_100 /* MIN    */: begin next_wr = 1; next_rd = ($signed(rs1_value) < $signed(rs2_value)) ? rs1_value : rs2_value; end
					10'b 0000101_101 /* MINU   */: begin next_wr = 1; next_rd = (rs1_value < rs2_value) ? rs1_value : rs2_value; end
					10'b 0110000_001 /* ROL    */: begin next_wr = 1; next_rd = rs1_value << rs2_value[4:0] | (rs1_value >> (32 - rs2_value[4:0])); end
					10'b 0110000_101 /* ROR    */: begin next_wr = 1; next_rd = rs1_value >> rs2_value[4:0] | (rs1_value << (32 - rs2_value[4:0])); end
					10'b 0000100_100 /* PACK   */: begin next_wr = 1; next_rd = {rs2_value[15:0], rs1_value[15:0]}; end
					10'b 0000100_111 /* PACKH  */: begin next_wr = 1; next_rd = {16'b0, rs2_value[7:0], rs1_value[7:0]}; end
					// Zbc: Carry-less multiplication
					10'b 0000101_001 /* CLMUL  */: begin next_wr = 1; next_rd = 0; for (int i=0; i<32; i=i+1) next_rd = (rs2_value[i]) ? next_rd ^ (rs1_value << i) : next_rd; end
					10'b 0000101_011 /* CLMULH */: begin next_wr = 1; next_rd = 0; for (int i=1; i<33; i=i+1) next_rd = ((rs2_value >> i) & 32'b1) ? next_rd ^ (rs1_value >> (32 - i)) : next_rd; end
					10'b 0000101_010 /* CLMULR */: begin next_wr = 1; next_rd = 0; for (int i=0; i<32; i=i+1) next_rd = (rs2_value[i]) ? next_rd ^ (rs1_value >> (32 - i - 1)) : next_rd; end
					// Zbs: Single-bit instructions
					10'b 0100100_001 /* BCLR */: begin next_wr = 1; next_rd = rs1_value & ~(1 << rs2_value[4:0]); end
					10'b 0100100_101 /* BEXT */: begin next_wr = 1; next_rd = (rs1_value >> rs2_value[4:0]) & 1; end
					10'b 0110100_001 /* BINV */: begin next_wr = 1; next_rd = rs1_value ^ (1 << rs2_value[4:0]); end
					10'b 0010100_001 /* BSET */: begin next_wr = 1; next_rd = rs1_value | (1 << rs2_value[4:0]); end
					// Zbkx: Crossbar permutations
					10'b 0010100_010 /* XPERM4 */: begin next_wr = 1; next_rd = 0; for (int i=0; i<8; i=i+1) next_rd[i*4+:4] = (rs1_value >> (rs2_value[i*4+:4])) & 4'h f; end
					10'b 0010100_100 /* XPERM8 */: begin next_wr = 1; next_rd = 0; for (int i=0; i<4; i=i+1) next_rd[i*8+:8] = (rs1_value >> (rs2_value[i*8+:8])) & 8'h ff; end
					default: illinsn = 1;
				endcase
			end
`ifdef NERV_CSR
			OPCODE_SYSTEM: begin
				case (insn_funct3)
					3'b 000 : begin
						case ({insn_funct7, insn_rs2})
							12'b 0000000_00000 /* ECALL */:
								begin
									csr_mepc_next = { pc[31:2], 2'b00 };
									npc = csr_mtvec_value & ~3;
									csr_mcause_next = MCAUSE_ECALL_M_MODE;
									csr_mstatus_next[7] = csr_mstatus_value[3];  // save MIE to MPIE
									csr_mstatus_next[3] = 0; // MIE to 0
								end
							12'b 0000000_00001 /* EBREAK */:
								begin
									csr_mepc_next = { pc[31:2], 2'b00 };
									npc = csr_mtvec_value & ~3;
									csr_mcause_next = MCAUSE_BREAKPOINT;
									csr_mstatus_next[7] = csr_mstatus_value[3];  // save MIE to MPIE
									csr_mstatus_next[3] = 0; // MIE to 0
								end
							12'b 0011000_00010 /* MRET */:
								begin
									npc = csr_mepc_value;
									csr_mcause_next = 'b0;
									csr_mstatus_next[3] = csr_mstatus_value[7];  // restore MIE from MPIE
								end
							12'b 0001000_00101 /* WFI */:
								begin
									// implemented as NOP
								end
							default: illinsn = 1;
						endcase
					end
					default : begin
						if (csr_ack) begin
							next_wr = 1;
							next_rd = csr_rdval;
						end else
							illinsn = 1;
					end
				endcase
			end
`endif
			default: illinsn = 1;
		endcase

		if (reset || reset_q) begin
			// reset has the highest priority
			npc = RESET_ADDR;
			csr_mstatus_next[3] = 0; // MIE
		end else if (stall) begin
			// if this is a stall cycle, don't perform any action
			npc = pc;
`ifdef NERV_FAULT
		end else if (mem_rd_enable_q || mem_wr_enable_q) begin
			npc = pc;

			if (dmem_fault) begin
				cycle_dmem_fault = 1;
				csr_mepc_next[31:2] = pc[31:2];
				npc = csr_mtvec_value & ~3;
				csr_mcause_next = mem_wr_enable_q ? MCAUSE_STORE_ACCESS_FAULT : MCAUSE_LOAD_ACCESS_FAULT;
				csr_mcause_wdata = csr_mcause_next;
				csr_mstatus_next[7] = csr_mstatus_value[3];  // save MIE to MPIE
				csr_mstatus_next[3] = 0; // MIE to 0
			end else begin
				cycle_late_wr = 1;

				if (mem_rd_enable_q) begin
					wr_rd = mem_rd_reg_q;
					next_rd = mem_rdata;
				end
			end
`else
		end else if (mem_rd_enable_q) begin
			// if last cycle was a memory read, then this cycle is the 2nd part of it and imem_data will not be a valid instruction
			npc = pc;
			cycle_late_wr = 1;
			wr_rd = mem_rd_reg_q;
			next_rd = mem_rdata;
`endif
		end else if (irq_num!=0) begin
			// if there's a pending IRQ, take it
			csr_mepc_next = { pc[31:2], 2'b00 };
			csr_mcause_next = 1 << 31 | irq_num;
			if (csr_mtvec_value & 1)
				npc = (csr_mtvec_value & ~3) + (irq_num << 2);
			else
				npc = csr_mtvec_value & ~3;
			csr_mstatus_next[7] = 1; // MPIE to 1
			csr_mstatus_next[3] = 0; // MIE to 0

			cycle_intr = 1;
		end else if (imem_fault || illinsn) begin
			// instruction fetch memory fault
			cycle_trap = 1;
			csr_mepc_next[31:2] = pc[31:2];
			npc = csr_mtvec_value & ~3;
			csr_mcause_next = imem_fault ? MCAUSE_INSN_ACCESS_FAULT : MCAUSE_INVALID_INSTRUCTION;
			csr_mcause_wdata = csr_mcause_next;
			csr_mstatus_next[7] = csr_mstatus_value[3];  // save MIE to MPIE
			csr_mstatus_next[3] = 0; // MIE to 0
		end else begin
			// the instruction is valid and nothing else has priority
			cycle_insn = 1;
		end

		if (!cycle_insn) begin
			next_wr = cycle_late_wr && mem_rd_enable_q;
			mem_rd_enable = 0;
			mem_wr_enable = 0;
		end
	end

	reg [31:0] mem_rdata;
`ifdef NERV_RVFI
	reg next_rvfi_intr;
	reg rvfi_trap_q;

`ifdef NERV_FAULT
	wire next_rvfi_valid = (cycle_insn && !mem_rd_enable && !mem_wr_enable) || cycle_trap || cycle_dmem_fault || cycle_late_wr;
`else
	wire next_rvfi_valid = (cycle_insn && !mem_rd_enable) || cycle_trap || cycle_late_wr;
`endif

`endif

	// mem read functions: Lower and Upper Bytes, signed and unsigned
	always @* begin
		mem_rdata = dmem_rdata >> (8*mem_rd_func_q[4:3]);
		case (mem_rd_func_q[2:0])
			3'b 000 /* LB  */: begin mem_rdata = $signed(mem_rdata[7:0]); end
			3'b 001 /* LH  */: begin mem_rdata = $signed(mem_rdata[15:0]); end
			3'b 100 /* LBU */: begin mem_rdata = mem_rdata[7:0]; end
			3'b 101 /* LHU */: begin mem_rdata = mem_rdata[15:0]; end
		endcase
	end

	// every cycle
	always @(posedge clock) begin
		reset_q <= reset || (reset_q && stall);

		// update pc
		pc <= npc;

		if (next_wr)
			regfile[wr_rd] <= next_rd;

`ifdef NERV_RVFI
		rvfi_valid <= next_rvfi_valid;

		if (cycle_intr)
			next_rvfi_intr <= 1;

		if (cycle_insn || cycle_late_wr || cycle_trap) begin
			rvfi_rd_addr <= next_wr ? wr_rd : 0;
			rvfi_rd_wdata <= next_wr && wr_rd ? next_rd : 0;
			rvfi_mem_rdata <= dmem_rdata;
		end

		if (cycle_insn || cycle_trap) begin
			next_rvfi_intr <= cycle_trap;
			rvfi_order <= rvfi_order + 1;
			rvfi_insn <= imem_fault ? 32'b0 : insn;
			rvfi_trap <= cycle_trap;
			rvfi_halt <= 0;
			rvfi_intr <= next_rvfi_intr;
			rvfi_mode <= 3;
			rvfi_ixl <= 1;
			rvfi_rs1_addr <= insn_rs1;
			rvfi_rs2_addr <= insn_rs2;
			rvfi_rs1_rdata <= rs1_value;
			rvfi_rs2_rdata <= rs2_value;
			rvfi_pc_rdata <= pc;
			rvfi_pc_wdata <= npc;
			if (dmem_valid) begin
				rvfi_mem_addr <= dmem_addr;
				case ({mem_rd_enable, insn_funct3})
					4'b 1_000 /* LB  */: begin rvfi_mem_rmask <= 4'b 0001 << mem_rd_func[4:3]; end
					4'b 1_001 /* LH  */: begin rvfi_mem_rmask <= 4'b 0011 << mem_rd_func[4:3]; end
					4'b 1_010 /* LW  */: begin rvfi_mem_rmask <= 4'b 1111 << mem_rd_func[4:3]; end
					4'b 1_100 /* LBU */: begin rvfi_mem_rmask <= 4'b 0001 << mem_rd_func[4:3]; end
					4'b 1_101 /* LHU */: begin rvfi_mem_rmask <= 4'b 0011 << mem_rd_func[4:3]; end
					default: rvfi_mem_rmask <= 0;
				endcase
				rvfi_mem_wmask <= dmem_wstrb;
				rvfi_mem_wdata <= dmem_wdata;
			end else begin
				rvfi_mem_addr <= 0;
				rvfi_mem_rmask <= 0;
				rvfi_mem_wmask <= 0;
				rvfi_mem_wdata <= 0;
			end
`ifdef NERV_FAULT
			rvfi_mem_fault <= imem_fault;
			rvfi_mem_fault_rmask <= 0;
			rvfi_mem_fault_wmask <= 0;
`endif
		end

`ifdef NERV_FAULT
		if (cycle_dmem_fault) begin
			next_rvfi_intr <= 1;
			rvfi_trap <= 1;
			rvfi_mem_fault <= 1;
			rvfi_rd_addr <= 0;
			rvfi_rd_wdata <= 0;

			rvfi_mem_fault_rmask <= rvfi_mem_rmask;
			rvfi_mem_fault_wmask <= rvfi_mem_wmask;

			rvfi_mem_rmask <= 0;
			rvfi_mem_wmask <= 0;
		end
`endif

		if (next_rvfi_valid) begin
`ifdef NERV_CSR
`define NERV_CSR_REG_MRW(NAME, ADDR, VALUE) \
			rvfi_csr_``NAME``_rmask <= 32'h ffff_ffff;	\
			rvfi_csr_``NAME``_wmask <= 32'h ffff_ffff;	\
			rvfi_csr_``NAME``_rdata <= csr_``NAME``_value;	\
			rvfi_csr_``NAME``_wdata <= csr_``NAME``_wdata;

`define NERV_CSR_VAL_MRW(NAME, ADDR, VALUE) \
	`NERV_CSR_REG_MRW(NAME, ADDR, VALUE)

`define NERV_CSR_VAL_MRO(NAME, ADDR, VALUE) \
			rvfi_csr_``NAME``_rmask <= 32'h ffff_ffff;	\
			rvfi_csr_``NAME``_wmask <= 32'h ffff_ffff;	\
			rvfi_csr_``NAME``_rdata <= csr_``NAME``_value;	\
			rvfi_csr_``NAME``_wdata <= csr_``NAME``_value;

`define NERV_CSR_ARR_DEF(ARRAY, DEPTH)
`define NERV_CSR_ARR_MRW(ARRAY, INDEX, NAME, ADDR) \
	`NERV_CSR_REG_MRW(NAME, ADDR, 32'h 0000_0000)

`NERV_CSRS
`undef NERV_CSR_REG_MRW
`undef NERV_CSR_VAL_MRW
`undef NERV_CSR_VAL_MRO
`undef NERV_CSR_ARR_DEF
`undef NERV_CSR_ARR_MRW
`endif
		end
`endif

		// reset
		if (reset || reset_q) begin
			pc <= RESET_ADDR - (reset ? 4 : 0);
`ifdef NERV_RVFI
			next_rvfi_intr <= 0;
			rvfi_valid <= 0;
			rvfi_order <= 0;
			rvfi_trap <= 0;
`endif
		end
	end


`ifdef NERV_DBGREGS
	wire [31:0] dbg_reg_x0  = 0;
	wire [31:0] dbg_reg_x1  = regfile[1];
	wire [31:0] dbg_reg_x2  = regfile[2];
	wire [31:0] dbg_reg_x3  = regfile[3];
	wire [31:0] dbg_reg_x4  = regfile[4];
	wire [31:0] dbg_reg_x5  = regfile[5];
	wire [31:0] dbg_reg_x6  = regfile[6];
	wire [31:0] dbg_reg_x7  = regfile[7];
	wire [31:0] dbg_reg_x8  = regfile[8];
	wire [31:0] dbg_reg_x9  = regfile[9];
	wire [31:0] dbg_reg_x10 = regfile[10];
	wire [31:0] dbg_reg_x11 = regfile[11];
	wire [31:0] dbg_reg_x12 = regfile[12];
	wire [31:0] dbg_reg_x13 = regfile[13];
	wire [31:0] dbg_reg_x14 = regfile[14];
	wire [31:0] dbg_reg_x15 = regfile[15];
	wire [31:0] dbg_reg_x16 = regfile[16];
	wire [31:0] dbg_reg_x17 = regfile[17];
	wire [31:0] dbg_reg_x18 = regfile[18];
	wire [31:0] dbg_reg_x19 = regfile[19];
	wire [31:0] dbg_reg_x20 = regfile[20];
	wire [31:0] dbg_reg_x21 = regfile[21];
	wire [31:0] dbg_reg_x22 = regfile[22];
	wire [31:0] dbg_reg_x23 = regfile[23];
	wire [31:0] dbg_reg_x24 = regfile[24];
	wire [31:0] dbg_reg_x25 = regfile[25];
	wire [31:0] dbg_reg_x26 = regfile[26];
	wire [31:0] dbg_reg_x27 = regfile[27];
	wire [31:0] dbg_reg_x28 = regfile[28];
	wire [31:0] dbg_reg_x29 = regfile[29];
	wire [31:0] dbg_reg_x30 = regfile[30];
	wire [31:0] dbg_reg_x31 = regfile[31];
`endif
endmodule
