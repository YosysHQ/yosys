/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Cologne Chip AG <support@colognechip.com>
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

(* blackbox *)
module CC_PLL #(
	parameter REF_CLK = "", // e.g. "10.0"
	parameter OUT_CLK = "", // e.g. "50.0"
	parameter PERF_MD = "", // LOWPOWER, ECONOMY, SPEED
	parameter LOCK_REQ = 1,
	parameter CLK270_DOUB = 0,
	parameter CLK180_DOUB = 0,
	parameter LOW_JITTER = 1,
	parameter CI_FILTER_CONST = 2,
	parameter CP_FILTER_CONST = 4
)(
	input  CLK_REF, CLK_FEEDBACK, USR_CLK_REF,
	input  USR_LOCKED_STDY_RST,
	output USR_PLL_LOCKED_STDY, USR_PLL_LOCKED,
	output CLK270, CLK180, CLK90, CLK0, CLK_REF_OUT
);
endmodule

(* blackbox *)
module CC_PLL_ADV #(
	parameter [95:0] PLL_CFG_A = 96'bx,
	parameter [95:0] PLL_CFG_B = 96'bx
)(
	input  CLK_REF, CLK_FEEDBACK, USR_CLK_REF,
	input  USR_LOCKED_STDY_RST, USR_SEL_A_B,
	output USR_PLL_LOCKED_STDY, USR_PLL_LOCKED,
	output CLK270, CLK180, CLK90, CLK0, CLK_REF_OUT
);
endmodule

(* blackbox *) (* keep *)
module CC_SERDES #(
	parameter SERDES_CFG = ""
)(
	input [63:0] TX_DATA_I,
	input TX_RESET_I,
	input TX_PCS_RESET_I,
	input TX_PMA_RESET_I,
	input PLL_RESET_I,
	input TX_POWERDOWN_N_I,
	input TX_POLARITY_I,
	input [2:0] TX_PRBS_SEL_I,
	input TX_PRBS_FORCE_ERR_I,
	input TX_8B10B_EN_I,
	input [7:0] TX_8B10B_BYPASS_I,
	input [7:0] TX_CHAR_IS_K_I,
	input [7:0] TX_CHAR_DISPMODE_I,
	input [7:0] TX_CHAR_DISPVAL_I,
	input TX_ELEC_IDLE_I,
	input TX_DETECT_RX_I,
	input [2:0] LOOPBACK_I,
	input CLK_CORE_TX_I,
	input CLK_CORE_RX_I,
	input RX_RESET_I,
	input RX_PMA_RESET_I,
	input RX_EQA_RESET_I,
	input RX_CDR_RESET_I,
	input RX_PCS_RESET_I,
	input RX_BUF_RESET_I,
	input RX_POWERDOWN_N_I,
	input RX_POLARITY_I,
	input [2:0] RX_PRBS_SEL_I,
	input RX_PRBS_CNT_RESET_I,
	input RX_8B10B_EN_I,
	input [7:0] RX_8B10B_BYPASS_I,
	input RX_EN_EI_DETECTOR_I,
	input RX_COMMA_DETECT_EN_I,
	input RX_SLIDE_I,
	input RX_MCOMMA_ALIGN_I,
	input RX_PCOMMA_ALIGN_I,
	input CLK_REG_I,
	input REGFILE_WE_I,
	input REGFILE_EN_I,
	input [7:0] REGFILE_ADDR_I,
	input [15:0] REGFILE_DI_I,
	input [15:0] REGFILE_MASK_I,
	output [63:0] RX_DATA_O,
	output [7:0] RX_NOT_IN_TABLE_O,
	output [7:0] RX_CHAR_IS_COMMA_O,
	output [7:0] RX_CHAR_IS_K_O,
	output [7:0] RX_DISP_ERR_O,
	output RX_DETECT_DONE_O,
	output RX_PRESENT_O,
	output TX_BUF_ERR_O,
	output TX_RESETDONE_O,
	output RX_PRBS_ERR_O,
	output RX_BUF_ERR_O,
	output RX_BYTE_IS_ALIGNED_O,
	output RX_BYTE_REALIGN_O,
	output RX_RESETDONE_O,
	output RX_EI_EN_O,
	output CLK_CORE_RX_O,
	output CLK_CORE_PLL_O,
	output [15:0] REGFILE_DO_O,
	output REGFILE_RDY_O
);
endmodule

(* blackbox *) (* keep *)
module CC_CFG_CTRL(
	input [7:0] DATA,
	input CLK,
	input EN,
	input RECFG,
	input VALID
);
endmodule

(* blackbox *) (* keep *)
module CC_USR_RSTN (
	output USR_RSTN
);
endmodule
