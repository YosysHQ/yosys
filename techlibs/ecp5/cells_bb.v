// ECP5 Blackbox cells
// FIXME: Create sim models

(* blackbox *)
module MULT18X18D(
	input A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17,
	input B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17,
	input C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17,
	input SIGNEDA, SIGNEDB, SOURCEA, SOURCEB,
	input CLK0, CLK1, CLK2, CLK3,
	input CE0, CE1, CE2, CE3,
	input RST0, RST1, RST2, RST3,
	input SRIA0, SRIA1, SRIA2, SRIA3, SRIA4, SRIA5, SRIA6, SRIA7, SRIA8, SRIA9, SRIA10, SRIA11, SRIA12, SRIA13, SRIA14, SRIA15, SRIA16, SRIA17,
	input SRIB0, SRIB1, SRIB2, SRIB3, SRIB4, SRIB5, SRIB6, SRIB7, SRIB8, SRIB9, SRIB10, SRIB11, SRIB12, SRIB13, SRIB14, SRIB15, SRIB16, SRIB17,
	output SROA0, SROA1, SROA2, SROA3, SROA4, SROA5, SROA6, SROA7, SROA8, SROA9, SROA10, SROA11, SROA12, SROA13, SROA14, SROA15, SROA16, SROA17,
	output SROB0, SROB1, SROB2, SROB3, SROB4, SROB5, SROB6, SROB7, SROB8, SROB9, SROB10, SROB11, SROB12, SROB13, SROB14, SROB15, SROB16, SROB17,
	output ROA0, ROA1, ROA2, ROA3, ROA4, ROA5, ROA6, ROA7, ROA8, ROA9, ROA10, ROA11, ROA12, ROA13, ROA14, ROA15, ROA16, ROA17,
	output ROB0, ROB1, ROB2, ROB3, ROB4, ROB5, ROB6, ROB7, ROB8, ROB9, ROB10, ROB11, ROB12, ROB13, ROB14, ROB15, ROB16, ROB17,
	output ROC0, ROC1, ROC2, ROC3, ROC4, ROC5, ROC6, ROC7, ROC8, ROC9, ROC10, ROC11, ROC12, ROC13, ROC14, ROC15, ROC16, ROC17,
	output P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, P28, P29, P30, P31, P32, P33, P34, P35,
	output SIGNEDP
);
	parameter REG_INPUTA_CLK = "NONE";
	parameter REG_INPUTA_CE = "CE0";
	parameter REG_INPUTA_RST = "RST0";
	parameter REG_INPUTB_CLK = "NONE";
	parameter REG_INPUTB_CE = "CE0";
	parameter REG_INPUTB_RST = "RST0";
	parameter REG_INPUTC_CLK = "NONE";
	parameter REG_PIPELINE_CLK = "NONE";
	parameter REG_PIPELINE_CE = "CE0";
	parameter REG_PIPELINE_RST = "RST0";
	parameter REG_OUTPUT_CLK = "NONE";
	parameter [127:0] CLK0_DIV = "ENABLED";
	parameter [127:0] CLK1_DIV = "ENABLED";
	parameter [127:0] CLK2_DIV = "ENABLED";
	parameter [127:0] CLK3_DIV = "ENABLED";
	parameter [127:0] GSR = "ENABLED";
	parameter [127:0] SOURCEB_MODE = "B_SHIFT";
	parameter [127:0] RESETMODE = "SYNC";
endmodule

(* blackbox *)
module ALU54B(
	input CLK0, CLK1, CLK2, CLK3,
	input CE0, CE1, CE2, CE3,
	input RST0, RST1, RST2, RST3,
	input SIGNEDIA, SIGNEDIB, SIGNEDCIN,
	input A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35,
	input B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35,
	input C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19, C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31, C32, C33, C34, C35, C36, C37, C38, C39, C40, C41, C42, C43, C44, C45, C46, C47, C48, C49, C50, C51, C52, C53,
	input CFB0, CFB1, CFB2, CFB3, CFB4, CFB5, CFB6, CFB7, CFB8, CFB9, CFB10, CFB11, CFB12, CFB13, CFB14, CFB15, CFB16, CFB17, CFB18, CFB19, CFB20, CFB21, CFB22, CFB23, CFB24, CFB25, CFB26, CFB27, CFB28, CFB29, CFB30, CFB31, CFB32, CFB33, CFB34, CFB35, CFB36, CFB37, CFB38, CFB39, CFB40, CFB41, CFB42, CFB43, CFB44, CFB45, CFB46, CFB47, CFB48, CFB49, CFB50, CFB51, CFB52, CFB53,
	input MA0, MA1, MA2, MA3, MA4, MA5, MA6, MA7, MA8, MA9, MA10, MA11, MA12, MA13, MA14, MA15, MA16, MA17, MA18, MA19, MA20, MA21, MA22, MA23, MA24, MA25, MA26, MA27, MA28, MA29, MA30, MA31, MA32, MA33, MA34, MA35,
	input MB0, MB1, MB2, MB3, MB4, MB5, MB6, MB7, MB8, MB9, MB10, MB11, MB12, MB13, MB14, MB15, MB16, MB17, MB18, MB19, MB20, MB21, MB22, MB23, MB24, MB25, MB26, MB27, MB28, MB29, MB30, MB31, MB32, MB33, MB34, MB35,
	input CIN0, CIN1, CIN2, CIN3, CIN4, CIN5, CIN6, CIN7, CIN8, CIN9, CIN10, CIN11, CIN12, CIN13, CIN14, CIN15, CIN16, CIN17, CIN18, CIN19, CIN20, CIN21, CIN22, CIN23, CIN24, CIN25, CIN26, CIN27, CIN28, CIN29, CIN30, CIN31, CIN32, CIN33, CIN34, CIN35, CIN36, CIN37, CIN38, CIN39, CIN40, CIN41, CIN42, CIN43, CIN44, CIN45, CIN46, CIN47, CIN48, CIN49, CIN50, CIN51, CIN52, CIN53,
	input OP0, OP1, OP2, OP3, OP4, OP5, OP6, OP7, OP8, OP9, OP10,
	output R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, R16, R17, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27, R28, R29, R30, R31, R32, R33, R34, R35, R36, R37, R38, R39, R40, R41, R42, R43, R44, R45, R46, R47, R48, R49, R50, R51, R52, R53,
	output CO0, CO1, CO2, CO3, CO4, CO5, CO6, CO7, CO8, CO9, CO10, CO11, CO12, CO13, CO14, CO15, CO16, CO17, CO18, CO19, CO20, CO21, CO22, CO23, CO24, CO25, CO26, CO27, CO28, CO29, CO30, CO31, CO32, CO33, CO34, CO35, CO36, CO37, CO38, CO39, CO40, CO41, CO42, CO43, CO44, CO45, CO46, CO47, CO48, CO49, CO50, CO51, CO52, CO53,
	output EQZ, EQZM, EQOM, EQPAT, EQPATB,
	output OVER, UNDER, OVERUNDER,
	output SIGNEDR
);
	parameter REG_INPUTC0_CLK = "NONE";
	parameter REG_INPUTC1_CLK = "NONE";
	parameter REG_OPCODEOP0_0_CLK = "NONE";
	parameter REG_OPCODEOP0_0_CE = "CE0";
	parameter REG_OPCODEOP0_0_RST = "RST0";
	parameter REG_OPCODEOP1_0_CLK = "NONE";
	parameter REG_OPCODEOP0_1_CLK = "NONE";
	parameter REG_OPCODEOP0_1_CE = "CE0";
	parameter REG_OPCODEOP0_1_RST = "RST0";
	parameter REG_OPCODEIN_0_CLK = "NONE";
	parameter REG_OPCODEIN_0_CE = "CE0";
	parameter REG_OPCODEIN_0_RST = "RST0";
	parameter REG_OPCODEIN_1_CLK = "NONE";
	parameter REG_OPCODEIN_1_CE = "CE0";
	parameter REG_OPCODEIN_1_RST = "RST0";
	parameter REG_OUTPUT0_CLK = "NONE";
	parameter REG_OUTPUT1_CLK = "NONE";
	parameter REG_FLAG_CLK = "NONE";
	parameter [127:0] MCPAT_SOURCE = "STATIC";
	parameter [127:0] MASKPAT_SOURCE = "STATIC";
	parameter MASK01 = "0x00000000000000";
	parameter [127:0] CLK0_DIV = "ENABLED";
	parameter [127:0] CLK1_DIV = "ENABLED";
	parameter [127:0] CLK2_DIV = "ENABLED";
	parameter [127:0] CLK3_DIV = "ENABLED";
	parameter MCPAT = "0x00000000000000";
	parameter MASKPAT = "0x00000000000000";
	parameter RNDPAT = "0x00000000000000";
	parameter [127:0] GSR = "ENABLED";
	parameter [127:0] RESETMODE = "SYNC";
	parameter FORCE_ZERO_BARREL_SHIFT = "DISABLED";
	parameter LEGACY = "DISABLED";
endmodule

(* blackbox *)
module EHXPLLL (
	input CLKI, CLKFB,
	input PHASESEL1, PHASESEL0, PHASEDIR, PHASESTEP, PHASELOADREG,
	input STDBY, PLLWAKESYNC,
	input RST, ENCLKOP, ENCLKOS, ENCLKOS2, ENCLKOS3,
	output CLKOP, CLKOS, CLKOS2, CLKOS3,
	output LOCK, INTLOCK,
	output REFCLK, CLKINTFB
);
	parameter CLKI_DIV = 1;
	parameter CLKFB_DIV = 1;
	parameter CLKOP_DIV = 8;
	parameter CLKOS_DIV = 8;
	parameter CLKOS2_DIV = 8;
	parameter CLKOS3_DIV = 8;
	parameter CLKOP_ENABLE = "ENABLED";
	parameter CLKOS_ENABLE = "DISABLED";
	parameter CLKOS2_ENABLE = "DISABLED";
	parameter CLKOS3_ENABLE = "DISABLED";
	parameter CLKOP_CPHASE = 0;
	parameter CLKOS_CPHASE = 0;
	parameter CLKOS2_CPHASE = 0;
	parameter CLKOS3_CPHASE = 0;
	parameter CLKOP_FPHASE = 0;
	parameter CLKOS_FPHASE = 0;
	parameter CLKOS2_FPHASE = 0;
	parameter CLKOS3_FPHASE = 0;
	parameter FEEDBK_PATH = "CLKOP";
	parameter CLKOP_TRIM_POL = "RISING";
	parameter CLKOP_TRIM_DELAY = 0;
	parameter CLKOS_TRIM_POL = "RISING";
	parameter CLKOS_TRIM_DELAY = 0;
	parameter OUTDIVIDER_MUXA = "DIVA";
	parameter OUTDIVIDER_MUXB = "DIVB";
	parameter OUTDIVIDER_MUXC = "DIVC";
	parameter OUTDIVIDER_MUXD = "DIVD";
	parameter PLL_LOCK_MODE = 0;
	parameter PLL_LOCK_DELAY = 200;
	parameter STDBY_ENABLE = "DISABLED";
	parameter REFIN_RESET = "DISABLED";
	parameter SYNC_ENABLE = "DISABLED";
	parameter INT_LOCK_STICKY = "ENABLED";
	parameter DPHASE_SOURCE = "DISABLED";
	parameter PLLRST_ENA = "DISABLED";
	parameter INTFB_WAKE = "DISABLED";
endmodule

(* blackbox *)
module DTR(
	input STARTPULSE,
	output DTROUT7, DTROUT6, DTROUT5, DTROUT4, DTROUT3, DTROUT2, DTROUT1, DTROUT0
);
endmodule

(* blackbox *)
module OSCG(
	output OSC
);
parameter DIV = 128;
endmodule

(* blackbox *) (* keep *)
module USRMCLK(
	input USRMCLKI, USRMCLKTS,
	output USRMCLKO
);
endmodule

(* blackbox *) (* keep *)
module JTAGG(
	input TCK, TMS, TDI, JTDO2, JTDO1,
	output TDO, JTDI, JTCK, JRTI2, JRTI1,
	output JSHIFT, JUPDATE, JRSTN, JCE2, JCE1
);
parameter ER1 = "ENABLED";
parameter ER2 = "ENABLED";
endmodule

(* blackbox *)
module DELAYF(
	input A, LOADN, MOVE, DIRECTION,
	output Z, CFLAG
);
	parameter DEL_MODE = "USER_DEFINED";
	parameter DEL_VALUE = 0;
endmodule

(* blackbox *)
module DELAYG(
	input A,
	output Z
);
	parameter DEL_MODE = "USER_DEFINED";
	parameter DEL_VALUE = 0;
endmodule

(* blackbox *)
module IDDRX1F(
	input D, SCLK, RST,
	output Q0, Q1
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module IDDRX2F(
	input D, SCLK, ECLK, RST,
	output Q0, Q1, Q2, Q3
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module IDDR71B(
	input D, SCLK, ECLK, RST, ALIGNWD,
	output Q0, Q1, Q2, Q3, Q4, Q5, Q6
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module IDDRX2DQA(
	input D, DQSR90, ECLK, SCLK, RST,
	input RDPNTR2, RDPNTR1, RDPNTR0, WRPNTR2, WRPNTR1, WRPNTR0,
	output Q0, Q1, Q2, Q3, QWL
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module ODDRX1F(
	input SCLK, RST, D0, D1,
	output Q
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module ODDRX2F(
	input SCLK, ECLK, RST, D0, D1, D2, D3,
	output Q
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module ODDR71B(
	input SCLK, ECLK, RST, D0, D1, D2, D3, D4, D5, D6,
	output Q
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module OSHX2A(
	input D0, D1, RST, ECLK, SCLK,
	output Q
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module ODDRX2DQA(
	input D0, D1, D2, D3, RST, ECLK, SCLK, DQSW270,
	output Q
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module ODDRX2DQSB(
	input D0, D1, D2, D3, RST, ECLK, SCLK, DQSW,
	output Q
);
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module TSHX2DQA(
	input T0, T1, SCLK, ECLK, DQSW270, RST,
	output Q
);
	parameter GSR = "ENABLED";
	parameter REGSET = "SET";
endmodule

(* blackbox *)
module TSHX2DQSA(
	input T0, T1, SCLK, ECLK, DQSW, RST,
	output Q
);
	parameter GSR = "ENABLED";
	parameter REGSET = "SET";
endmodule

(* blackbox *)
module DQSBUFM(
	input DQSI, READ1, READ0, READCLKSEL2, READCLKSEL1, READCLKSEL0, DDRDEL,
	input ECLK, SCLK,
	input DYNDELAY7, DYNDELAY6, DYNDELAY5, DYNDELAY4,
	input DYNDELAY3, DYNDELAY2, DYNDELAY1, DYNDELAY0, 
	input RST, RDLOADN, RDMOVE, RDDIRECTION, WRLOADN, WRMOVE, WRDIRECTION, PAUSE,
	output DQSR90, DQSW, DQSW270,
	output RDPNTR2, RDPNTR1, RDPNTR0, WRPNTR2, WRPNTR1, WRPNTR0,
	output DATAVALID, BURSTDET, RDCFLAG, WRCFLAG
);
	parameter DQS_LI_DEL_ADJ = "FACTORYONLY";
	parameter DQS_LI_DEL_VAL = 0;
	parameter DQS_LO_DEL_ADJ = "FACTORYONLY";
	parameter DQS_LO_DEL_VAL = 0;
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module DDRDLLA(
	input CLK, RST, UDDCNTLN, FREEZE,
	output LOCK, DDRDEL, DCNTL7, DCNTL6, DCNTL5, DCNTL4, DCNTL3, DCNTL2, DCNTL1, DCNTL0
);
	parameter FORCE_MAX_DELAY = "NO";
	parameter GSR = "ENABLED";
endmodule

(* blackbox *)
module CLKDIVF(
	input CLKI, RST, ALIGNWD,
	output CDIVX
);
	parameter GSR = "DISABLED";
	parameter DIV = "2.0";
endmodule

(* blackbox *)
module ECLKSYNCB(
	input ECLKI, STOP,
	output ECLKO
);
endmodule

(* blackbox *)
module DCCA(
	input CLKI, CE,
	output CLKO
);
endmodule

(* blackbox *) (* keep *)
module DCUA(
	input CH0_HDINP, CH1_HDINP, CH0_HDINN, CH1_HDINN,
	input D_TXBIT_CLKP_FROM_ND, D_TXBIT_CLKN_FROM_ND, D_SYNC_ND, D_TXPLL_LOL_FROM_ND,
	input CH0_RX_REFCLK, CH1_RX_REFCLK, CH0_FF_RXI_CLK, CH1_FF_RXI_CLK, CH0_FF_TXI_CLK, CH1_FF_TXI_CLK, CH0_FF_EBRD_CLK, CH1_FF_EBRD_CLK,
	input CH0_FF_TX_D_0, CH1_FF_TX_D_0, CH0_FF_TX_D_1, CH1_FF_TX_D_1, CH0_FF_TX_D_2, CH1_FF_TX_D_2, CH0_FF_TX_D_3, CH1_FF_TX_D_3,
	input CH0_FF_TX_D_4, CH1_FF_TX_D_4, CH0_FF_TX_D_5, CH1_FF_TX_D_5, CH0_FF_TX_D_6, CH1_FF_TX_D_6, CH0_FF_TX_D_7, CH1_FF_TX_D_7,
	input CH0_FF_TX_D_8, CH1_FF_TX_D_8, CH0_FF_TX_D_9, CH1_FF_TX_D_9, CH0_FF_TX_D_10, CH1_FF_TX_D_10, CH0_FF_TX_D_11, CH1_FF_TX_D_11,
	input CH0_FF_TX_D_12, CH1_FF_TX_D_12, CH0_FF_TX_D_13, CH1_FF_TX_D_13, CH0_FF_TX_D_14, CH1_FF_TX_D_14, CH0_FF_TX_D_15, CH1_FF_TX_D_15,
	input CH0_FF_TX_D_16, CH1_FF_TX_D_16, CH0_FF_TX_D_17, CH1_FF_TX_D_17, CH0_FF_TX_D_18, CH1_FF_TX_D_18, CH0_FF_TX_D_19, CH1_FF_TX_D_19,
	input CH0_FF_TX_D_20, CH1_FF_TX_D_20, CH0_FF_TX_D_21, CH1_FF_TX_D_21, CH0_FF_TX_D_22, CH1_FF_TX_D_22, CH0_FF_TX_D_23, CH1_FF_TX_D_23,
	input CH0_FFC_EI_EN, CH1_FFC_EI_EN, CH0_FFC_PCIE_DET_EN, CH1_FFC_PCIE_DET_EN, CH0_FFC_PCIE_CT, CH1_FFC_PCIE_CT, CH0_FFC_SB_INV_RX, CH1_FFC_SB_INV_RX,
	input CH0_FFC_ENABLE_CGALIGN, CH1_FFC_ENABLE_CGALIGN, CH0_FFC_SIGNAL_DETECT, CH1_FFC_SIGNAL_DETECT, CH0_FFC_FB_LOOPBACK, CH1_FFC_FB_LOOPBACK, CH0_FFC_SB_PFIFO_LP, CH1_FFC_SB_PFIFO_LP,
	input CH0_FFC_PFIFO_CLR, CH1_FFC_PFIFO_CLR, CH0_FFC_RATE_MODE_RX, CH1_FFC_RATE_MODE_RX, CH0_FFC_RATE_MODE_TX, CH1_FFC_RATE_MODE_TX, CH0_FFC_DIV11_MODE_RX, CH1_FFC_DIV11_MODE_RX, CH0_FFC_RX_GEAR_MODE, CH1_FFC_RX_GEAR_MODE, CH0_FFC_TX_GEAR_MODE, CH1_FFC_TX_GEAR_MODE,
	input CH0_FFC_DIV11_MODE_TX, CH1_FFC_DIV11_MODE_TX, CH0_FFC_LDR_CORE2TX_EN, CH1_FFC_LDR_CORE2TX_EN, CH0_FFC_LANE_TX_RST, CH1_FFC_LANE_TX_RST, CH0_FFC_LANE_RX_RST, CH1_FFC_LANE_RX_RST,
	input CH0_FFC_RRST, CH1_FFC_RRST, CH0_FFC_TXPWDNB, CH1_FFC_TXPWDNB, CH0_FFC_RXPWDNB, CH1_FFC_RXPWDNB, CH0_LDR_CORE2TX, CH1_LDR_CORE2TX,
	input D_SCIWDATA0, D_SCIWDATA1, D_SCIWDATA2, D_SCIWDATA3, D_SCIWDATA4, D_SCIWDATA5, D_SCIWDATA6, D_SCIWDATA7,
	input D_SCIADDR0, D_SCIADDR1, D_SCIADDR2, D_SCIADDR3, D_SCIADDR4, D_SCIADDR5, D_SCIENAUX, D_SCISELAUX,
	input CH0_SCIEN, CH1_SCIEN, CH0_SCISEL, CH1_SCISEL, D_SCIRD, D_SCIWSTN, D_CYAWSTN, D_FFC_SYNC_TOGGLE,
	input D_FFC_DUAL_RST, D_FFC_MACRO_RST, D_FFC_MACROPDB, D_FFC_TRST, CH0_FFC_CDR_EN_BITSLIP, CH1_FFC_CDR_EN_BITSLIP, D_SCAN_ENABLE, D_SCAN_IN_0,
	input D_SCAN_IN_1, D_SCAN_IN_2, D_SCAN_IN_3, D_SCAN_IN_4, D_SCAN_IN_5, D_SCAN_IN_6, D_SCAN_IN_7, D_SCAN_MODE,
	input D_SCAN_RESET, D_CIN0, D_CIN1, D_CIN2, D_CIN3, D_CIN4, D_CIN5, D_CIN6,D_CIN7, D_CIN8, D_CIN9, D_CIN10, D_CIN11,
	output CH0_HDOUTP, CH1_HDOUTP, CH0_HDOUTN, CH1_HDOUTN, D_TXBIT_CLKP_TO_ND, D_TXBIT_CLKN_TO_ND, D_SYNC_PULSE2ND, D_TXPLL_LOL_TO_ND,
	output CH0_FF_RX_F_CLK, CH1_FF_RX_F_CLK, CH0_FF_RX_H_CLK, CH1_FF_RX_H_CLK, CH0_FF_TX_F_CLK, CH1_FF_TX_F_CLK, CH0_FF_TX_H_CLK, CH1_FF_TX_H_CLK,
	output CH0_FF_RX_PCLK, CH1_FF_RX_PCLK, CH0_FF_TX_PCLK, CH1_FF_TX_PCLK, CH0_FF_RX_D_0, CH1_FF_RX_D_0, CH0_FF_RX_D_1, CH1_FF_RX_D_1,
	output CH0_FF_RX_D_2, CH1_FF_RX_D_2, CH0_FF_RX_D_3, CH1_FF_RX_D_3, CH0_FF_RX_D_4, CH1_FF_RX_D_4, CH0_FF_RX_D_5, CH1_FF_RX_D_5,
	output CH0_FF_RX_D_6, CH1_FF_RX_D_6, CH0_FF_RX_D_7, CH1_FF_RX_D_7, CH0_FF_RX_D_8, CH1_FF_RX_D_8, CH0_FF_RX_D_9, CH1_FF_RX_D_9,
	output CH0_FF_RX_D_10, CH1_FF_RX_D_10, CH0_FF_RX_D_11, CH1_FF_RX_D_11, CH0_FF_RX_D_12, CH1_FF_RX_D_12, CH0_FF_RX_D_13, CH1_FF_RX_D_13,
	output CH0_FF_RX_D_14, CH1_FF_RX_D_14, CH0_FF_RX_D_15, CH1_FF_RX_D_15, CH0_FF_RX_D_16, CH1_FF_RX_D_16, CH0_FF_RX_D_17, CH1_FF_RX_D_17,
	output CH0_FF_RX_D_18, CH1_FF_RX_D_18, CH0_FF_RX_D_19, CH1_FF_RX_D_19, CH0_FF_RX_D_20, CH1_FF_RX_D_20, CH0_FF_RX_D_21, CH1_FF_RX_D_21,
	output CH0_FF_RX_D_22, CH1_FF_RX_D_22, CH0_FF_RX_D_23, CH1_FF_RX_D_23, CH0_FFS_PCIE_DONE, CH1_FFS_PCIE_DONE, CH0_FFS_PCIE_CON, CH1_FFS_PCIE_CON,
	output CH0_FFS_RLOS, CH1_FFS_RLOS, CH0_FFS_LS_SYNC_STATUS, CH1_FFS_LS_SYNC_STATUS, CH0_FFS_CC_UNDERRUN, CH1_FFS_CC_UNDERRUN, CH0_FFS_CC_OVERRUN, CH1_FFS_CC_OVERRUN,
	output CH0_FFS_RXFBFIFO_ERROR, CH1_FFS_RXFBFIFO_ERROR, CH0_FFS_TXFBFIFO_ERROR, CH1_FFS_TXFBFIFO_ERROR, CH0_FFS_RLOL, CH1_FFS_RLOL, CH0_FFS_SKP_ADDED, CH1_FFS_SKP_ADDED,
	output CH0_FFS_SKP_DELETED, CH1_FFS_SKP_DELETED, CH0_LDR_RX2CORE, CH1_LDR_RX2CORE, D_SCIRDATA0, D_SCIRDATA1, D_SCIRDATA2, D_SCIRDATA3,
	output D_SCIRDATA4, D_SCIRDATA5, D_SCIRDATA6, D_SCIRDATA7, D_SCIINT, D_SCAN_OUT_0, D_SCAN_OUT_1, D_SCAN_OUT_2, D_SCAN_OUT_3, D_SCAN_OUT_4, D_SCAN_OUT_5, D_SCAN_OUT_6, D_SCAN_OUT_7,
	output D_COUT0, D_COUT1, D_COUT2, D_COUT3, D_COUT4, D_COUT5, D_COUT6, D_COUT7, D_COUT8, D_COUT9, D_COUT10, D_COUT11, D_COUT12, D_COUT13, D_COUT14, D_COUT15, D_COUT16, D_COUT17, D_COUT18, D_COUT19,

	input  D_REFCLKI,
	output D_FFS_PLOL
);
	parameter CH0_AUTO_CALIB_EN = "0b0";
	parameter CH0_AUTO_FACQ_EN = "0b0";
	parameter CH0_BAND_THRESHOLD = "0b000000";
	parameter CH0_CALIB_CK_MODE = "0b0";
	parameter CH0_CC_MATCH_1 = "0b0000000000";
	parameter CH0_CC_MATCH_2 = "0b0000000000";
	parameter CH0_CC_MATCH_3 = "0b0000000000";
	parameter CH0_CC_MATCH_4 = "0b0000000000";
	parameter CH0_CDR_CNT4SEL = "0b00";
	parameter CH0_CDR_CNT8SEL = "0b00";
	parameter CH0_CTC_BYPASS = "0b0";
	parameter CH0_DCOATDCFG = "0b00";
	parameter CH0_DCOATDDLY = "0b00";
	parameter CH0_DCOBYPSATD = "0b0";
	parameter CH0_DCOCALDIV = "0b000";
	parameter CH0_DCOCTLGI = "0b000";
	parameter CH0_DCODISBDAVOID = "0b0";
	parameter CH0_DCOFLTDAC = "0b00";
	parameter CH0_DCOFTNRG = "0b000";
	parameter CH0_DCOIOSTUNE = "0b000";
	parameter CH0_DCOITUNE = "0b00";
	parameter CH0_DCOITUNE4LSB = "0b000";
	parameter CH0_DCOIUPDNX2 = "0b0";
	parameter CH0_DCONUOFLSB = "0b000";
	parameter CH0_DCOSCALEI = "0b00";
	parameter CH0_DCOSTARTVAL = "0b000";
	parameter CH0_DCOSTEP = "0b00";
	parameter CH0_DEC_BYPASS = "0b0";
	parameter CH0_ENABLE_CG_ALIGN = "0b0";
	parameter CH0_ENC_BYPASS = "0b0";
	parameter CH0_FF_RX_F_CLK_DIS = "0b0";
	parameter CH0_FF_RX_H_CLK_EN = "0b0";
	parameter CH0_FF_TX_F_CLK_DIS = "0b0";
	parameter CH0_FF_TX_H_CLK_EN = "0b0";
	parameter CH0_GE_AN_ENABLE = "0b0";
	parameter CH0_INVERT_RX = "0b0";
	parameter CH0_INVERT_TX = "0b0";
	parameter CH0_LDR_CORE2TX_SEL = "0b0";
	parameter CH0_LDR_RX2CORE_SEL = "0b0";
	parameter CH0_LEQ_OFFSET_SEL = "0b0";
	parameter CH0_LEQ_OFFSET_TRIM = "0b000";
	parameter CH0_LSM_DISABLE = "0b0";
	parameter CH0_MATCH_2_ENABLE = "0b0";
	parameter CH0_MATCH_4_ENABLE = "0b0";
	parameter CH0_MIN_IPG_CNT = "0b00";
	parameter CH0_PCIE_EI_EN = "0b0";
	parameter CH0_PCIE_MODE = "0b0";
	parameter CH0_PCS_DET_TIME_SEL = "0b00";
	parameter CH0_PDEN_SEL = "0b0";
	parameter CH0_PRBS_ENABLE = "0b0";
	parameter CH0_PRBS_LOCK = "0b0";
	parameter CH0_PRBS_SELECTION = "0b0";
	parameter CH0_RATE_MODE_RX = "0b0";
	parameter CH0_RATE_MODE_TX = "0b0";
	parameter CH0_RCV_DCC_EN = "0b0";
	parameter CH0_REG_BAND_OFFSET = "0b0000";
	parameter CH0_REG_BAND_SEL = "0b000000";
	parameter CH0_REG_IDAC_EN = "0b0";
	parameter CH0_REG_IDAC_SEL = "0b0000000000";
	parameter CH0_REQ_EN = "0b0";
	parameter CH0_REQ_LVL_SET = "0b00";
	parameter CH0_RIO_MODE = "0b0";
	parameter CH0_RLOS_SEL = "0b0";
	parameter CH0_RPWDNB = "0b0";
	parameter CH0_RTERM_RX = "0b00000";
	parameter CH0_RTERM_TX = "0b00000";
	parameter CH0_RXIN_CM = "0b00";
	parameter CH0_RXTERM_CM = "0b00";
	parameter CH0_RX_DCO_CK_DIV = "0b000";
	parameter CH0_RX_DIV11_SEL = "0b0";
	parameter CH0_RX_GEAR_BYPASS = "0b0";
	parameter CH0_RX_GEAR_MODE = "0b0";
	parameter CH0_RX_LOS_CEQ = "0b00";
	parameter CH0_RX_LOS_EN = "0b0";
	parameter CH0_RX_LOS_HYST_EN = "0b0";
	parameter CH0_RX_LOS_LVL = "0b000";
	parameter CH0_RX_RATE_SEL = "0b0000";
	parameter CH0_RX_SB_BYPASS = "0b0";
	parameter CH0_SB_BYPASS = "0b0";
	parameter CH0_SEL_SD_RX_CLK = "0b0";
	parameter CH0_TDRV_DAT_SEL = "0b00";
	parameter CH0_TDRV_POST_EN = "0b0";
	parameter CH0_TDRV_PRE_EN = "0b0";
	parameter CH0_TDRV_SLICE0_CUR = "0b000";
	parameter CH0_TDRV_SLICE0_SEL = "0b00";
	parameter CH0_TDRV_SLICE1_CUR = "0b000";
	parameter CH0_TDRV_SLICE1_SEL = "0b00";
	parameter CH0_TDRV_SLICE2_CUR = "0b00";
	parameter CH0_TDRV_SLICE2_SEL = "0b00";
	parameter CH0_TDRV_SLICE3_CUR = "0b00";
	parameter CH0_TDRV_SLICE3_SEL = "0b00";
	parameter CH0_TDRV_SLICE4_CUR = "0b00";
	parameter CH0_TDRV_SLICE4_SEL = "0b00";
	parameter CH0_TDRV_SLICE5_CUR = "0b00";
	parameter CH0_TDRV_SLICE5_SEL = "0b00";
	parameter CH0_TPWDNB = "0b0";
	parameter CH0_TX_CM_SEL = "0b00";
	parameter CH0_TX_DIV11_SEL = "0b0";
	parameter CH0_TX_GEAR_BYPASS = "0b0";
	parameter CH0_TX_GEAR_MODE = "0b0";
	parameter CH0_TX_POST_SIGN = "0b0";
	parameter CH0_TX_PRE_SIGN = "0b0";
	parameter CH0_UC_MODE = "0b0";
	parameter CH0_UDF_COMMA_A = "0b0000000000";
	parameter CH0_UDF_COMMA_B = "0b0000000000";
	parameter CH0_UDF_COMMA_MASK = "0b0000000000";
	parameter CH0_WA_BYPASS = "0b0";
	parameter CH0_WA_MODE = "0b0";
	parameter CH1_AUTO_CALIB_EN = "0b0";
	parameter CH1_AUTO_FACQ_EN = "0b0";
	parameter CH1_BAND_THRESHOLD = "0b000000";
	parameter CH1_CALIB_CK_MODE = "0b0";
	parameter CH1_CC_MATCH_1 = "0b0000000000";
	parameter CH1_CC_MATCH_2 = "0b0000000000";
	parameter CH1_CC_MATCH_3 = "0b0000000000";
	parameter CH1_CC_MATCH_4 = "0b0000000000";
	parameter CH1_CDR_CNT4SEL = "0b00";
	parameter CH1_CDR_CNT8SEL = "0b00";
	parameter CH1_CTC_BYPASS = "0b0";
	parameter CH1_DCOATDCFG = "0b00";
	parameter CH1_DCOATDDLY = "0b00";
	parameter CH1_DCOBYPSATD = "0b0";
	parameter CH1_DCOCALDIV = "0b000";
	parameter CH1_DCOCTLGI = "0b000";
	parameter CH1_DCODISBDAVOID = "0b0";
	parameter CH1_DCOFLTDAC = "0b00";
	parameter CH1_DCOFTNRG = "0b000";
	parameter CH1_DCOIOSTUNE = "0b000";
	parameter CH1_DCOITUNE = "0b00";
	parameter CH1_DCOITUNE4LSB = "0b000";
	parameter CH1_DCOIUPDNX2 = "0b0";
	parameter CH1_DCONUOFLSB = "0b000";
	parameter CH1_DCOSCALEI = "0b00";
	parameter CH1_DCOSTARTVAL = "0b000";
	parameter CH1_DCOSTEP = "0b00";
	parameter CH1_DEC_BYPASS = "0b0";
	parameter CH1_ENABLE_CG_ALIGN = "0b0";
	parameter CH1_ENC_BYPASS = "0b0";
	parameter CH1_FF_RX_F_CLK_DIS = "0b0";
	parameter CH1_FF_RX_H_CLK_EN = "0b0";
	parameter CH1_FF_TX_F_CLK_DIS = "0b0";
	parameter CH1_FF_TX_H_CLK_EN = "0b0";
	parameter CH1_GE_AN_ENABLE = "0b0";
	parameter CH1_INVERT_RX = "0b0";
	parameter CH1_INVERT_TX = "0b0";
	parameter CH1_LDR_CORE2TX_SEL = "0b0";
	parameter CH1_LDR_RX2CORE_SEL = "0b0";
	parameter CH1_LEQ_OFFSET_SEL = "0b0";
	parameter CH1_LEQ_OFFSET_TRIM = "0b000";
	parameter CH1_LSM_DISABLE = "0b0";
	parameter CH1_MATCH_2_ENABLE = "0b0";
	parameter CH1_MATCH_4_ENABLE = "0b0";
	parameter CH1_MIN_IPG_CNT = "0b00";
	parameter CH1_PCIE_EI_EN = "0b0";
	parameter CH1_PCIE_MODE = "0b0";
	parameter CH1_PCS_DET_TIME_SEL = "0b00";
	parameter CH1_PDEN_SEL = "0b0";
	parameter CH1_PRBS_ENABLE = "0b0";
	parameter CH1_PRBS_LOCK = "0b0";
	parameter CH1_PRBS_SELECTION = "0b0";
	parameter CH1_RATE_MODE_RX = "0b0";
	parameter CH1_RATE_MODE_TX = "0b0";
	parameter CH1_RCV_DCC_EN = "0b0";
	parameter CH1_REG_BAND_OFFSET = "0b0000";
	parameter CH1_REG_BAND_SEL = "0b000000";
	parameter CH1_REG_IDAC_EN = "0b0";
	parameter CH1_REG_IDAC_SEL = "0b0000000000";
	parameter CH1_REQ_EN = "0b0";
	parameter CH1_REQ_LVL_SET = "0b00";
	parameter CH1_RIO_MODE = "0b0";
	parameter CH1_RLOS_SEL = "0b0";
	parameter CH1_RPWDNB = "0b0";
	parameter CH1_RTERM_RX = "0b00000";
	parameter CH1_RTERM_TX = "0b00000";
	parameter CH1_RXIN_CM = "0b00";
	parameter CH1_RXTERM_CM = "0b00";
	parameter CH1_RX_DCO_CK_DIV = "0b000";
	parameter CH1_RX_DIV11_SEL = "0b0";
	parameter CH1_RX_GEAR_BYPASS = "0b0";
	parameter CH1_RX_GEAR_MODE = "0b0";
	parameter CH1_RX_LOS_CEQ = "0b00";
	parameter CH1_RX_LOS_EN = "0b0";
	parameter CH1_RX_LOS_HYST_EN = "0b0";
	parameter CH1_RX_LOS_LVL = "0b000";
	parameter CH1_RX_RATE_SEL = "0b0000";
	parameter CH1_RX_SB_BYPASS = "0b0";
	parameter CH1_SB_BYPASS = "0b0";
	parameter CH1_SEL_SD_RX_CLK = "0b0";
	parameter CH1_TDRV_DAT_SEL = "0b00";
	parameter CH1_TDRV_POST_EN = "0b0";
	parameter CH1_TDRV_PRE_EN = "0b0";
	parameter CH1_TDRV_SLICE0_CUR = "0b000";
	parameter CH1_TDRV_SLICE0_SEL = "0b00";
	parameter CH1_TDRV_SLICE1_CUR = "0b000";
	parameter CH1_TDRV_SLICE1_SEL = "0b00";
	parameter CH1_TDRV_SLICE2_CUR = "0b00";
	parameter CH1_TDRV_SLICE2_SEL = "0b00";
	parameter CH1_TDRV_SLICE3_CUR = "0b00";
	parameter CH1_TDRV_SLICE3_SEL = "0b00";
	parameter CH1_TDRV_SLICE4_CUR = "0b00";
	parameter CH1_TDRV_SLICE4_SEL = "0b00";
	parameter CH1_TDRV_SLICE5_CUR = "0b00";
	parameter CH1_TDRV_SLICE5_SEL = "0b00";
	parameter CH1_TPWDNB = "0b0";
	parameter CH1_TX_CM_SEL = "0b00";
	parameter CH1_TX_DIV11_SEL = "0b0";
	parameter CH1_TX_GEAR_BYPASS = "0b0";
	parameter CH1_TX_GEAR_MODE = "0b0";
	parameter CH1_TX_POST_SIGN = "0b0";
	parameter CH1_TX_PRE_SIGN = "0b0";
	parameter CH1_UC_MODE = "0b0";
	parameter CH1_UDF_COMMA_A = "0b0000000000";
	parameter CH1_UDF_COMMA_B = "0b0000000000";
	parameter CH1_UDF_COMMA_MASK = "0b0000000000";
	parameter CH1_WA_BYPASS = "0b0";
	parameter CH1_WA_MODE = "0b0";
	parameter D_BITCLK_FROM_ND_EN = "0b0";
	parameter D_BITCLK_LOCAL_EN = "0b0";
	parameter D_BITCLK_ND_EN = "0b0";
	parameter D_BUS8BIT_SEL = "0b0";
	parameter D_CDR_LOL_SET = "0b00";
	parameter D_CMUSETBIASI = "0b00";
	parameter D_CMUSETI4CPP = "0b0000";
	parameter D_CMUSETI4CPZ = "0b0000";
	parameter D_CMUSETI4VCO = "0b00";
	parameter D_CMUSETICP4P = "0b00";
	parameter D_CMUSETICP4Z = "0b000";
	parameter D_CMUSETINITVCT = "0b00";
	parameter D_CMUSETISCL4VCO = "0b000";
	parameter D_CMUSETP1GM = "0b000";
	parameter D_CMUSETP2AGM = "0b000";
	parameter D_CMUSETZGM = "0b000";
	parameter D_DCO_CALIB_TIME_SEL = "0b00";
	parameter D_HIGH_MARK = "0b0000";
	parameter D_IB_PWDNB = "0b0";
	parameter D_ISETLOS = "0b00000000";
	parameter D_LOW_MARK = "0b0000";
	parameter D_MACROPDB = "0b0";
	parameter D_PD_ISET = "0b00";
	parameter D_PLL_LOL_SET = "0b00";
	parameter D_REFCK_MODE = "0b000";
	parameter D_REQ_ISET = "0b000";
	parameter D_RG_EN = "0b0";
	parameter D_RG_SET = "0b00";
	parameter D_SETICONST_AUX = "0b00";
	parameter D_SETICONST_CH = "0b00";
	parameter D_SETIRPOLY_AUX = "0b00";
	parameter D_SETIRPOLY_CH = "0b00";
	parameter D_SETPLLRC = "0b000000";
	parameter D_SYNC_LOCAL_EN = "0b0";
	parameter D_SYNC_ND_EN = "0b0";
	parameter D_TXPLL_PWDNB = "0b0";
	parameter D_TX_VCO_CK_DIV = "0b000";
	parameter D_XGE_MODE = "0b0";

// These parameters don't do anything but are
// needed for compatibility with Diamond
	parameter D_TX_MAX_RATE = "2.5";
	parameter D_RX_MAX_RATE = "2.5";
	parameter CH0_TXAMPLITUDE = "0d1300";
	parameter CH1_TXAMPLITUDE = "0d1300";
	parameter CH0_PROTOCOL = "8B10B";
	parameter CH1_PROTOCOL = "8B10B";
	parameter CH0_CDR_MAX_RATE = "2.5";
	parameter CH1_CDR_MAX_RATE = "2.5";
endmodule

(* blackbox *)
module EXTREFB (
	input  REFCLKP, REFCLKN,
	output REFCLKO
);
	parameter REFCK_PWDNB = "0b0";
	parameter REFCK_RTERM = "0b0";
	parameter REFCK_DCBIAS_EN = "0b0";
endmodule

(* blackbox *)
module PCSCLKDIV (
	input CLKI, RST, SEL2, SEL1, SEL0,
	output CDIV1, CDIVX
);
	parameter GSR = "DISABLED";
endmodule

// Note: this module is not marked keep as we want it swept away in synth (sim use only)
(* blackbox *)
module PUR (
	input PUR
);
	parameter RST_PULSE = 1;
endmodule

(* blackbox, keep *)
module GSR (
	input GSR
);
endmodule

(* blackbox, keep *)
module SGSR (
	input GSR, CLK
);
endmodule