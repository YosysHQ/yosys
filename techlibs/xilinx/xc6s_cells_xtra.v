// Created by cells_xtra.py from Xilinx models

module MCB (...);
    parameter integer ARB_NUM_TIME_SLOTS = 12;
    parameter [17:0] ARB_TIME_SLOT_0 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_1 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_10 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_11 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_2 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_3 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_4 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_5 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_6 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_7 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_8 = 18'b111111111111111111;
    parameter [17:0] ARB_TIME_SLOT_9 = 18'b111111111111111111;
    parameter [2:0] CAL_BA = 3'h0;
    parameter CAL_BYPASS = "YES";
    parameter [11:0] CAL_CA = 12'h000;
    parameter CAL_CALIBRATION_MODE = "NOCALIBRATION";
    parameter integer CAL_CLK_DIV = 1;
    parameter CAL_DELAY = "QUARTER";
    parameter [14:0] CAL_RA = 15'h0000;
    parameter MEM_ADDR_ORDER = "BANK_ROW_COLUMN";
    parameter integer MEM_BA_SIZE = 3;
    parameter integer MEM_BURST_LEN = 8;
    parameter integer MEM_CAS_LATENCY = 4;
    parameter integer MEM_CA_SIZE = 11;
    parameter MEM_DDR1_2_ODS = "FULL";
    parameter MEM_DDR2_3_HIGH_TEMP_SR = "NORMAL";
    parameter MEM_DDR2_3_PA_SR = "FULL";
    parameter integer MEM_DDR2_ADD_LATENCY = 0;
    parameter MEM_DDR2_DIFF_DQS_EN = "YES";
    parameter MEM_DDR2_RTT = "50OHMS";
    parameter integer MEM_DDR2_WRT_RECOVERY = 4;
    parameter MEM_DDR3_ADD_LATENCY = "OFF";
    parameter MEM_DDR3_AUTO_SR = "ENABLED";
    parameter integer MEM_DDR3_CAS_LATENCY = 7;
    parameter integer MEM_DDR3_CAS_WR_LATENCY = 5;
    parameter MEM_DDR3_DYN_WRT_ODT = "OFF";
    parameter MEM_DDR3_ODS = "DIV7";
    parameter MEM_DDR3_RTT = "DIV2";
    parameter integer MEM_DDR3_WRT_RECOVERY = 7;
    parameter MEM_MDDR_ODS = "FULL";
    parameter MEM_MOBILE_PA_SR = "FULL";
    parameter integer MEM_MOBILE_TC_SR = 0;
    parameter integer MEM_RAS_VAL = 0;
    parameter integer MEM_RA_SIZE = 13;
    parameter integer MEM_RCD_VAL = 1;
    parameter integer MEM_REFI_VAL = 0;
    parameter integer MEM_RFC_VAL = 0;
    parameter integer MEM_RP_VAL = 0;
    parameter integer MEM_RTP_VAL = 0;
    parameter MEM_TYPE = "DDR3";
    parameter integer MEM_WIDTH = 4;
    parameter integer MEM_WR_VAL = 0;
    parameter integer MEM_WTR_VAL = 3;
    parameter PORT_CONFIG = "B32_B32_B32_B32";
    output CAS;
    output CKE;
    output DQIOWEN0;
    output DQSIOWEN90N;
    output DQSIOWEN90P;
    output IOIDRPADD;
    output IOIDRPBROADCAST;
    output IOIDRPCLK;
    output IOIDRPCS;
    output IOIDRPSDO;
    output IOIDRPTRAIN;
    output IOIDRPUPDATE;
    output LDMN;
    output LDMP;
    output ODT;
    output P0CMDEMPTY;
    output P0CMDFULL;
    output P0RDEMPTY;
    output P0RDERROR;
    output P0RDFULL;
    output P0RDOVERFLOW;
    output P0WREMPTY;
    output P0WRERROR;
    output P0WRFULL;
    output P0WRUNDERRUN;
    output P1CMDEMPTY;
    output P1CMDFULL;
    output P1RDEMPTY;
    output P1RDERROR;
    output P1RDFULL;
    output P1RDOVERFLOW;
    output P1WREMPTY;
    output P1WRERROR;
    output P1WRFULL;
    output P1WRUNDERRUN;
    output P2CMDEMPTY;
    output P2CMDFULL;
    output P2EMPTY;
    output P2ERROR;
    output P2FULL;
    output P2RDOVERFLOW;
    output P2WRUNDERRUN;
    output P3CMDEMPTY;
    output P3CMDFULL;
    output P3EMPTY;
    output P3ERROR;
    output P3FULL;
    output P3RDOVERFLOW;
    output P3WRUNDERRUN;
    output P4CMDEMPTY;
    output P4CMDFULL;
    output P4EMPTY;
    output P4ERROR;
    output P4FULL;
    output P4RDOVERFLOW;
    output P4WRUNDERRUN;
    output P5CMDEMPTY;
    output P5CMDFULL;
    output P5EMPTY;
    output P5ERROR;
    output P5FULL;
    output P5RDOVERFLOW;
    output P5WRUNDERRUN;
    output RAS;
    output RST;
    output SELFREFRESHMODE;
    output UDMN;
    output UDMP;
    output UOCALSTART;
    output UOCMDREADYIN;
    output UODATAVALID;
    output UODONECAL;
    output UOREFRSHFLAG;
    output UOSDO;
    output WE;
    output [14:0] ADDR;
    output [15:0] DQON;
    output [15:0] DQOP;
    output [2:0] BA;
    output [31:0] P0RDDATA;
    output [31:0] P1RDDATA;
    output [31:0] P2RDDATA;
    output [31:0] P3RDDATA;
    output [31:0] P4RDDATA;
    output [31:0] P5RDDATA;
    output [31:0] STATUS;
    output [4:0] IOIDRPADDR;
    output [6:0] P0RDCOUNT;
    output [6:0] P0WRCOUNT;
    output [6:0] P1RDCOUNT;
    output [6:0] P1WRCOUNT;
    output [6:0] P2COUNT;
    output [6:0] P3COUNT;
    output [6:0] P4COUNT;
    output [6:0] P5COUNT;
    output [7:0] UODATA;
    input DQSIOIN;
    input DQSIOIP;
    input IOIDRPSDI;
    input P0ARBEN;
    input P0CMDCLK;
    input P0CMDEN;
    input P0RDCLK;
    input P0RDEN;
    input P0WRCLK;
    input P0WREN;
    input P1ARBEN;
    input P1CMDCLK;
    input P1CMDEN;
    input P1RDCLK;
    input P1RDEN;
    input P1WRCLK;
    input P1WREN;
    input P2ARBEN;
    input P2CLK;
    input P2CMDCLK;
    input P2CMDEN;
    input P2EN;
    input P3ARBEN;
    input P3CLK;
    input P3CMDCLK;
    input P3CMDEN;
    input P3EN;
    input P4ARBEN;
    input P4CLK;
    input P4CMDCLK;
    input P4CMDEN;
    input P4EN;
    input P5ARBEN;
    input P5CLK;
    input P5CMDCLK;
    input P5CMDEN;
    input P5EN;
    input PLLLOCK;
    input RECAL;
    input SELFREFRESHENTER;
    input SYSRST;
    input UDQSIOIN;
    input UDQSIOIP;
    input UIADD;
    input UIBROADCAST;
    input UICLK;
    input UICMD;
    input UICMDEN;
    input UICMDIN;
    input UICS;
    input UIDONECAL;
    input UIDQLOWERDEC;
    input UIDQLOWERINC;
    input UIDQUPPERDEC;
    input UIDQUPPERINC;
    input UIDRPUPDATE;
    input UILDQSDEC;
    input UILDQSINC;
    input UIREAD;
    input UISDI;
    input UIUDQSDEC;
    input UIUDQSINC;
    input [11:0] P0CMDCA;
    input [11:0] P1CMDCA;
    input [11:0] P2CMDCA;
    input [11:0] P3CMDCA;
    input [11:0] P4CMDCA;
    input [11:0] P5CMDCA;
    input [14:0] P0CMDRA;
    input [14:0] P1CMDRA;
    input [14:0] P2CMDRA;
    input [14:0] P3CMDRA;
    input [14:0] P4CMDRA;
    input [14:0] P5CMDRA;
    input [15:0] DQI;
    input [1:0] PLLCE;
    input [1:0] PLLCLK;
    input [2:0] P0CMDBA;
    input [2:0] P0CMDINSTR;
    input [2:0] P1CMDBA;
    input [2:0] P1CMDINSTR;
    input [2:0] P2CMDBA;
    input [2:0] P2CMDINSTR;
    input [2:0] P3CMDBA;
    input [2:0] P3CMDINSTR;
    input [2:0] P4CMDBA;
    input [2:0] P4CMDINSTR;
    input [2:0] P5CMDBA;
    input [2:0] P5CMDINSTR;
    input [31:0] P0WRDATA;
    input [31:0] P1WRDATA;
    input [31:0] P2WRDATA;
    input [31:0] P3WRDATA;
    input [31:0] P4WRDATA;
    input [31:0] P5WRDATA;
    input [3:0] P0RWRMASK;
    input [3:0] P1RWRMASK;
    input [3:0] P2WRMASK;
    input [3:0] P3WRMASK;
    input [3:0] P4WRMASK;
    input [3:0] P5WRMASK;
    input [3:0] UIDQCOUNT;
    input [4:0] UIADDR;
    input [5:0] P0CMDBL;
    input [5:0] P1CMDBL;
    input [5:0] P2CMDBL;
    input [5:0] P3CMDBL;
    input [5:0] P4CMDBL;
    input [5:0] P5CMDBL;
endmodule

module PCIE_A1 (...);
    parameter [31:0] BAR0 = 32'h00000000;
    parameter [31:0] BAR1 = 32'h00000000;
    parameter [31:0] BAR2 = 32'h00000000;
    parameter [31:0] BAR3 = 32'h00000000;
    parameter [31:0] BAR4 = 32'h00000000;
    parameter [31:0] BAR5 = 32'h00000000;
    parameter [31:0] CARDBUS_CIS_POINTER = 32'h00000000;
    parameter [23:0] CLASS_CODE = 24'h000000;
    parameter integer DEV_CAP_ENDPOINT_L0S_LATENCY = 7;
    parameter integer DEV_CAP_ENDPOINT_L1_LATENCY = 7;
    parameter DEV_CAP_EXT_TAG_SUPPORTED = "FALSE";
    parameter integer DEV_CAP_MAX_PAYLOAD_SUPPORTED = 2;
    parameter integer DEV_CAP_PHANTOM_FUNCTIONS_SUPPORT = 0;
    parameter DEV_CAP_ROLE_BASED_ERROR = "TRUE";
    parameter DISABLE_BAR_FILTERING = "FALSE";
    parameter DISABLE_ID_CHECK = "FALSE";
    parameter DISABLE_SCRAMBLING = "FALSE";
    parameter ENABLE_RX_TD_ECRC_TRIM = "FALSE";
    parameter [21:0] EXPANSION_ROM = 22'h000000;
    parameter FAST_TRAIN = "FALSE";
    parameter integer GTP_SEL = 0;
    parameter integer LINK_CAP_ASPM_SUPPORT = 1;
    parameter integer LINK_CAP_L0S_EXIT_LATENCY = 7;
    parameter integer LINK_CAP_L1_EXIT_LATENCY = 7;
    parameter LINK_STATUS_SLOT_CLOCK_CONFIG = "FALSE";
    parameter [14:0] LL_ACK_TIMEOUT = 15'h0204;
    parameter LL_ACK_TIMEOUT_EN = "FALSE";
    parameter [14:0] LL_REPLAY_TIMEOUT = 15'h060D;
    parameter LL_REPLAY_TIMEOUT_EN = "FALSE";
    parameter integer MSI_CAP_MULTIMSGCAP = 0;
    parameter integer MSI_CAP_MULTIMSG_EXTENSION = 0;
    parameter [3:0] PCIE_CAP_CAPABILITY_VERSION = 4'h1;
    parameter [3:0] PCIE_CAP_DEVICE_PORT_TYPE = 4'h0;
    parameter [4:0] PCIE_CAP_INT_MSG_NUM = 5'b00000;
    parameter PCIE_CAP_SLOT_IMPLEMENTED = "FALSE";
    parameter [11:0] PCIE_GENERIC = 12'h000;
    parameter PLM_AUTO_CONFIG = "FALSE";
    parameter integer PM_CAP_AUXCURRENT = 0;
    parameter PM_CAP_D1SUPPORT = "TRUE";
    parameter PM_CAP_D2SUPPORT = "TRUE";
    parameter PM_CAP_DSI = "FALSE";
    parameter [4:0] PM_CAP_PMESUPPORT = 5'b01111;
    parameter PM_CAP_PME_CLOCK = "FALSE";
    parameter integer PM_CAP_VERSION = 3;
    parameter [7:0] PM_DATA0 = 8'h1E;
    parameter [7:0] PM_DATA1 = 8'h1E;
    parameter [7:0] PM_DATA2 = 8'h1E;
    parameter [7:0] PM_DATA3 = 8'h1E;
    parameter [7:0] PM_DATA4 = 8'h1E;
    parameter [7:0] PM_DATA5 = 8'h1E;
    parameter [7:0] PM_DATA6 = 8'h1E;
    parameter [7:0] PM_DATA7 = 8'h1E;
    parameter [1:0] PM_DATA_SCALE0 = 2'b01;
    parameter [1:0] PM_DATA_SCALE1 = 2'b01;
    parameter [1:0] PM_DATA_SCALE2 = 2'b01;
    parameter [1:0] PM_DATA_SCALE3 = 2'b01;
    parameter [1:0] PM_DATA_SCALE4 = 2'b01;
    parameter [1:0] PM_DATA_SCALE5 = 2'b01;
    parameter [1:0] PM_DATA_SCALE6 = 2'b01;
    parameter [1:0] PM_DATA_SCALE7 = 2'b01;
    parameter SIM_VERSION = "1.0";
    parameter SLOT_CAP_ATT_BUTTON_PRESENT = "FALSE";
    parameter SLOT_CAP_ATT_INDICATOR_PRESENT = "FALSE";
    parameter SLOT_CAP_POWER_INDICATOR_PRESENT = "FALSE";
    parameter integer TL_RX_RAM_RADDR_LATENCY = 1;
    parameter integer TL_RX_RAM_RDATA_LATENCY = 2;
    parameter integer TL_RX_RAM_WRITE_LATENCY = 0;
    parameter TL_TFC_DISABLE = "FALSE";
    parameter TL_TX_CHECKS_DISABLE = "FALSE";
    parameter integer TL_TX_RAM_RADDR_LATENCY = 0;
    parameter integer TL_TX_RAM_RDATA_LATENCY = 2;
    parameter USR_CFG = "FALSE";
    parameter USR_EXT_CFG = "FALSE";
    parameter VC0_CPL_INFINITE = "TRUE";
    parameter [11:0] VC0_RX_RAM_LIMIT = 12'h01E;
    parameter integer VC0_TOTAL_CREDITS_CD = 104;
    parameter integer VC0_TOTAL_CREDITS_CH = 36;
    parameter integer VC0_TOTAL_CREDITS_NPH = 8;
    parameter integer VC0_TOTAL_CREDITS_PD = 288;
    parameter integer VC0_TOTAL_CREDITS_PH = 32;
    parameter integer VC0_TX_LASTPACKET = 31;
    output CFGCOMMANDBUSMASTERENABLE;
    output CFGCOMMANDINTERRUPTDISABLE;
    output CFGCOMMANDIOENABLE;
    output CFGCOMMANDMEMENABLE;
    output CFGCOMMANDSERREN;
    output CFGDEVCONTROLAUXPOWEREN;
    output CFGDEVCONTROLCORRERRREPORTINGEN;
    output CFGDEVCONTROLENABLERO;
    output CFGDEVCONTROLEXTTAGEN;
    output CFGDEVCONTROLFATALERRREPORTINGEN;
    output CFGDEVCONTROLNONFATALREPORTINGEN;
    output CFGDEVCONTROLNOSNOOPEN;
    output CFGDEVCONTROLPHANTOMEN;
    output CFGDEVCONTROLURERRREPORTINGEN;
    output CFGDEVSTATUSCORRERRDETECTED;
    output CFGDEVSTATUSFATALERRDETECTED;
    output CFGDEVSTATUSNONFATALERRDETECTED;
    output CFGDEVSTATUSURDETECTED;
    output CFGERRCPLRDYN;
    output CFGINTERRUPTMSIENABLE;
    output CFGINTERRUPTRDYN;
    output CFGLINKCONTOLRCB;
    output CFGLINKCONTROLCOMMONCLOCK;
    output CFGLINKCONTROLEXTENDEDSYNC;
    output CFGRDWRDONEN;
    output CFGTOTURNOFFN;
    output DBGBADDLLPSTATUS;
    output DBGBADTLPLCRC;
    output DBGBADTLPSEQNUM;
    output DBGBADTLPSTATUS;
    output DBGDLPROTOCOLSTATUS;
    output DBGFCPROTOCOLERRSTATUS;
    output DBGMLFRMDLENGTH;
    output DBGMLFRMDMPS;
    output DBGMLFRMDTCVC;
    output DBGMLFRMDTLPSTATUS;
    output DBGMLFRMDUNRECTYPE;
    output DBGPOISTLPSTATUS;
    output DBGRCVROVERFLOWSTATUS;
    output DBGREGDETECTEDCORRECTABLE;
    output DBGREGDETECTEDFATAL;
    output DBGREGDETECTEDNONFATAL;
    output DBGREGDETECTEDUNSUPPORTED;
    output DBGRPLYROLLOVERSTATUS;
    output DBGRPLYTIMEOUTSTATUS;
    output DBGURNOBARHIT;
    output DBGURPOISCFGWR;
    output DBGURSTATUS;
    output DBGURUNSUPMSG;
    output MIMRXREN;
    output MIMRXWEN;
    output MIMTXREN;
    output MIMTXWEN;
    output PIPEGTTXELECIDLEA;
    output PIPEGTTXELECIDLEB;
    output PIPERXPOLARITYA;
    output PIPERXPOLARITYB;
    output PIPERXRESETA;
    output PIPERXRESETB;
    output PIPETXRCVRDETA;
    output PIPETXRCVRDETB;
    output RECEIVEDHOTRESET;
    output TRNLNKUPN;
    output TRNREOFN;
    output TRNRERRFWDN;
    output TRNRSOFN;
    output TRNRSRCDSCN;
    output TRNRSRCRDYN;
    output TRNTCFGREQN;
    output TRNTDSTRDYN;
    output TRNTERRDROPN;
    output USERRSTN;
    output [11:0] MIMRXRADDR;
    output [11:0] MIMRXWADDR;
    output [11:0] MIMTXRADDR;
    output [11:0] MIMTXWADDR;
    output [11:0] TRNFCCPLD;
    output [11:0] TRNFCNPD;
    output [11:0] TRNFCPD;
    output [15:0] PIPETXDATAA;
    output [15:0] PIPETXDATAB;
    output [1:0] CFGLINKCONTROLASPMCONTROL;
    output [1:0] PIPEGTPOWERDOWNA;
    output [1:0] PIPEGTPOWERDOWNB;
    output [1:0] PIPETXCHARDISPMODEA;
    output [1:0] PIPETXCHARDISPMODEB;
    output [1:0] PIPETXCHARDISPVALA;
    output [1:0] PIPETXCHARDISPVALB;
    output [1:0] PIPETXCHARISKA;
    output [1:0] PIPETXCHARISKB;
    output [2:0] CFGDEVCONTROLMAXPAYLOAD;
    output [2:0] CFGDEVCONTROLMAXREADREQ;
    output [2:0] CFGFUNCTIONNUMBER;
    output [2:0] CFGINTERRUPTMMENABLE;
    output [2:0] CFGPCIELINKSTATEN;
    output [31:0] CFGDO;
    output [31:0] TRNRD;
    output [34:0] MIMRXWDATA;
    output [35:0] MIMTXWDATA;
    output [4:0] CFGDEVICENUMBER;
    output [4:0] CFGLTSSMSTATE;
    output [5:0] TRNTBUFAV;
    output [6:0] TRNRBARHITN;
    output [7:0] CFGBUSNUMBER;
    output [7:0] CFGINTERRUPTDO;
    output [7:0] TRNFCCPLH;
    output [7:0] TRNFCNPH;
    output [7:0] TRNFCPH;
    input CFGERRCORN;
    input CFGERRCPLABORTN;
    input CFGERRCPLTIMEOUTN;
    input CFGERRECRCN;
    input CFGERRLOCKEDN;
    input CFGERRPOSTEDN;
    input CFGERRURN;
    input CFGINTERRUPTASSERTN;
    input CFGINTERRUPTN;
    input CFGPMWAKEN;
    input CFGRDENN;
    input CFGTRNPENDINGN;
    input CFGTURNOFFOKN;
    input CLOCKLOCKED;
    input MGTCLK;
    input PIPEGTRESETDONEA;
    input PIPEGTRESETDONEB;
    input PIPEPHYSTATUSA;
    input PIPEPHYSTATUSB;
    input PIPERXENTERELECIDLEA;
    input PIPERXENTERELECIDLEB;
    input SYSRESETN;
    input TRNRDSTRDYN;
    input TRNRNPOKN;
    input TRNTCFGGNTN;
    input TRNTEOFN;
    input TRNTERRFWDN;
    input TRNTSOFN;
    input TRNTSRCDSCN;
    input TRNTSRCRDYN;
    input TRNTSTRN;
    input USERCLK;
    input [15:0] CFGDEVID;
    input [15:0] CFGSUBSYSID;
    input [15:0] CFGSUBSYSVENID;
    input [15:0] CFGVENID;
    input [15:0] PIPERXDATAA;
    input [15:0] PIPERXDATAB;
    input [1:0] PIPERXCHARISKA;
    input [1:0] PIPERXCHARISKB;
    input [2:0] PIPERXSTATUSA;
    input [2:0] PIPERXSTATUSB;
    input [2:0] TRNFCSEL;
    input [31:0] TRNTD;
    input [34:0] MIMRXRDATA;
    input [35:0] MIMTXRDATA;
    input [47:0] CFGERRTLPCPLHEADER;
    input [63:0] CFGDSN;
    input [7:0] CFGINTERRUPTDI;
    input [7:0] CFGREVID;
    input [9:0] CFGDWADDR;
endmodule

module DSP48A1 (...);
    parameter integer A0REG = 0;
    parameter integer A1REG = 1;
    parameter integer B0REG = 0;
    parameter integer B1REG = 1;
    parameter integer CARRYINREG = 1;
    parameter integer CARRYOUTREG = 1;
    parameter CARRYINSEL = "OPMODE5";
    parameter integer CREG = 1;
    parameter integer DREG = 1;
    parameter integer MREG = 1;
    parameter integer OPMODEREG = 1;
    parameter integer PREG = 1;
    parameter RSTTYPE = "SYNC";
    output [17:0] BCOUT;
    output CARRYOUT;
    output CARRYOUTF;
    output [35:0] M;
    output [47:0] P;
    output [47:0] PCOUT;
    input [17:0] A;
    input [17:0] B;
    input [47:0] C;
    input CARRYIN;
    input CEA;
    input CEB;
    input CEC;
    input CECARRYIN;
    input CED;
    input CEM;
    input CEOPMODE;
    input CEP;
    (* clkbuf_sink *)
    input CLK;
    input [17:0] D;
    input [7:0] OPMODE;
    input [47:0] PCIN;
    input RSTA;
    input RSTB;
    input RSTC;
    input RSTCARRYIN;
    input RSTD;
    input RSTM;
    input RSTOPMODE;
    input RSTP;
endmodule

module BUFGCE (...);
    parameter CE_TYPE = "SYNC";
    parameter [0:0] IS_CE_INVERTED = 1'b0;
    parameter [0:0] IS_I_INVERTED = 1'b0;
    (* clkbuf_driver *)
    output O;
    (* invertible_pin = "IS_CE_INVERTED" *)
    input CE;
    (* invertible_pin = "IS_I_INVERTED" *)
    input I;
endmodule

module BUFGCE_1 (...);
    (* clkbuf_driver *)
    output O;
    input CE;
    input I;
endmodule

module BUFGMUX (...);
    parameter CLK_SEL_TYPE = "SYNC";
    (* clkbuf_driver *)
    output O;
    input I0;
    input I1;
    input S;
endmodule

module BUFGMUX_1 (...);
    parameter CLK_SEL_TYPE = "SYNC";
    (* clkbuf_driver *)
    output O;
    input I0;
    input I1;
    input S;
endmodule

module BUFH (...);
    (* clkbuf_driver *)
    output O;
    input I;
endmodule

module BUFIO2 (...);
    parameter DIVIDE_BYPASS = "TRUE";
    parameter integer DIVIDE = 1;
    parameter I_INVERT = "FALSE";
    parameter USE_DOUBLER = "FALSE";
    (* clkbuf_driver *)
    output DIVCLK;
    (* clkbuf_driver *)
    output IOCLK;
    output SERDESSTROBE;
    input I;
endmodule

module BUFIO2_2CLK (...);
    parameter integer DIVIDE = 2;
    (* clkbuf_driver *)
    output DIVCLK;
    (* clkbuf_driver *)
    output IOCLK;
    output SERDESSTROBE;
    input I;
    input IB;
endmodule

module BUFIO2FB (...);
    parameter DIVIDE_BYPASS = "TRUE";
    (* clkbuf_driver *)
    output O;
    input I;
endmodule

module BUFPLL_MCB (...);
    parameter integer DIVIDE = 2;
    parameter LOCK_SRC = "LOCK_TO_0";
    (* clkbuf_driver *)
    output IOCLK0;
    (* clkbuf_driver *)
    output IOCLK1;
    output LOCK;
    output SERDESSTROBE0;
    output SERDESSTROBE1;
    input GCLK;
    input LOCKED;
    input PLLIN0;
    input PLLIN1;
endmodule

module DCM_CLKGEN (...);
    parameter SPREAD_SPECTRUM = "NONE";
    parameter STARTUP_WAIT = "FALSE";
    parameter integer CLKFXDV_DIVIDE = 2;
    parameter integer CLKFX_DIVIDE = 1;
    parameter integer CLKFX_MULTIPLY = 4;
    parameter real CLKFX_MD_MAX = 0.0;
    parameter real CLKIN_PERIOD = 0.0;
    output CLKFX180;
    output CLKFX;
    output CLKFXDV;
    output LOCKED;
    output PROGDONE;
    output [2:1] STATUS;
    input CLKIN;
    input FREEZEDCM;
    input PROGCLK;
    input PROGDATA;
    input PROGEN;
    input RST;
endmodule

module DCM_SP (...);
    parameter real CLKDV_DIVIDE = 2.0;
    parameter integer CLKFX_DIVIDE = 1;
    parameter integer CLKFX_MULTIPLY = 4;
    parameter CLKIN_DIVIDE_BY_2 = "FALSE";
    parameter real CLKIN_PERIOD = 10.0;
    parameter CLKOUT_PHASE_SHIFT = "NONE";
    parameter CLK_FEEDBACK = "1X";
    parameter DESKEW_ADJUST = "SYSTEM_SYNCHRONOUS";
    parameter DFS_FREQUENCY_MODE = "LOW";
    parameter DLL_FREQUENCY_MODE = "LOW";
    parameter DSS_MODE = "NONE";
    parameter DUTY_CYCLE_CORRECTION = "TRUE";
    parameter FACTORY_JF = 16'hC080;
    parameter integer PHASE_SHIFT = 0;
    parameter STARTUP_WAIT = "FALSE";
    input CLKFB;
    input CLKIN;
    input DSSEN;
    input PSCLK;
    input PSEN;
    input PSINCDEC;
    input RST;
    output CLK0;
    output CLK180;
    output CLK270;
    output CLK2X;
    output CLK2X180;
    output CLK90;
    output CLKDV;
    output CLKFX;
    output CLKFX180;
    output LOCKED;
    output PSDONE;
    output [7:0] STATUS;
endmodule

module PLL_BASE (...);
    parameter BANDWIDTH = "OPTIMIZED";
    parameter integer CLKFBOUT_MULT = 1;
    parameter real CLKFBOUT_PHASE = 0.0;
    parameter real CLKIN_PERIOD = 0.000;
    parameter integer CLKOUT0_DIVIDE = 1;
    parameter real CLKOUT0_DUTY_CYCLE = 0.5;
    parameter real CLKOUT0_PHASE = 0.0;
    parameter integer CLKOUT1_DIVIDE = 1;
    parameter real CLKOUT1_DUTY_CYCLE = 0.5;
    parameter real CLKOUT1_PHASE = 0.0;
    parameter integer CLKOUT2_DIVIDE = 1;
    parameter real CLKOUT2_DUTY_CYCLE = 0.5;
    parameter real CLKOUT2_PHASE = 0.0;
    parameter integer CLKOUT3_DIVIDE = 1;
    parameter real CLKOUT3_DUTY_CYCLE = 0.5;
    parameter real CLKOUT3_PHASE = 0.0;
    parameter integer CLKOUT4_DIVIDE = 1;
    parameter real CLKOUT4_DUTY_CYCLE = 0.5;
    parameter real CLKOUT4_PHASE = 0.0;
    parameter integer CLKOUT5_DIVIDE = 1;
    parameter real CLKOUT5_DUTY_CYCLE = 0.5;
    parameter real CLKOUT5_PHASE = 0.0;
    parameter CLK_FEEDBACK = "CLKFBOUT";
    parameter COMPENSATION = "SYSTEM_SYNCHRONOUS";
    parameter integer DIVCLK_DIVIDE = 1;
    parameter real REF_JITTER = 0.100;
    parameter RESET_ON_LOSS_OF_LOCK = "FALSE";
    output CLKFBOUT;
    output CLKOUT0;
    output CLKOUT1;
    output CLKOUT2;
    output CLKOUT3;
    output CLKOUT4;
    output CLKOUT5;
    output LOCKED;
    input CLKFBIN;
    input CLKIN;
    input RST;
endmodule

(* keep *)
module BSCAN_SPARTAN6 (...);
    parameter integer JTAG_CHAIN = 1;
    output CAPTURE;
    output DRCK;
    output RESET;
    output RUNTEST;
    output SEL;
    output SHIFT;
    output TCK;
    output TDI;
    output TMS;
    output UPDATE;
    input TDO;
endmodule

module DNA_PORT (...);
    parameter [56:0] SIM_DNA_VALUE = 57'h0;
    output DOUT;
    input CLK;
    input DIN;
    input READ;
    input SHIFT;
endmodule

(* keep *)
module ICAP_SPARTAN6 (...);
    parameter DEVICE_ID = 32'h04000093;
    parameter SIM_CFG_FILE_NAME = "NONE";
    output BUSY;
    output [15:0] O;
    input CLK;
    input CE;
    input WRITE;
    input [15:0] I;
endmodule

module POST_CRC_INTERNAL (...);
    output CRCERROR;
endmodule

(* keep *)
module STARTUP_SPARTAN6 (...);
    output CFGCLK;
    output CFGMCLK;
    output EOS;
    input CLK;
    input GSR;
    input GTS;
    input KEYCLEARB;
endmodule

(* keep *)
module SUSPEND_SYNC (...);
    output SREQ;
    input CLK;
    input SACK;
endmodule

module GTPA1_DUAL (...);
    parameter AC_CAP_DIS_0 = "TRUE";
    parameter AC_CAP_DIS_1 = "TRUE";
    parameter integer ALIGN_COMMA_WORD_0 = 1;
    parameter integer ALIGN_COMMA_WORD_1 = 1;
    parameter integer CB2_INH_CC_PERIOD_0 = 8;
    parameter integer CB2_INH_CC_PERIOD_1 = 8;
    parameter [4:0] CDR_PH_ADJ_TIME_0 = 5'b01010;
    parameter [4:0] CDR_PH_ADJ_TIME_1 = 5'b01010;
    parameter integer CHAN_BOND_1_MAX_SKEW_0 = 7;
    parameter integer CHAN_BOND_1_MAX_SKEW_1 = 7;
    parameter integer CHAN_BOND_2_MAX_SKEW_0 = 1;
    parameter integer CHAN_BOND_2_MAX_SKEW_1 = 1;
    parameter CHAN_BOND_KEEP_ALIGN_0 = "FALSE";
    parameter CHAN_BOND_KEEP_ALIGN_1 = "FALSE";
    parameter [9:0] CHAN_BOND_SEQ_1_1_0 = 10'b0101111100;
    parameter [9:0] CHAN_BOND_SEQ_1_1_1 = 10'b0101111100;
    parameter [9:0] CHAN_BOND_SEQ_1_2_0 = 10'b0001001010;
    parameter [9:0] CHAN_BOND_SEQ_1_2_1 = 10'b0001001010;
    parameter [9:0] CHAN_BOND_SEQ_1_3_0 = 10'b0001001010;
    parameter [9:0] CHAN_BOND_SEQ_1_3_1 = 10'b0001001010;
    parameter [9:0] CHAN_BOND_SEQ_1_4_0 = 10'b0110111100;
    parameter [9:0] CHAN_BOND_SEQ_1_4_1 = 10'b0110111100;
    parameter [3:0] CHAN_BOND_SEQ_1_ENABLE_0 = 4'b1111;
    parameter [3:0] CHAN_BOND_SEQ_1_ENABLE_1 = 4'b1111;
    parameter [9:0] CHAN_BOND_SEQ_2_1_0 = 10'b0110111100;
    parameter [9:0] CHAN_BOND_SEQ_2_1_1 = 10'b0110111100;
    parameter [9:0] CHAN_BOND_SEQ_2_2_0 = 10'b0100111100;
    parameter [9:0] CHAN_BOND_SEQ_2_2_1 = 10'b0100111100;
    parameter [9:0] CHAN_BOND_SEQ_2_3_0 = 10'b0100111100;
    parameter [9:0] CHAN_BOND_SEQ_2_3_1 = 10'b0100111100;
    parameter [9:0] CHAN_BOND_SEQ_2_4_0 = 10'b0100111100;
    parameter [9:0] CHAN_BOND_SEQ_2_4_1 = 10'b0100111100;
    parameter [3:0] CHAN_BOND_SEQ_2_ENABLE_0 = 4'b1111;
    parameter [3:0] CHAN_BOND_SEQ_2_ENABLE_1 = 4'b1111;
    parameter CHAN_BOND_SEQ_2_USE_0 = "FALSE";
    parameter CHAN_BOND_SEQ_2_USE_1 = "FALSE";
    parameter integer CHAN_BOND_SEQ_LEN_0 = 1;
    parameter integer CHAN_BOND_SEQ_LEN_1 = 1;
    parameter integer CLK25_DIVIDER_0 = 4;
    parameter integer CLK25_DIVIDER_1 = 4;
    parameter CLKINDC_B_0 = "TRUE";
    parameter CLKINDC_B_1 = "TRUE";
    parameter CLKRCV_TRST_0 = "TRUE";
    parameter CLKRCV_TRST_1 = "TRUE";
    parameter CLK_CORRECT_USE_0 = "TRUE";
    parameter CLK_CORRECT_USE_1 = "TRUE";
    parameter integer CLK_COR_ADJ_LEN_0 = 1;
    parameter integer CLK_COR_ADJ_LEN_1 = 1;
    parameter integer CLK_COR_DET_LEN_0 = 1;
    parameter integer CLK_COR_DET_LEN_1 = 1;
    parameter CLK_COR_INSERT_IDLE_FLAG_0 = "FALSE";
    parameter CLK_COR_INSERT_IDLE_FLAG_1 = "FALSE";
    parameter CLK_COR_KEEP_IDLE_0 = "FALSE";
    parameter CLK_COR_KEEP_IDLE_1 = "FALSE";
    parameter integer CLK_COR_MAX_LAT_0 = 20;
    parameter integer CLK_COR_MAX_LAT_1 = 20;
    parameter integer CLK_COR_MIN_LAT_0 = 18;
    parameter integer CLK_COR_MIN_LAT_1 = 18;
    parameter CLK_COR_PRECEDENCE_0 = "TRUE";
    parameter CLK_COR_PRECEDENCE_1 = "TRUE";
    parameter integer CLK_COR_REPEAT_WAIT_0 = 0;
    parameter integer CLK_COR_REPEAT_WAIT_1 = 0;
    parameter [9:0] CLK_COR_SEQ_1_1_0 = 10'b0100011100;
    parameter [9:0] CLK_COR_SEQ_1_1_1 = 10'b0100011100;
    parameter [9:0] CLK_COR_SEQ_1_2_0 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_1_2_1 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_1_3_0 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_1_3_1 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_1_4_0 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_1_4_1 = 10'b0000000000;
    parameter [3:0] CLK_COR_SEQ_1_ENABLE_0 = 4'b1111;
    parameter [3:0] CLK_COR_SEQ_1_ENABLE_1 = 4'b1111;
    parameter [9:0] CLK_COR_SEQ_2_1_0 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_2_1_1 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_2_2_0 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_2_2_1 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_2_3_0 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_2_3_1 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_2_4_0 = 10'b0000000000;
    parameter [9:0] CLK_COR_SEQ_2_4_1 = 10'b0000000000;
    parameter [3:0] CLK_COR_SEQ_2_ENABLE_0 = 4'b1111;
    parameter [3:0] CLK_COR_SEQ_2_ENABLE_1 = 4'b1111;
    parameter CLK_COR_SEQ_2_USE_0 = "FALSE";
    parameter CLK_COR_SEQ_2_USE_1 = "FALSE";
    parameter CLK_OUT_GTP_SEL_0 = "REFCLKPLL0";
    parameter CLK_OUT_GTP_SEL_1 = "REFCLKPLL1";
    parameter [1:0] CM_TRIM_0 = 2'b00;
    parameter [1:0] CM_TRIM_1 = 2'b00;
    parameter [9:0] COMMA_10B_ENABLE_0 = 10'b1111111111;
    parameter [9:0] COMMA_10B_ENABLE_1 = 10'b1111111111;
    parameter [3:0] COM_BURST_VAL_0 = 4'b1111;
    parameter [3:0] COM_BURST_VAL_1 = 4'b1111;
    parameter DEC_MCOMMA_DETECT_0 = "TRUE";
    parameter DEC_MCOMMA_DETECT_1 = "TRUE";
    parameter DEC_PCOMMA_DETECT_0 = "TRUE";
    parameter DEC_PCOMMA_DETECT_1 = "TRUE";
    parameter DEC_VALID_COMMA_ONLY_0 = "TRUE";
    parameter DEC_VALID_COMMA_ONLY_1 = "TRUE";
    parameter GTP_CFG_PWRUP_0 = "TRUE";
    parameter GTP_CFG_PWRUP_1 = "TRUE";
    parameter [9:0] MCOMMA_10B_VALUE_0 = 10'b1010000011;
    parameter [9:0] MCOMMA_10B_VALUE_1 = 10'b1010000011;
    parameter MCOMMA_DETECT_0 = "TRUE";
    parameter MCOMMA_DETECT_1 = "TRUE";
    parameter [2:0] OOBDETECT_THRESHOLD_0 = 3'b110;
    parameter [2:0] OOBDETECT_THRESHOLD_1 = 3'b110;
    parameter integer OOB_CLK_DIVIDER_0 = 4;
    parameter integer OOB_CLK_DIVIDER_1 = 4;
    parameter PCI_EXPRESS_MODE_0 = "FALSE";
    parameter PCI_EXPRESS_MODE_1 = "FALSE";
    parameter [9:0] PCOMMA_10B_VALUE_0 = 10'b0101111100;
    parameter [9:0] PCOMMA_10B_VALUE_1 = 10'b0101111100;
    parameter PCOMMA_DETECT_0 = "TRUE";
    parameter PCOMMA_DETECT_1 = "TRUE";
    parameter [2:0] PLLLKDET_CFG_0 = 3'b101;
    parameter [2:0] PLLLKDET_CFG_1 = 3'b101;
    parameter [23:0] PLL_COM_CFG_0 = 24'h21680A;
    parameter [23:0] PLL_COM_CFG_1 = 24'h21680A;
    parameter [7:0] PLL_CP_CFG_0 = 8'h00;
    parameter [7:0] PLL_CP_CFG_1 = 8'h00;
    parameter integer PLL_DIVSEL_FB_0 = 5;
    parameter integer PLL_DIVSEL_FB_1 = 5;
    parameter integer PLL_DIVSEL_REF_0 = 2;
    parameter integer PLL_DIVSEL_REF_1 = 2;
    parameter integer PLL_RXDIVSEL_OUT_0 = 1;
    parameter integer PLL_RXDIVSEL_OUT_1 = 1;
    parameter PLL_SATA_0 = "FALSE";
    parameter PLL_SATA_1 = "FALSE";
    parameter PLL_SOURCE_0 = "PLL0";
    parameter PLL_SOURCE_1 = "PLL0";
    parameter integer PLL_TXDIVSEL_OUT_0 = 1;
    parameter integer PLL_TXDIVSEL_OUT_1 = 1;
    parameter [26:0] PMA_CDR_SCAN_0 = 27'h6404040;
    parameter [26:0] PMA_CDR_SCAN_1 = 27'h6404040;
    parameter [35:0] PMA_COM_CFG_EAST = 36'h000008000;
    parameter [35:0] PMA_COM_CFG_WEST = 36'h00000A000;
    parameter [6:0] PMA_RXSYNC_CFG_0 = 7'h00;
    parameter [6:0] PMA_RXSYNC_CFG_1 = 7'h00;
    parameter [24:0] PMA_RX_CFG_0 = 25'h05CE048;
    parameter [24:0] PMA_RX_CFG_1 = 25'h05CE048;
    parameter [19:0] PMA_TX_CFG_0 = 20'h00082;
    parameter [19:0] PMA_TX_CFG_1 = 20'h00082;
    parameter RCV_TERM_GND_0 = "FALSE";
    parameter RCV_TERM_GND_1 = "FALSE";
    parameter RCV_TERM_VTTRX_0 = "TRUE";
    parameter RCV_TERM_VTTRX_1 = "TRUE";
    parameter [7:0] RXEQ_CFG_0 = 8'b01111011;
    parameter [7:0] RXEQ_CFG_1 = 8'b01111011;
    parameter [0:0] RXPRBSERR_LOOPBACK_0 = 1'b0;
    parameter [0:0] RXPRBSERR_LOOPBACK_1 = 1'b0;
    parameter RX_BUFFER_USE_0 = "TRUE";
    parameter RX_BUFFER_USE_1 = "TRUE";
    parameter RX_DECODE_SEQ_MATCH_0 = "TRUE";
    parameter RX_DECODE_SEQ_MATCH_1 = "TRUE";
    parameter RX_EN_IDLE_HOLD_CDR_0 = "FALSE";
    parameter RX_EN_IDLE_HOLD_CDR_1 = "FALSE";
    parameter RX_EN_IDLE_RESET_BUF_0 = "TRUE";
    parameter RX_EN_IDLE_RESET_BUF_1 = "TRUE";
    parameter RX_EN_IDLE_RESET_FR_0 = "TRUE";
    parameter RX_EN_IDLE_RESET_FR_1 = "TRUE";
    parameter RX_EN_IDLE_RESET_PH_0 = "TRUE";
    parameter RX_EN_IDLE_RESET_PH_1 = "TRUE";
    parameter RX_EN_MODE_RESET_BUF_0 = "TRUE";
    parameter RX_EN_MODE_RESET_BUF_1 = "TRUE";
    parameter [3:0] RX_IDLE_HI_CNT_0 = 4'b1000;
    parameter [3:0] RX_IDLE_HI_CNT_1 = 4'b1000;
    parameter [3:0] RX_IDLE_LO_CNT_0 = 4'b0000;
    parameter [3:0] RX_IDLE_LO_CNT_1 = 4'b0000;
    parameter RX_LOSS_OF_SYNC_FSM_0 = "FALSE";
    parameter RX_LOSS_OF_SYNC_FSM_1 = "FALSE";
    parameter integer RX_LOS_INVALID_INCR_0 = 1;
    parameter integer RX_LOS_INVALID_INCR_1 = 1;
    parameter integer RX_LOS_THRESHOLD_0 = 4;
    parameter integer RX_LOS_THRESHOLD_1 = 4;
    parameter RX_SLIDE_MODE_0 = "PCS";
    parameter RX_SLIDE_MODE_1 = "PCS";
    parameter RX_STATUS_FMT_0 = "PCIE";
    parameter RX_STATUS_FMT_1 = "PCIE";
    parameter RX_XCLK_SEL_0 = "RXREC";
    parameter RX_XCLK_SEL_1 = "RXREC";
    parameter [2:0] SATA_BURST_VAL_0 = 3'b100;
    parameter [2:0] SATA_BURST_VAL_1 = 3'b100;
    parameter [2:0] SATA_IDLE_VAL_0 = 3'b011;
    parameter [2:0] SATA_IDLE_VAL_1 = 3'b011;
    parameter integer SATA_MAX_BURST_0 = 7;
    parameter integer SATA_MAX_BURST_1 = 7;
    parameter integer SATA_MAX_INIT_0 = 22;
    parameter integer SATA_MAX_INIT_1 = 22;
    parameter integer SATA_MAX_WAKE_0 = 7;
    parameter integer SATA_MAX_WAKE_1 = 7;
    parameter integer SATA_MIN_BURST_0 = 4;
    parameter integer SATA_MIN_BURST_1 = 4;
    parameter integer SATA_MIN_INIT_0 = 12;
    parameter integer SATA_MIN_INIT_1 = 12;
    parameter integer SATA_MIN_WAKE_0 = 4;
    parameter integer SATA_MIN_WAKE_1 = 4;
    parameter integer SIM_GTPRESET_SPEEDUP = 0;
    parameter SIM_RECEIVER_DETECT_PASS = "FALSE";
    parameter [2:0] SIM_REFCLK0_SOURCE = 3'b000;
    parameter [2:0] SIM_REFCLK1_SOURCE = 3'b000;
    parameter SIM_TX_ELEC_IDLE_LEVEL = "X";
    parameter SIM_VERSION = "2.0";
    parameter [4:0] TERMINATION_CTRL_0 = 5'b10100;
    parameter [4:0] TERMINATION_CTRL_1 = 5'b10100;
    parameter TERMINATION_OVRD_0 = "FALSE";
    parameter TERMINATION_OVRD_1 = "FALSE";
    parameter [11:0] TRANS_TIME_FROM_P2_0 = 12'h03C;
    parameter [11:0] TRANS_TIME_FROM_P2_1 = 12'h03C;
    parameter [7:0] TRANS_TIME_NON_P2_0 = 8'h19;
    parameter [7:0] TRANS_TIME_NON_P2_1 = 8'h19;
    parameter [9:0] TRANS_TIME_TO_P2_0 = 10'h064;
    parameter [9:0] TRANS_TIME_TO_P2_1 = 10'h064;
    parameter [31:0] TST_ATTR_0 = 32'h00000000;
    parameter [31:0] TST_ATTR_1 = 32'h00000000;
    parameter [2:0] TXRX_INVERT_0 = 3'b011;
    parameter [2:0] TXRX_INVERT_1 = 3'b011;
    parameter TX_BUFFER_USE_0 = "FALSE";
    parameter TX_BUFFER_USE_1 = "FALSE";
    parameter [13:0] TX_DETECT_RX_CFG_0 = 14'h1832;
    parameter [13:0] TX_DETECT_RX_CFG_1 = 14'h1832;
    parameter [2:0] TX_IDLE_DELAY_0 = 3'b011;
    parameter [2:0] TX_IDLE_DELAY_1 = 3'b011;
    parameter [1:0] TX_TDCC_CFG_0 = 2'b00;
    parameter [1:0] TX_TDCC_CFG_1 = 2'b00;
    parameter TX_XCLK_SEL_0 = "TXUSR";
    parameter TX_XCLK_SEL_1 = "TXUSR";
    output DRDY;
    output PHYSTATUS0;
    output PHYSTATUS1;
    output PLLLKDET0;
    output PLLLKDET1;
    output REFCLKOUT0;
    output REFCLKOUT1;
    output REFCLKPLL0;
    output REFCLKPLL1;
    output RESETDONE0;
    output RESETDONE1;
    output RXBYTEISALIGNED0;
    output RXBYTEISALIGNED1;
    output RXBYTEREALIGN0;
    output RXBYTEREALIGN1;
    output RXCHANBONDSEQ0;
    output RXCHANBONDSEQ1;
    output RXCHANISALIGNED0;
    output RXCHANISALIGNED1;
    output RXCHANREALIGN0;
    output RXCHANREALIGN1;
    output RXCOMMADET0;
    output RXCOMMADET1;
    output RXELECIDLE0;
    output RXELECIDLE1;
    output RXPRBSERR0;
    output RXPRBSERR1;
    output RXRECCLK0;
    output RXRECCLK1;
    output RXVALID0;
    output RXVALID1;
    output TXN0;
    output TXN1;
    output TXOUTCLK0;
    output TXOUTCLK1;
    output TXP0;
    output TXP1;
    output [15:0] DRPDO;
    output [1:0] GTPCLKFBEAST;
    output [1:0] GTPCLKFBWEST;
    output [1:0] GTPCLKOUT0;
    output [1:0] GTPCLKOUT1;
    output [1:0] RXLOSSOFSYNC0;
    output [1:0] RXLOSSOFSYNC1;
    output [1:0] TXBUFSTATUS0;
    output [1:0] TXBUFSTATUS1;
    output [2:0] RXBUFSTATUS0;
    output [2:0] RXBUFSTATUS1;
    output [2:0] RXCHBONDO;
    output [2:0] RXCLKCORCNT0;
    output [2:0] RXCLKCORCNT1;
    output [2:0] RXSTATUS0;
    output [2:0] RXSTATUS1;
    output [31:0] RXDATA0;
    output [31:0] RXDATA1;
    output [3:0] RXCHARISCOMMA0;
    output [3:0] RXCHARISCOMMA1;
    output [3:0] RXCHARISK0;
    output [3:0] RXCHARISK1;
    output [3:0] RXDISPERR0;
    output [3:0] RXDISPERR1;
    output [3:0] RXNOTINTABLE0;
    output [3:0] RXNOTINTABLE1;
    output [3:0] RXRUNDISP0;
    output [3:0] RXRUNDISP1;
    output [3:0] TXKERR0;
    output [3:0] TXKERR1;
    output [3:0] TXRUNDISP0;
    output [3:0] TXRUNDISP1;
    output [4:0] RCALOUTEAST;
    output [4:0] RCALOUTWEST;
    output [4:0] TSTOUT0;
    output [4:0] TSTOUT1;
    input CLK00;
    input CLK01;
    input CLK10;
    input CLK11;
    input CLKINEAST0;
    input CLKINEAST1;
    input CLKINWEST0;
    input CLKINWEST1;
    input DCLK;
    input DEN;
    input DWE;
    input GATERXELECIDLE0;
    input GATERXELECIDLE1;
    input GCLK00;
    input GCLK01;
    input GCLK10;
    input GCLK11;
    input GTPRESET0;
    input GTPRESET1;
    input IGNORESIGDET0;
    input IGNORESIGDET1;
    input INTDATAWIDTH0;
    input INTDATAWIDTH1;
    input PLLCLK00;
    input PLLCLK01;
    input PLLCLK10;
    input PLLCLK11;
    input PLLLKDETEN0;
    input PLLLKDETEN1;
    input PLLPOWERDOWN0;
    input PLLPOWERDOWN1;
    input PRBSCNTRESET0;
    input PRBSCNTRESET1;
    input REFCLKPWRDNB0;
    input REFCLKPWRDNB1;
    input RXBUFRESET0;
    input RXBUFRESET1;
    input RXCDRRESET0;
    input RXCDRRESET1;
    input RXCHBONDMASTER0;
    input RXCHBONDMASTER1;
    input RXCHBONDSLAVE0;
    input RXCHBONDSLAVE1;
    input RXCOMMADETUSE0;
    input RXCOMMADETUSE1;
    input RXDEC8B10BUSE0;
    input RXDEC8B10BUSE1;
    input RXENCHANSYNC0;
    input RXENCHANSYNC1;
    input RXENMCOMMAALIGN0;
    input RXENMCOMMAALIGN1;
    input RXENPCOMMAALIGN0;
    input RXENPCOMMAALIGN1;
    input RXENPMAPHASEALIGN0;
    input RXENPMAPHASEALIGN1;
    input RXN0;
    input RXN1;
    input RXP0;
    input RXP1;
    input RXPMASETPHASE0;
    input RXPMASETPHASE1;
    input RXPOLARITY0;
    input RXPOLARITY1;
    input RXRESET0;
    input RXRESET1;
    input RXSLIDE0;
    input RXSLIDE1;
    input RXUSRCLK0;
    input RXUSRCLK1;
    input RXUSRCLK20;
    input RXUSRCLK21;
    input TSTCLK0;
    input TSTCLK1;
    input TXCOMSTART0;
    input TXCOMSTART1;
    input TXCOMTYPE0;
    input TXCOMTYPE1;
    input TXDETECTRX0;
    input TXDETECTRX1;
    input TXELECIDLE0;
    input TXELECIDLE1;
    input TXENC8B10BUSE0;
    input TXENC8B10BUSE1;
    input TXENPMAPHASEALIGN0;
    input TXENPMAPHASEALIGN1;
    input TXINHIBIT0;
    input TXINHIBIT1;
    input TXPDOWNASYNCH0;
    input TXPDOWNASYNCH1;
    input TXPMASETPHASE0;
    input TXPMASETPHASE1;
    input TXPOLARITY0;
    input TXPOLARITY1;
    input TXPRBSFORCEERR0;
    input TXPRBSFORCEERR1;
    input TXRESET0;
    input TXRESET1;
    input TXUSRCLK0;
    input TXUSRCLK1;
    input TXUSRCLK20;
    input TXUSRCLK21;
    input USRCODEERR0;
    input USRCODEERR1;
    input [11:0] TSTIN0;
    input [11:0] TSTIN1;
    input [15:0] DI;
    input [1:0] GTPCLKFBSEL0EAST;
    input [1:0] GTPCLKFBSEL0WEST;
    input [1:0] GTPCLKFBSEL1EAST;
    input [1:0] GTPCLKFBSEL1WEST;
    input [1:0] RXDATAWIDTH0;
    input [1:0] RXDATAWIDTH1;
    input [1:0] RXEQMIX0;
    input [1:0] RXEQMIX1;
    input [1:0] RXPOWERDOWN0;
    input [1:0] RXPOWERDOWN1;
    input [1:0] TXDATAWIDTH0;
    input [1:0] TXDATAWIDTH1;
    input [1:0] TXPOWERDOWN0;
    input [1:0] TXPOWERDOWN1;
    input [2:0] LOOPBACK0;
    input [2:0] LOOPBACK1;
    input [2:0] REFSELDYPLL0;
    input [2:0] REFSELDYPLL1;
    input [2:0] RXCHBONDI;
    input [2:0] RXENPRBSTST0;
    input [2:0] RXENPRBSTST1;
    input [2:0] TXBUFDIFFCTRL0;
    input [2:0] TXBUFDIFFCTRL1;
    input [2:0] TXENPRBSTST0;
    input [2:0] TXENPRBSTST1;
    input [2:0] TXPREEMPHASIS0;
    input [2:0] TXPREEMPHASIS1;
    input [31:0] TXDATA0;
    input [31:0] TXDATA1;
    input [3:0] TXBYPASS8B10B0;
    input [3:0] TXBYPASS8B10B1;
    input [3:0] TXCHARDISPMODE0;
    input [3:0] TXCHARDISPMODE1;
    input [3:0] TXCHARDISPVAL0;
    input [3:0] TXCHARDISPVAL1;
    input [3:0] TXCHARISK0;
    input [3:0] TXCHARISK1;
    input [3:0] TXDIFFCTRL0;
    input [3:0] TXDIFFCTRL1;
    input [4:0] RCALINEAST;
    input [4:0] RCALINWEST;
    input [7:0] DADDR;
    input [7:0] GTPTEST0;
    input [7:0] GTPTEST1;
endmodule

module IBUFDS (...);
    parameter CAPACITANCE = "DONT_CARE";
    parameter DIFF_TERM = "FALSE";
    parameter DQS_BIAS = "FALSE";
    parameter IBUF_DELAY_VALUE = "0";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IFD_DELAY_VALUE = "AUTO";
    parameter IOSTANDARD = "DEFAULT";
    output O;
    (* iopad_external_pin *)
    input I;
    (* iopad_external_pin *)
    input IB;
endmodule

module IBUFDS_DIFF_OUT (...);
    parameter DIFF_TERM = "FALSE";
    parameter DQS_BIAS = "FALSE";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    output O;
    output OB;
    (* iopad_external_pin *)
    input I;
    (* iopad_external_pin *)
    input IB;
endmodule

module IBUFG (...);
    parameter CAPACITANCE = "DONT_CARE";
    parameter IBUF_DELAY_VALUE = "0";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    output O;
    (* iopad_external_pin *)
    input I;
endmodule

module IBUFGDS (...);
    parameter CAPACITANCE = "DONT_CARE";
    parameter DIFF_TERM = "FALSE";
    parameter IBUF_DELAY_VALUE = "0";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    output O;
    (* iopad_external_pin *)
    input I;
    (* iopad_external_pin *)
    input IB;
endmodule

module IBUFGDS_DIFF_OUT (...);
    parameter DIFF_TERM = "FALSE";
    parameter DQS_BIAS = "FALSE";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    output O;
    output OB;
    (* iopad_external_pin *)
    input I;
    (* iopad_external_pin *)
    input IB;
endmodule

module IOBUF (...);
    parameter integer DRIVE = 12;
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    parameter SLEW = "SLOW";
    output O;
    (* iopad_external_pin *)
    inout IO;
    input I;
    input T;
endmodule

module IOBUFDS (...);
    parameter DIFF_TERM = "FALSE";
    parameter DQS_BIAS = "FALSE";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    parameter SLEW = "SLOW";
    output O;
    (* iopad_external_pin *)
    inout IO;
    inout IOB;
    input I;
    input T;
endmodule

module IODELAY2 (...);
    parameter COUNTER_WRAPAROUND = "WRAPAROUND";
    parameter DATA_RATE = "SDR";
    parameter DELAY_SRC = "IO";
    parameter integer IDELAY2_VALUE = 0;
    parameter IDELAY_MODE = "NORMAL";
    parameter IDELAY_TYPE = "DEFAULT";
    parameter integer IDELAY_VALUE = 0;
    parameter integer ODELAY_VALUE = 0;
    parameter SERDES_MODE = "NONE";
    parameter integer SIM_TAPDELAY_VALUE = 75;
    output BUSY;
    output DATAOUT2;
    output DATAOUT;
    output DOUT;
    output TOUT;
    input CAL;
    input CE;
    (* clkbuf_sink *)
    input CLK;
    input IDATAIN;
    input INC;
    (* clkbuf_sink *)
    input IOCLK0;
    (* clkbuf_sink *)
    input IOCLK1;
    input ODATAIN;
    input RST;
    input T;
endmodule

module IODRP2 (...);
    parameter DATA_RATE = "SDR";
    parameter integer SIM_TAPDELAY_VALUE = 75;
    output DATAOUT2;
    output DATAOUT;
    output DOUT;
    output SDO;
    output TOUT;
    input ADD;
    input BKST;
    (* clkbuf_sink *)
    input CLK;
    input CS;
    input IDATAIN;
    (* clkbuf_sink *)
    input IOCLK0;
    (* clkbuf_sink *)
    input IOCLK1;
    input ODATAIN;
    input SDI;
    input T;
endmodule

module IODRP2_MCB (...);
    parameter DATA_RATE = "SDR";
    parameter integer IDELAY_VALUE = 0;
    parameter integer MCB_ADDRESS = 0;
    parameter integer ODELAY_VALUE = 0;
    parameter SERDES_MODE = "NONE";
    parameter integer SIM_TAPDELAY_VALUE = 75;
    output AUXSDO;
    output DATAOUT2;
    output DATAOUT;
    output DOUT;
    output DQSOUTN;
    output DQSOUTP;
    output SDO;
    output TOUT;
    input ADD;
    input AUXSDOIN;
    input BKST;
    (* clkbuf_sink *)
    input CLK;
    input CS;
    input IDATAIN;
    (* clkbuf_sink *)
    input IOCLK0;
    (* clkbuf_sink *)
    input IOCLK1;
    input MEMUPDATE;
    input ODATAIN;
    input SDI;
    input T;
    input [4:0] AUXADDR;
endmodule

module ISERDES2 (...);
    parameter BITSLIP_ENABLE = "FALSE";
    parameter DATA_RATE = "SDR";
    parameter integer DATA_WIDTH = 1;
    parameter INTERFACE_TYPE = "NETWORKING";
    parameter SERDES_MODE = "NONE";
    output CFB0;
    output CFB1;
    output DFB;
    output FABRICOUT;
    output INCDEC;
    output Q1;
    output Q2;
    output Q3;
    output Q4;
    output SHIFTOUT;
    output VALID;
    input BITSLIP;
    input CE0;
    (* clkbuf_sink *)
    input CLK0;
    (* clkbuf_sink *)
    input CLK1;
    (* clkbuf_sink *)
    input CLKDIV;
    input D;
    input IOCE;
    input RST;
    input SHIFTIN;
endmodule

module KEEPER (...);
    inout O;
endmodule

module OBUFDS (...);
    parameter CAPACITANCE = "DONT_CARE";
    parameter IOSTANDARD = "DEFAULT";
    parameter SLEW = "SLOW";
    (* iopad_external_pin *)
    output O;
    (* iopad_external_pin *)
    output OB;
    input I;
endmodule

module OBUFT (...);
    parameter CAPACITANCE = "DONT_CARE";
    parameter integer DRIVE = 12;
    parameter IOSTANDARD = "DEFAULT";
    parameter SLEW = "SLOW";
    (* iopad_external_pin *)
    output O;
    input I;
    input T;
endmodule

module OBUFTDS (...);
    parameter CAPACITANCE = "DONT_CARE";
    parameter IOSTANDARD = "DEFAULT";
    parameter SLEW = "SLOW";
    (* iopad_external_pin *)
    output O;
    (* iopad_external_pin *)
    output OB;
    input I;
    input T;
endmodule

module OSERDES2 (...);
    parameter BYPASS_GCLK_FF = "FALSE";
    parameter DATA_RATE_OQ = "DDR";
    parameter DATA_RATE_OT = "DDR";
    parameter integer DATA_WIDTH = 2;
    parameter OUTPUT_MODE = "SINGLE_ENDED";
    parameter SERDES_MODE = "NONE";
    parameter integer TRAIN_PATTERN = 0;
    output OQ;
    output SHIFTOUT1;
    output SHIFTOUT2;
    output SHIFTOUT3;
    output SHIFTOUT4;
    output TQ;
    (* clkbuf_sink *)
    input CLK0;
    (* clkbuf_sink *)
    input CLK1;
    (* clkbuf_sink *)
    input CLKDIV;
    input D1;
    input D2;
    input D3;
    input D4;
    input IOCE;
    input OCE;
    input RST;
    input SHIFTIN1;
    input SHIFTIN2;
    input SHIFTIN3;
    input SHIFTIN4;
    input T1;
    input T2;
    input T3;
    input T4;
    input TCE;
    input TRAIN;
endmodule

module PULLDOWN (...);
    output O;
endmodule

module PULLUP (...);
    output O;
endmodule

module RAM128X1S (...);
    parameter [127:0] INIT = 128'h00000000000000000000000000000000;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output O;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input A5;
    input A6;
    input D;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module RAM256X1S (...);
    parameter [255:0] INIT = 256'h0;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output O;
    input [7:0] A;
    input D;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module RAM32M (...);
    parameter [63:0] INIT_A = 64'h0000000000000000;
    parameter [63:0] INIT_B = 64'h0000000000000000;
    parameter [63:0] INIT_C = 64'h0000000000000000;
    parameter [63:0] INIT_D = 64'h0000000000000000;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output [1:0] DOA;
    output [1:0] DOB;
    output [1:0] DOC;
    output [1:0] DOD;
    input [4:0] ADDRA;
    input [4:0] ADDRB;
    input [4:0] ADDRC;
    input [4:0] ADDRD;
    input [1:0] DIA;
    input [1:0] DIB;
    input [1:0] DIC;
    input [1:0] DID;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module RAM32X1S (...);
    parameter [31:0] INIT = 32'h00000000;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output O;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input D;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module RAM32X1S_1 (...);
    parameter [31:0] INIT = 32'h00000000;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output O;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input D;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module RAM32X2S (...);
    parameter [31:0] INIT_00 = 32'h00000000;
    parameter [31:0] INIT_01 = 32'h00000000;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output O0;
    output O1;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input D0;
    input D1;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module RAM64M (...);
    parameter [63:0] INIT_A = 64'h0000000000000000;
    parameter [63:0] INIT_B = 64'h0000000000000000;
    parameter [63:0] INIT_C = 64'h0000000000000000;
    parameter [63:0] INIT_D = 64'h0000000000000000;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output DOA;
    output DOB;
    output DOC;
    output DOD;
    input [5:0] ADDRA;
    input [5:0] ADDRB;
    input [5:0] ADDRC;
    input [5:0] ADDRD;
    input DIA;
    input DIB;
    input DIC;
    input DID;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module RAM64X1S (...);
    parameter [63:0] INIT = 64'h0000000000000000;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output O;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input A5;
    input D;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module RAM64X1S_1 (...);
    parameter [63:0] INIT = 64'h0000000000000000;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output O;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input A5;
    input D;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module RAM64X2S (...);
    parameter [63:0] INIT_00 = 64'h0000000000000000;
    parameter [63:0] INIT_01 = 64'h0000000000000000;
    parameter [0:0] IS_WCLK_INVERTED = 1'b0;
    output O0;
    output O1;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input A5;
    input D0;
    input D1;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_WCLK_INVERTED" *)
    input WCLK;
    input WE;
endmodule

module ROM128X1 (...);
    parameter [127:0] INIT = 128'h00000000000000000000000000000000;
    output O;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input A5;
    input A6;
endmodule

module ROM256X1 (...);
    parameter [255:0] INIT = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    output O;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input A5;
    input A6;
    input A7;
endmodule

module ROM32X1 (...);
    parameter [31:0] INIT = 32'h00000000;
    output O;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
endmodule

module ROM64X1 (...);
    parameter [63:0] INIT = 64'h0000000000000000;
    output O;
    input A0;
    input A1;
    input A2;
    input A3;
    input A4;
    input A5;
endmodule

module IDDR2 (...);
    parameter DDR_ALIGNMENT = "NONE";
    parameter [0:0] INIT_Q0 = 1'b0;
    parameter [0:0] INIT_Q1 = 1'b0;
    parameter SRTYPE = "SYNC";
    output Q0;
    output Q1;
    (* clkbuf_sink *)
    input C0;
    (* clkbuf_sink *)
    input C1;
    input CE;
    input D;
    input R;
    input S;
endmodule

module LDCE (...);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_CLR_INVERTED = 1'b0;
    parameter [0:0] IS_G_INVERTED = 1'b0;
    parameter MSGON = "TRUE";
    parameter XON = "TRUE";
    output Q;
    (* invertible_pin = "IS_CLR_INVERTED" *)
    input CLR;
    input D;
    (* invertible_pin = "IS_G_INVERTED" *)
    input G;
    input GE;
endmodule

module LDPE (...);
    parameter [0:0] INIT = 1'b1;
    parameter [0:0] IS_G_INVERTED = 1'b0;
    parameter [0:0] IS_PRE_INVERTED = 1'b0;
    parameter MSGON = "TRUE";
    parameter XON = "TRUE";
    output Q;
    input D;
    (* invertible_pin = "IS_G_INVERTED" *)
    input G;
    input GE;
    (* invertible_pin = "IS_PRE_INVERTED" *)
    input PRE;
endmodule

module ODDR2 (...);
    parameter DDR_ALIGNMENT = "NONE";
    parameter [0:0] INIT = 1'b0;
    parameter SRTYPE = "SYNC";
    output Q;
    (* clkbuf_sink *)
    input C0;
    (* clkbuf_sink *)
    input C1;
    input CE;
    input D0;
    input D1;
    input R;
    input S;
endmodule

module CFGLUT5 (...);
    parameter [31:0] INIT = 32'h00000000;
    parameter [0:0] IS_CLK_INVERTED = 1'b0;
    output CDO;
    output O5;
    output O6;
    input I4;
    input I3;
    input I2;
    input I1;
    input I0;
    input CDI;
    input CE;
    (* clkbuf_sink *)
    (* invertible_pin = "IS_CLK_INVERTED" *)
    input CLK;
endmodule

