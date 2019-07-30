// UG615
//   https://www.xilinx.com/support/documentation/sw_manuals/xilinx14_7/spartan6_hdl.pdf

module PLL_ADV (...);
    parameter BANDWIDTH = "OPTIMIZED";
    parameter CLKFBOUT_DESKEW_ADJUST = "NONE";
    parameter integer CLKFBOUT_MULT = 1;
    parameter real CLKFBOUT_PHASE = 0.0;
    parameter CLK_FEEDBACK = "CLKFBOUT";
    parameter CLKIN1_PERIOD = "0";
    parameter CLKIN2_PERIOD = "0";
    parameter CLKOUT0_DESKEW_ADJUST = "NONE";
    parameter CLKOUT1_DESKEW_ADJUST = "NONE";
    parameter CLKOUT2_DESKEW_ADJUST = "NONE";
    parameter CLKOUT3_DESKEW_ADJUST = "NONE";
    parameter CLKOUT4_DESKEW_ADJUST = "NONE";
    parameter CLKOUT5_DESKEW_ADJUST = "NONE";
    parameter integer CLKOUT0_DIVIDE = 1;
    parameter integer CLKOUT1_DIVIDE = 1;
    parameter integer CLKOUT2_DIVIDE = 1;
    parameter integer CLKOUT3_DIVIDE = 1;
    parameter integer CLKOUT4_DIVIDE = 1;
    parameter integer CLKOUT5_DIVIDE = 1;
    parameter real CLKOUT0_DUTY_CYCLE = 0.50;
    parameter real CLKOUT1_DUTY_CYCLE = 0.50;
    parameter real CLKOUT2_DUTY_CYCLE = 0.50;
    parameter real CLKOUT3_DUTY_CYCLE = 0.50;
    parameter real CLKOUT4_DUTY_CYCLE = 0.50;
    parameter real CLKOUT5_DUTY_CYCLE = 0.50;
    parameter real CLKOUT0_PHASE = 0.0;
    parameter real CLKOUT1_PHASE = 0.0;
    parameter real CLKOUT2_PHASE = 0.0;
    parameter real CLKOUT3_PHASE = 0.0;
    parameter real CLKOUT4_PHASE = 0.0;
    parameter real CLKOUT5_PHASE = 0.0;
    parameter COMPENSATION = "SYSTEM_SYNCHRONOUS";
    parameter integer DIVCLK_DIVIDE = 1;
    parameter EN_REL = "FALSE";
    parameter PLL_PMCD_MODE = "FALSE";
    parameter real REF_JITTER = 0.100;
    parameter RESET_ON_LOSS_OF_LOCK = "FALSE";
    parameter RST_DEASSERT_CLK = "CLKIN1";
    parameter SIM_DEVICE = "SPARTAN6";
    output CLKFBDCM;
    input CLKFBIN;
    output CLKFBOUT;
    input CLKINSEL;
    input CLKIN1;
    input CLKIN2;
    output CLKOUTDCM0;
    output CLKOUTDCM1;
    output CLKOUTDCM2;
    output CLKOUTDCM3;
    output CLKOUTDCM4;
    output CLKOUTDCM5;
    output CLKOUT0;
    output CLKOUT1;
    output CLKOUT2;
    output CLKOUT3;
    output CLKOUT4;
    output CLKOUT5;
    input [4:0] DADDR;
    input DCLK;
    input DEN;
    input [15:0] DI;
    output [15:0] DO;
    output DRDY;
    input DWE;
    output LOCKED;
    input REL;
    input RST;
endmodule

module BUFIO2 (...);
    output DIVCLK;
    input I;
    output IOCLK;
    output SERDESSTROBE;
endmodule


