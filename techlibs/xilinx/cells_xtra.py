#!/usr/bin/env python3

from argparse import ArgumentParser
from io import StringIO
from enum import Enum, auto
import os.path
import sys
import re


class Cell:
    def __init__(self, name, keep=False, port_attrs={}):
        self.name = name
        self.keep = keep
        self.port_attrs = port_attrs


XC6S_CELLS = [
    # Design elements types listed in Xilinx UG615.

    # Advanced.
    Cell('MCB'),
    Cell('PCIE_A1'),

    # Arithmetic functions.
    Cell('DSP48A1', port_attrs={'CLK': ['clkbuf_sink']}),

    # Clock components.
    # Cell('BUFG', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE_1', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_1', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFH', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFIO2', port_attrs={'IOCLK': ['clkbuf_driver'], 'DIVCLK': ['clkbuf_driver']}),
    Cell('BUFIO2_2CLK', port_attrs={'IOCLK': ['clkbuf_driver'], 'DIVCLK': ['clkbuf_driver']}),
    Cell('BUFIO2FB', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFPLL_MCB', port_attrs={'IOCLK0': ['clkbuf_driver'], 'IOCLK1': ['clkbuf_driver']}),
    Cell('DCM_CLKGEN'),
    Cell('DCM_SP'),
    Cell('PLL_BASE'),

    # Config/BSCAN components.
    Cell('BSCAN_SPARTAN6', keep=True),
    Cell('DNA_PORT'),
    Cell('ICAP_SPARTAN6', keep=True),
    Cell('POST_CRC_INTERNAL'),
    Cell('STARTUP_SPARTAN6', keep=True),
    Cell('SUSPEND_SYNC', keep=True),

    # I/O components.
    Cell('GTPA1_DUAL'),
    # Cell('IBUF', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFDS', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFG', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFGDS', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFGDS_DIFF_OUT', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IOBUF', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFDS', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IODELAY2', port_attrs={'IOCLK0': ['clkbuf_sink'], 'IOCLK1': ['clkbuf_sink'], 'CLK': ['clkbuf_sink']}),
    Cell('IODRP2', port_attrs={'IOCLK0': ['clkbuf_sink'], 'IOCLK1': ['clkbuf_sink'], 'CLK': ['clkbuf_sink']}),
    Cell('IODRP2_MCB', port_attrs={'IOCLK0': ['clkbuf_sink'], 'IOCLK1': ['clkbuf_sink'], 'CLK': ['clkbuf_sink']}),
    Cell('ISERDES2', port_attrs={
        'CLK0': ['clkbuf_sink'],
        'CLK1': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),
    Cell('KEEPER'),
    # Cell('OBUF', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFT', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFTDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OSERDES2', port_attrs={
        'CLK0': ['clkbuf_sink'],
        'CLK1': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),
    Cell('PULLDOWN'),
    Cell('PULLUP'),

    # RAM/ROM.
    #Cell('RAM128X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    # NOTE: not in the official library guide!
    Cell('RAM128X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM256X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32M', port_attrs={'WCLK': ['clkbuf_sink']}),
    #Cell('RAM32X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64M', port_attrs={'WCLK': ['clkbuf_sink']}),
    #Cell('RAM64X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # NOTE: not in the official library guide!
    Cell('RAM64X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAMB8BWER', port_attrs={'CLKAWRCLK': ['clkbuf_sink'], 'CLKBRDCLK': ['clkbuf_sink']}),
    # Cell('RAMB16BWER', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('ROM128X1'),
    Cell('ROM256X1'),
    Cell('ROM32X1'),
    Cell('ROM64X1'),

    # Registers/latches.
    # Cell('FDCE'),
    # Cell('FDPE'),
    # Cell('FDRE'),
    # Cell('FDSE'),
    Cell('IDDR2', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink']}),
    Cell('LDCE'),
    Cell('LDPE'),
    Cell('ODDR2', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink']}),

    # Slice/CLB primitives.
    # Cell('CARRY4'),
    Cell('CFGLUT5', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('LUT1'),
    # Cell('LUT2'),
    # Cell('LUT3'),
    # Cell('LUT4'),
    # Cell('LUT5'),
    # Cell('LUT6'),
    # Cell('LUT6_2'),
    # Cell('MUXF7'),
    # Cell('MUXF8'),
    # Cell('SRL16E', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('SRLC32E', port_attrs={'CLK': ['clkbuf_sink']}),
]


XC6V_CELLS = [
    # Design elements types listed in Xilinx UG623.

    # Advanced.
    Cell('PCIE_2_0'),
    Cell('SYSMON'),

    # Arithmetic functions.
    Cell('DSP48E1', port_attrs={'CLK': ['clkbuf_sink']}),

    # Clock components.
    # Cell('BUFG', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE_1', port_attrs={'O': ['clkbuf_driver']}),
    #Cell('BUFGCTRL', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_1', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_CTRL', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFH', port_attrs={'O': ['clkbuf_driver']}),
    #Cell('BUFHCE', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFIO', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFIODQS', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFR', port_attrs={'O': ['clkbuf_driver']}),
    Cell('IBUFDS_GTXE1', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('MMCM_ADV'),
    Cell('MMCM_BASE'),

    # Config/BSCAN components.
    Cell('BSCAN_VIRTEX6', keep=True),
    Cell('CAPTURE_VIRTEX6', keep=True),
    Cell('DNA_PORT'),
    Cell('EFUSE_USR'),
    Cell('FRAME_ECC_VIRTEX6'),
    Cell('ICAP_VIRTEX6', keep=True),
    Cell('STARTUP_VIRTEX6', keep=True),
    Cell('USR_ACCESS_VIRTEX6'),

    # I/O components.
    Cell('DCIRESET', keep=True),
    Cell('GTHE1_QUAD'),
    Cell('GTXE1'),
    # Cell('IBUF', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFDS', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_GTHE1', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFG', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFGDS', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFGDS_DIFF_OUT', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IDELAYCTRL', keep=True, port_attrs={'REFCLK': ['clkbuf_sink']}),
    Cell('IOBUF', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFDS', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IODELAYE1', port_attrs={'C': ['clkbuf_sink']}),
    Cell('ISERDESE1', port_attrs={
        'CLK': ['clkbuf_sink'],
        'CLKB': ['clkbuf_sink'],
        'OCLK': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),
    Cell('KEEPER'),
    # Cell('OBUF', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFT', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFTDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OSERDESE1', port_attrs={'CLK': ['clkbuf_sink'], 'CLKDIV': ['clkbuf_sink']}),
    Cell('PULLDOWN'),
    Cell('PULLUP'),
    Cell('TEMAC_SINGLE'),

    # RAM/ROM.
    Cell('FIFO18E1', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FIFO36E1', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    #Cell('RAM128X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM128X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM256X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32M', port_attrs={'WCLK': ['clkbuf_sink']}),
    #Cell('RAM32X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64M', port_attrs={'WCLK': ['clkbuf_sink']}),
    #Cell('RAM64X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # NOTE: not in the official library guide!
    Cell('RAM64X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAMB18E1', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),
    # Cell('RAMB36E1', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),
    Cell('ROM128X1'),
    Cell('ROM256X1'),
    Cell('ROM32X1'),
    Cell('ROM64X1'),

    # Registers/latches.
    # Cell('FDCE'),
    # Cell('FDPE'),
    # Cell('FDRE'),
    # Cell('FDSE'),
    Cell('IDDR', port_attrs={'C': ['clkbuf_sink']}),
    Cell('IDDR_2CLK', port_attrs={'C': ['clkbuf_sink'], 'CB': ['clkbuf_sink']}),
    Cell('LDCE'),
    Cell('LDPE'),
    Cell('ODDR', port_attrs={'C': ['clkbuf_sink']}),

    # Slice/CLB primitives.
    # Cell('CARRY4'),
    Cell('CFGLUT5', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('LUT1'),
    # Cell('LUT2'),
    # Cell('LUT3'),
    # Cell('LUT4'),
    # Cell('LUT5'),
    # Cell('LUT6'),
    # Cell('LUT6_2'),
    # Cell('MUXF7'),
    # Cell('MUXF8'),
    # Cell('SRL16E', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('SRLC32E', port_attrs={'CLK': ['clkbuf_sink']}),
]


XC7_CELLS = [
    # Design elements types listed in Xilinx UG953.

    # Advanced.
    Cell('GTHE2_CHANNEL'),
    Cell('GTHE2_COMMON'),
    Cell('GTPE2_CHANNEL'),
    Cell('GTPE2_COMMON'),
    Cell('GTXE2_CHANNEL'),
    Cell('GTXE2_COMMON'),
    Cell('PCIE_2_1'),
    Cell('PCIE_3_0'),
    Cell('XADC'),

    # Arithmetic functions.
    Cell('DSP48E1', port_attrs={'CLK': ['clkbuf_sink']}),

    # Clock components.
    # Cell('BUFG', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE_1', port_attrs={'O': ['clkbuf_driver']}),
    #Cell('BUFGCTRL', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_1', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_CTRL', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFH', port_attrs={'O': ['clkbuf_driver']}),
    #Cell('BUFHCE', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFIO', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFMR', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFMRCE', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFR', port_attrs={'O': ['clkbuf_driver']}),
    Cell('MMCME2_ADV'),
    Cell('MMCME2_BASE'),
    Cell('PLLE2_ADV'),
    Cell('PLLE2_BASE'),

    # Config/BSCAN components.
    Cell('BSCANE2', keep=True),
    Cell('CAPTUREE2', keep=True),
    Cell('DNA_PORT'),
    Cell('EFUSE_USR'),
    Cell('FRAME_ECCE2'),
    Cell('ICAPE2', keep=True),
    Cell('STARTUPE2', keep=True),
    Cell('USR_ACCESSE2'),

    # I/O components.
    Cell('DCIRESET', keep=True),
    # Cell('IBUF', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUF_IBUFDISABLE', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUF_INTERMDISABLE', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFDS', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT_IBUFDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT_INTERMDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_GTE2', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_IBUFDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_INTERMDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFG', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFGDS', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFGDS_DIFF_OUT', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IDELAYCTRL', keep=True, port_attrs={'REFCLK': ['clkbuf_sink']}),
    Cell('IDELAYE2', port_attrs={'C': ['clkbuf_sink']}),
    Cell('IN_FIFO', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('IOBUF', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUF_DCIEN', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUF_INTERMDISABLE', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFDS', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFDS_DCIEN', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_DIFF_OUT', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_DIFF_OUT_DCIEN', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_DIFF_OUT_INTERMDISABLE', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_INTERMDISABLE', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('ISERDESE2', port_attrs={
        'CLK': ['clkbuf_sink'],
        'CLKB': ['clkbuf_sink'],
        'OCLK': ['clkbuf_sink'],
        'OCLKB': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
        'CLKDIVP': ['clkbuf_sink'],
    }),
    Cell('KEEPER'),
    # Cell('OBUF', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFT', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFTDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('ODELAYE2', port_attrs={'C': ['clkbuf_sink']}),
    Cell('OSERDESE2', port_attrs={'CLK': ['clkbuf_sink'], 'CLKDIV': ['clkbuf_sink']}),
    Cell('OUT_FIFO', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('PHASER_IN'),
    Cell('PHASER_IN_PHY'),
    Cell('PHASER_OUT'),
    Cell('PHASER_OUT_PHY'),
    Cell('PHASER_REF'),
    Cell('PHY_CONTROL'),
    Cell('PULLDOWN'),
    Cell('PULLUP'),

    # RAM/ROM.
    Cell('FIFO18E1', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FIFO36E1', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    #Cell('RAM128X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM128X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM256X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32M', port_attrs={'WCLK': ['clkbuf_sink']}),
    #Cell('RAM32X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64M', port_attrs={'WCLK': ['clkbuf_sink']}),
    #Cell('RAM64X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # NOTE: not in the official library guide!
    Cell('RAM64X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAMB18E1', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),
    # Cell('RAMB36E1', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),
    Cell('ROM128X1'),
    Cell('ROM256X1'),
    Cell('ROM32X1'),
    Cell('ROM64X1'),

    # Registers/latches.
    # Cell('FDCE'),
    # Cell('FDPE'),
    # Cell('FDRE'),
    # Cell('FDSE'),
    Cell('IDDR', port_attrs={'C': ['clkbuf_sink']}),
    Cell('IDDR_2CLK', port_attrs={'C': ['clkbuf_sink'], 'CB': ['clkbuf_sink']}),
    Cell('LDCE'),
    Cell('LDPE'),
    Cell('ODDR', port_attrs={'C': ['clkbuf_sink']}),

    # Slice/CLB primitives.
    # Cell('CARRY4'),
    Cell('CFGLUT5', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('LUT1'),
    # Cell('LUT2'),
    # Cell('LUT3'),
    # Cell('LUT4'),
    # Cell('LUT5'),
    # Cell('LUT6'),
    # Cell('LUT6_2'),
    # Cell('MUXF7'),
    # Cell('MUXF8'),
    # Cell('SRL16E', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('SRLC32E', port_attrs={'CLK': ['clkbuf_sink']}),

    # NOTE: not in the official library guide!
    Cell('PS7', keep=True),
]


XCU_CELLS = [
    # Design elements types listed in Xilinx UG974.

    # Advanced.
    Cell('CMAC'),
    Cell('CMACE4'),
    Cell('GTHE3_CHANNEL'),
    Cell('GTHE3_COMMON'),
    Cell('GTHE4_CHANNEL'),
    Cell('GTHE4_COMMON'),
    Cell('GTYE3_CHANNEL'),
    Cell('GTYE3_COMMON'),
    Cell('GTYE4_CHANNEL'),
    Cell('GTYE4_COMMON'),
    Cell('IBUFDS_GTE3', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_GTE4', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('ILKN'),
    Cell('ILKNE4'),
    Cell('OBUFDS_GTE3', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFDS_GTE3_ADV', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFDS_GTE4', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFDS_GTE4_ADV', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('PCIE40E4'),
    Cell('PCIE_3_1'),
    Cell('SYSMONE1'),
    Cell('SYSMONE4'),

    # Arithmetic functions.
    Cell('DSP48E2', port_attrs={'CLK': ['clkbuf_sink']}),

    # Blockram.
    Cell('FIFO18E2', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FIFO36E2', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('RAMB18E2', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),
    Cell('RAMB36E2', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),
    Cell('URAM288', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('URAM288_BASE', port_attrs={'CLK': ['clkbuf_sink']}),

    # CLB.
    # Cell('LUT6_2'),
    #Cell('RAM128X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM128X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM256X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM256X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32M', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32M16', port_attrs={'WCLK': ['clkbuf_sink']}),
    #Cell('RAM32X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM32X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM512X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64M', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64M8', port_attrs={'WCLK': ['clkbuf_sink']}),
    #Cell('RAM64X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('RAM64X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    Cell('AND2B1L'),
    Cell('CARRY8'),
    Cell('CFGLUT5', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('LUT1'),
    # Cell('LUT2'),
    # Cell('LUT3'),
    # Cell('LUT4'),
    # Cell('LUT5'),
    # Cell('LUT6'),
    # Cell('MUXF7'),
    # Cell('MUXF8'),
    Cell('MUXF9'),
    Cell('OR2L'),
    # Cell('SRL16E', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('SRLC32E', port_attrs={'CLK': ['clkbuf_sink']}),

    # Clock.
    # Cell('BUFG', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFG_GT', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFG_GT_SYNC'),
    Cell('BUFG_PS', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE_1', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE_DIV', port_attrs={'O': ['clkbuf_driver']}),
    #Cell('BUFGCTRL', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_1', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_CTRL', port_attrs={'O': ['clkbuf_driver']}),
    Cell('MMCME3_ADV'),
    Cell('MMCME3_BASE'),
    Cell('MMCME4_ADV'),
    Cell('MMCME4_BASE'),
    Cell('PLLE3_ADV'),
    Cell('PLLE3_BASE'),
    Cell('PLLE4_ADV'),
    Cell('PLLE4_BASE'),

    # Configuration.
    Cell('BSCANE2', keep=True),
    Cell('DNA_PORTE2'),
    Cell('EFUSE_USR'),
    Cell('FRAME_ECCE3'),
    Cell('ICAPE3', keep=True),
    Cell('MASTER_JTAG', keep=True),
    Cell('STARTUPE3', keep=True),
    Cell('USR_ACCESSE2'),

    # I/O.
    Cell('BITSLICE_CONTROL', keep=True),
    Cell('DCIRESET', keep=True),
    Cell('HPIO_VREF'),
    # XXX
    # Cell('IBUF', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUF_ANALOG', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUF_IBUFDISABLE', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUF_INTERMDISABLE', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFDS', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT_IBUFDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT_INTERMDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DPHY', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_IBUFDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_INTERMDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDSE3', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFE3', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IDELAYCTRL', keep=True, port_attrs={'REFCLK': ['clkbuf_sink']}),
    Cell('IDELAYE3', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('IOBUF', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUF_DCIEN', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUF_INTERMDISABLE', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFDS', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFDS_DCIEN', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_DIFF_OUT', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_DIFF_OUT_DCIEN', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_DIFF_OUT_INTERMDISABLE', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_INTERMDISABLE', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDSE3', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFE3', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('ISERDESE3', port_attrs={
        'CLK': ['clkbuf_sink'],
        'CLK_B': ['clkbuf_sink'],
        'FIFO_RD_CLK': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),
    Cell('KEEPER'),
    # Cell('OBUF', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFDS_DPHY', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFT', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFTDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('ODELAYE3', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('OSERDESE3', port_attrs={'CLK': ['clkbuf_sink'], 'CLKDIV': ['clkbuf_sink']}),
    Cell('PULLDOWN'),
    Cell('PULLUP'),
    Cell('RIU_OR'),
    Cell('RX_BITSLICE'),
    Cell('RXTX_BITSLICE'),
    Cell('TX_BITSLICE'),
    Cell('TX_BITSLICE_TRI'),

    # Registers.
    # Cell('FDCE'),
    # Cell('FDPE'),
    # Cell('FDRE'),
    # Cell('FDSE'),
    Cell('HARD_SYNC', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('IDDRE1', port_attrs={'C': ['clkbuf_sink'], 'CB': ['clkbuf_sink']}),
    Cell('LDCE'),
    Cell('LDPE'),
    Cell('ODDRE1', port_attrs={'C': ['clkbuf_sink']}),

    # NOTE: not in the official library guide!
    Cell('PS8', keep=True),
]


class State(Enum):
    OUTSIDE = auto()
    IN_MODULE = auto()
    IN_OTHER_MODULE = auto()
    IN_FUNCTION = auto()
    IN_TASK = auto()

def xtract_cell_decl(cell, dirs, outf):
    for dir in dirs:
        fname = os.path.join(dir, cell.name + '.v')
        try:
            with open(fname) as f:
                state = State.OUTSIDE
                found = False
                # Probably the most horrible Verilog "parser" ever written.
                module_ports = []
                invertible_ports = set()
                for l in f:
                    l = l.partition('//')[0]
                    l = l.strip()
                    if l == 'module {}'.format(cell.name) or l.startswith('module {} '.format(cell.name)):
                        if found:
                            print('Multiple modules in {}.'.format(fname))
                            sys.exit(1)
                        elif state != State.OUTSIDE:
                            print('Nested modules in {}.'.format(fname))
                            sys.exit(1)
                        found = True
                        state = State.IN_MODULE
                        if cell.keep:
                            outf.write('(* keep *)\n')
                        outf.write('module {} (...);\n'.format(cell.name))
                    elif l.startswith('module '):
                        if state != State.OUTSIDE:
                            print('Nested modules in {}.'.format(fname))
                            sys.exit(1)
                        state = State.IN_OTHER_MODULE
                    elif l.startswith('task '):
                        if state == State.IN_MODULE:
                            state = State.IN_TASK
                    elif l.startswith('function '):
                        if state == State.IN_MODULE:
                            state = State.IN_FUNCTION
                    elif l == 'endtask':
                        if state == State.IN_TASK:
                            state = State.IN_MODULE
                    elif l == 'endfunction':
                        if state == State.IN_FUNCTION:
                            state = State.IN_MODULE
                    elif l == 'endmodule':
                        if state == State.IN_MODULE:
                            for kind, rng, port in module_ports:
                                for attr in cell.port_attrs.get(port, []):
                                    outf.write('    (* {} *)\n'.format(attr))
                                if port in invertible_ports:
                                    outf.write('    (* invertible_pin = "IS_{}_INVERTED" *)\n'.format(port))
                                if rng is None:
                                    outf.write('    {} {};\n'.format(kind, port))
                                else:
                                    outf.write('    {} {} {};\n'.format(kind, rng, port))
                            outf.write(l + '\n')
                            outf.write('\n')
                        elif state != State.IN_OTHER_MODULE:
                            print('endmodule in weird place in {}.'.format(cell.name, fname))
                            sys.exit(1)
                        state = State.OUTSIDE
                    elif l.startswith(('input ', 'output ', 'inout ')) and state == State.IN_MODULE:
                        if l.endswith((';', ',')):
                            l = l[:-1]
                        if ';' in l:
                            print('Weird port line in {} [{}].'.format(fname, l))
                            sys.exit(1)
                        kind, _, ports = l.partition(' ')
                        for port in ports.split(','):
                            port = port.strip()
                            if port.startswith('['):
                                rng, port = port.split()
                            else:
                                rng = None
                            module_ports.append((kind, rng, port))
                    elif l.startswith('parameter ') and state == State.IN_MODULE:
                        if 'UNPLACED' in l:
                            continue
                        if l.endswith((';', ',')):
                            l = l[:-1]
                        while '  ' in l:
                            l = l.replace('  ', ' ')
                        if ';' in l:
                            print('Weird parameter line in {} [{}].'.format(fname, l))
                            sys.exit(1)
                        outf.write('    {};\n'.format(l))
                        match = re.search('IS_([a-zA-Z0-9_]+)_INVERTED', l)
                        if match:
                            invertible_ports.add(match[1])
                if state != State.OUTSIDE:
                    print('endmodule not found in {}.'.format(fname))
                    sys.exit(1)
                if not found:
                    print('Cannot find module {} in {}.'.format(cell.name, fname))
                    sys.exit(1)
            return
        except FileNotFoundError:
            continue
    print('Cannot find {}.'.format(cell.name))
    sys.exit(1)

if __name__ == '__main__':
    parser = ArgumentParser(description='Extract Xilinx blackbox cell definitions from ISE and Vivado.')
    parser.add_argument('vivado_dir', nargs='?', default='/opt/Xilinx/Vivado/2018.1')
    parser.add_argument('ise_dir', nargs='?', default='/opt/Xilinx/ISE/14.7')
    args = parser.parse_args()

    dirs = [
        os.path.join(args.vivado_dir, 'data/verilog/src/xeclib'),
        os.path.join(args.vivado_dir, 'data/verilog/src/retarget'),
        os.path.join(args.ise_dir, 'ISE_DS/ISE/verilog/xeclib/unisims'),
    ]
    for dir in dirs:
        if not os.path.isdir(dir):
            print('{} is not a directory'.format(dir))

    for ofile, cells in [
        ('xc6s_cells_xtra.v', XC6S_CELLS),
        ('xc6v_cells_xtra.v', XC6V_CELLS),
        ('xc7_cells_xtra.v', XC7_CELLS),
        ('xcu_cells_xtra.v', XCU_CELLS),
    ]:
        out = StringIO()
        for cell in cells:
            xtract_cell_decl(cell, dirs, out)

        with open(ofile, 'w') as f:
            f.write('// Created by cells_xtra.py from Xilinx models\n')
            f.write('\n')
            f.write(out.getvalue())
