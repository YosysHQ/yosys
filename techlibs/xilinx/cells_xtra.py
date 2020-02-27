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


CELLS = [
    # Design element types listed in:
    # - UG607 (Spartan 3)
    # - UG613 (Spartan 3A)
    # - UG617 (Spartan 3E)
    # - UG615 (Spartan 6)
    # - UG619 (Virtex 4)
    # - UG621 (Virtex 5)
    # - UG623 (Virtex 6)
    # - UG953 (Series 7)
    # - UG974 (Ultrascale)

    # CLB -- RAM/ROM.
    # Cell('RAM16X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM16X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM32X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM32X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM64X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM64X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM128X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM128X1S_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM256X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM512X1S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM16X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM32X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM64X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM16X4S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM32X4S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM16X8S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM32X8S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM16X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM16X1D_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM32X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM32X1D_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM64X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM64X1D_1', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM128X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM256X1D', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM32M', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM32M16', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM64M', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAM64M8', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('ROM16X1'),
    # Cell('ROM32X1'),
    # Cell('ROM64X1'),
    # Cell('ROM128X1'),
    # Cell('ROM256X1'),

    # CLB -- registers/latches.
    # Virtex 1/2/4/5, Spartan 3.
    # Cell('FDCPE', port_attrs={'C': ['clkbuf_sink']}),
    # Cell('FDRSE', port_attrs={'C': ['clkbuf_sink']}),
    # Cell('LDCPE', port_attrs={'C': ['clkbuf_sink']}),
    # Virtex 6, Spartan 6, Series 7, Ultrascale.
    # Cell('FDCE'),
    # Cell('FDPE'),
    # Cell('FDRE'),
    # Cell('FDSE'),
    # Cell('LDCE'),
    # Cell('LDPE'),
    # Cell('AND2B1L'),
    # Cell('OR2L'),

    # CLB -- other.
    # Cell('LUT1'),
    # Cell('LUT2'),
    # Cell('LUT3'),
    # Cell('LUT4'),
    # Cell('LUT5'),
    # Cell('LUT6'),
    # Cell('LUT6_2'),
    # Cell('MUXF5'),
    # Cell('MUXF6'),
    # Cell('MUXF7'),
    # Cell('MUXF8'),
    # Cell('MUXF9'),
    # Cell('CARRY4'),
    # Cell('CARRY8'),
    # Cell('MUXCY'),
    # Cell('XORCY'),
    # Cell('ORCY'),
    # Cell('MULT_AND'),
    # Cell('SRL16', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('SRL16E', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('SRLC16', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('SRLC16E', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('SRLC32E', port_attrs={'CLK': ['clkbuf_sink']}),
    # Cell('CFGLUT5', port_attrs={'CLK': ['clkbuf_sink']}),

    # Block RAM.
    # Virtex.
    # TODO: RAMB4_*
    # Virtex 2, Spartan 3.
    Cell('RAMB16_S1', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('RAMB16_S2', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('RAMB16_S4', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('RAMB16_S9', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('RAMB16_S18', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('RAMB16_S36', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('RAMB16_S1_S1', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S1_S2', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S1_S4', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S1_S9', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S1_S18', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S1_S36', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S2_S2', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S2_S4', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S2_S9', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S2_S18', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S2_S36', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S4_S4', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S4_S9', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S4_S18', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S4_S36', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S9_S9', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S9_S18', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S9_S36', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S18_S18', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S18_S36', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16_S36_S36', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    # Spartan 3A (in addition to above).
    Cell('RAMB16BWE_S18', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('RAMB16BWE_S36', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('RAMB16BWE_S18_S9', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16BWE_S18_S18', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16BWE_S36_S9', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16BWE_S36_S18', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB16BWE_S36_S36', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    # Spartan 3A DSP.
    Cell('RAMB16BWER', port_attrs={ 'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    # Spartan 6 (in addition to above).
    Cell('RAMB8BWER', port_attrs={ 'CLKAWRCLK': ['clkbuf_sink'], 'CLKBRDCLK': ['clkbuf_sink']}),
    # Virtex 4.
    Cell('FIFO16', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('RAMB16', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB32_S64_ECC', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    # Virtex 5.
    Cell('FIFO18', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FIFO18_36', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FIFO36', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FIFO36_72', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('RAMB18', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB36', port_attrs={'CLKA': ['clkbuf_sink'], 'CLKB': ['clkbuf_sink']}),
    Cell('RAMB18SDP', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('RAMB36SDP', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    # Virtex 6 / Series 7.
    Cell('FIFO18E1', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FIFO36E1', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    #Cell('RAMB18E1', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']]}),
    #Cell('RAMB36E1', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']]}),
    # Ultrascale.
    Cell('FIFO18E2', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FIFO36E2', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('RAMB18E2', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),
    Cell('RAMB36E2', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),

    # Ultra RAM.
    Cell('URAM288', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('URAM288_BASE', port_attrs={'CLK': ['clkbuf_sink']}),

    # Multipliers and DSP.
    # Cell('MULT18X18'), # Virtex 2, Spartan 3
    # Cell('MULT18X18S', port_attrs={'C': ['clkbuf_sink']}), # Spartan 3
    # Cell('MULT18X18SIO', port_attrs={'CLK': ['clkbuf_sink']}), # Spartan 3E
    # Cell('DSP48A', port_attrs={'CLK': ['clkbuf_sink']}), # Spartan 3A DSP
    # Cell('DSP48A1', port_attrs={'CLK': ['clkbuf_sink']}), # Spartan 6
    # Cell('DSP48', port_attrs={'CLK': ['clkbuf_sink']}), # Virtex 4
    Cell('DSP48E', port_attrs={'CLK': ['clkbuf_sink']}), # Virtex 5
    #Cell('DSP48E1', port_attrs={'CLK': ['clkbuf_sink']}), # Virtex 6 / Series 7
    Cell('DSP48E2', port_attrs={'CLK': ['clkbuf_sink']}), # Ultrascale

    # I/O logic.
    # Virtex 2, Spartan 3.
    Cell('IFDDRCPE', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink'], 'D': ['iopad_external_pin']}),
    Cell('IFDDRRSE', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink'], 'D': ['iopad_external_pin']}),
    Cell('OFDDRCPE', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink'], 'Q': ['iopad_external_pin']}),
    Cell('OFDDRRSE', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink'], 'Q': ['iopad_external_pin']}),
    Cell('OFDDRTCPE', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink'], 'O': ['iopad_external_pin']}),
    Cell('OFDDRTRSE', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink'], 'O': ['iopad_external_pin']}),
    # Spartan 3E.
    Cell('IDDR2', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink']}),
    Cell('ODDR2', port_attrs={'C0': ['clkbuf_sink'], 'C1': ['clkbuf_sink']}),
    # Virtex 4.
    Cell('IDDR', port_attrs={'C': ['clkbuf_sink']}),
    Cell('IDDR_2CLK', port_attrs={'C': ['clkbuf_sink'], 'CB': ['clkbuf_sink']}),
    Cell('ODDR', port_attrs={'C': ['clkbuf_sink']}),
    Cell('IDELAYCTRL', keep=True, port_attrs={'REFCLK': ['clkbuf_sink']}),
    Cell('IDELAY', port_attrs={'C': ['clkbuf_sink']}),
    Cell('ISERDES', port_attrs={
        'CLK': ['clkbuf_sink'],
        'OCLK': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),
    Cell('OSERDES', port_attrs={'CLK': ['clkbuf_sink'], 'CLKDIV': ['clkbuf_sink']}),
    # Virtex 5.
    Cell('IODELAY', port_attrs={'C': ['clkbuf_sink']}),
    Cell('ISERDES_NODELAY', port_attrs={
        'CLK': ['clkbuf_sink'],
        'CLKB': ['clkbuf_sink'],
        'OCLK': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),
    # Virtex 6.
    Cell('IODELAYE1', port_attrs={'C': ['clkbuf_sink']}),
    Cell('ISERDESE1', port_attrs={
        'CLK': ['clkbuf_sink'],
        'CLKB': ['clkbuf_sink'],
        'OCLK': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),
    Cell('OSERDESE1', port_attrs={'CLK': ['clkbuf_sink'], 'CLKDIV': ['clkbuf_sink']}),
    # Series 7.
    Cell('IDELAYE2', port_attrs={'C': ['clkbuf_sink']}),
    Cell('ODELAYE2', port_attrs={'C': ['clkbuf_sink']}),
    Cell('ISERDESE2', port_attrs={
        'CLK': ['clkbuf_sink'],
        'CLKB': ['clkbuf_sink'],
        'OCLK': ['clkbuf_sink'],
        'OCLKB': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
        'CLKDIVP': ['clkbuf_sink'],
    }),
    Cell('OSERDESE2', port_attrs={'CLK': ['clkbuf_sink'], 'CLKDIV': ['clkbuf_sink']}),
    Cell('PHASER_IN'),
    Cell('PHASER_IN_PHY'),
    Cell('PHASER_OUT'),
    Cell('PHASER_OUT_PHY'),
    Cell('PHASER_REF'),
    Cell('PHY_CONTROL'),
    # Ultrascale.
    Cell('IDDRE1', port_attrs={'C': ['clkbuf_sink'], 'CB': ['clkbuf_sink']}),
    Cell('ODDRE1', port_attrs={'C': ['clkbuf_sink']}),
    Cell('IDELAYE3', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('ODELAYE3', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('ISERDESE3', port_attrs={
        'CLK': ['clkbuf_sink'],
        'CLK_B': ['clkbuf_sink'],
        'FIFO_RD_CLK': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),
    Cell('OSERDESE3', port_attrs={'CLK': ['clkbuf_sink'], 'CLKDIV': ['clkbuf_sink']}),
    Cell('BITSLICE_CONTROL', keep=True),
    Cell('RIU_OR'),
    Cell('RX_BITSLICE'),
    Cell('RXTX_BITSLICE'),
    Cell('TX_BITSLICE'),
    Cell('TX_BITSLICE_TRI'),
    # Spartan 6.
    Cell('IODELAY2', port_attrs={'IOCLK0': ['clkbuf_sink'], 'IOCLK1': ['clkbuf_sink'], 'CLK': ['clkbuf_sink']}),
    Cell('IODRP2', port_attrs={'IOCLK0': ['clkbuf_sink'], 'IOCLK1': ['clkbuf_sink'], 'CLK': ['clkbuf_sink']}),
    Cell('IODRP2_MCB', port_attrs={'IOCLK0': ['clkbuf_sink'], 'IOCLK1': ['clkbuf_sink'], 'CLK': ['clkbuf_sink']}),
    Cell('ISERDES2', port_attrs={
        'CLK0': ['clkbuf_sink'],
        'CLK1': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),
    Cell('OSERDES2', port_attrs={
        'CLK0': ['clkbuf_sink'],
        'CLK1': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
    }),

    # I/O buffers.
    # Input.
    # Cell('IBUF', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUF_DLY_ADJ', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUF_IBUFDISABLE', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUF_INTERMDISABLE', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUF_ANALOG', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFE3', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFDS', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DLY_ADJ', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_IBUFDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_INTERMDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT_IBUFDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DIFF_OUT_INTERMDISABLE', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDSE3', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_DPHY', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    # Cell('IBUFG', port_attrs={'I': ['iopad_external_pin']}),
    Cell('IBUFGDS', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFGDS_DIFF_OUT', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    # I/O.
    # Cell('IOBUF', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUF_DCIEN', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUF_INTERMDISABLE', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFE3', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFDS', port_attrs={'IO': ['iopad_external_pin']}),
    Cell('IOBUFDS_DCIEN', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_INTERMDISABLE', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_DIFF_OUT', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_DIFF_OUT_DCIEN', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDS_DIFF_OUT_INTERMDISABLE', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    Cell('IOBUFDSE3', port_attrs={'IO': ['iopad_external_pin'], 'IOB': ['iopad_external_pin']}),
    # Output.
    # Cell('OBUF', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFDS_DPHY', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    # Output + tristate.
    # Cell('OBUFT', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFTDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    # Pulls.
    Cell('KEEPER'),
    Cell('PULLDOWN'),
    Cell('PULLUP'),
    # Misc.
    Cell('DCIRESET', keep=True),
    Cell('HPIO_VREF'), # Ultrascale

    # Clock buffers (global).
    # Cell('BUFG', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE_1', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_1', port_attrs={'O': ['clkbuf_driver']}),
    #Cell('BUFGCTRL', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_CTRL', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGMUX_VIRTEX4', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFG_GT', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFG_GT_SYNC'),
    Cell('BUFG_PS', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFGCE_DIV', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFH', port_attrs={'O': ['clkbuf_driver']}),
    #Cell('BUFHCE', port_attrs={'O': ['clkbuf_driver']}),

    # Clock buffers (IO) -- Spartan 6.
    Cell('BUFIO2', port_attrs={'IOCLK': ['clkbuf_driver'], 'DIVCLK': ['clkbuf_driver']}),
    Cell('BUFIO2_2CLK', port_attrs={'IOCLK': ['clkbuf_driver'], 'DIVCLK': ['clkbuf_driver']}),
    Cell('BUFIO2FB', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFPLL', port_attrs={'IOCLK': ['clkbuf_driver']}),
    Cell('BUFPLL_MCB', port_attrs={'IOCLK0': ['clkbuf_driver'], 'IOCLK1': ['clkbuf_driver']}),

    # Clock buffers (IO and regional) -- Virtex.
    Cell('BUFIO', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFIODQS', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFR', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFMR', port_attrs={'O': ['clkbuf_driver']}),
    Cell('BUFMRCE', port_attrs={'O': ['clkbuf_driver']}),

    # Clock components.
    # VIrtex.
    # TODO: CLKDLL
    # TODO: CLKDLLE
    # TODO: CLKDLLHF
    # Virtex 2, Spartan 3.
    Cell('DCM'),
    # Spartan 3E.
    Cell('DCM_SP'),
    # Spartan 6 (also uses DCM_SP and PLL_BASE).
    Cell('DCM_CLKGEN'),
    # Virtex 4/5.
    Cell('DCM_ADV'),
    Cell('DCM_BASE'),
    Cell('DCM_PS'),
    # Virtex 4.
    Cell('PMCD'),
    # Virtex 5.
    Cell('PLL_ADV'),
    Cell('PLL_BASE'),
    # Virtex 6.
    Cell('MMCM_ADV'),
    Cell('MMCM_BASE'),
    # Series 7.
    Cell('MMCME2_ADV'),
    Cell('MMCME2_BASE'),
    Cell('PLLE2_ADV'),
    Cell('PLLE2_BASE'),
    # Ultrascale.
    Cell('MMCME3_ADV'),
    Cell('MMCME3_BASE'),
    Cell('PLLE3_ADV'),
    Cell('PLLE3_BASE'),
    # Ultrascale+.
    Cell('MMCME4_ADV'),
    Cell('MMCME4_BASE'),
    Cell('PLLE4_ADV'),
    Cell('PLLE4_BASE'),

    # Misc stuff.
    Cell('BUFT'),
    # Series 7 I/O FIFOs.
    Cell('IN_FIFO', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('OUT_FIFO', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    # Ultrascale special synchronizer register.
    Cell('HARD_SYNC', port_attrs={'CLK': ['clkbuf_sink']}),

    # Singletons.
    # Startup.
    # TODO: STARTUP_VIRTEX
    # TODO: STARTUP_VIRTEX2
    Cell('STARTUP_SPARTAN3', keep=True),
    Cell('STARTUP_SPARTAN3E', keep=True),
    Cell('STARTUP_SPARTAN3A', keep=True),
    Cell('STARTUP_SPARTAN6', keep=True),
    Cell('STARTUP_VIRTEX4', keep=True),
    Cell('STARTUP_VIRTEX5', keep=True),
    Cell('STARTUP_VIRTEX6', keep=True),
    Cell('STARTUPE2', keep=True), # Series 7
    Cell('STARTUPE3', keep=True), # Ultrascale
    # Capture trigger.
    # TODO: CAPTURE_VIRTEX
    # TODO: CAPTURE_VIRTEX2
    Cell('CAPTURE_SPARTAN3', keep=True),
    Cell('CAPTURE_SPARTAN3A', keep=True),
    Cell('CAPTURE_VIRTEX4', keep=True),
    Cell('CAPTURE_VIRTEX5', keep=True),
    Cell('CAPTURE_VIRTEX6', keep=True),
    Cell('CAPTUREE2', keep=True), # Series 7
    # Internal Configuration Access Port.
    # TODO: ICAP_VIRTEX2
    Cell('ICAP_SPARTAN3A', keep=True),
    Cell('ICAP_SPARTAN6', keep=True),
    Cell('ICAP_VIRTEX4', keep=True),
    Cell('ICAP_VIRTEX5', keep=True),
    Cell('ICAP_VIRTEX6', keep=True),
    Cell('ICAPE2', keep=True), # Series 7
    Cell('ICAPE3', keep=True), # Ultrascale
    # JTAG.
    # TODO: BSCAN_VIRTEX
    # TODO: BSCAN_VIRTEX2
    Cell('BSCAN_SPARTAN3', keep=True),
    Cell('BSCAN_SPARTAN3A', keep=True),
    Cell('BSCAN_SPARTAN6', keep=True),
    Cell('BSCAN_VIRTEX4', keep=True),
    Cell('BSCAN_VIRTEX5', keep=True),
    Cell('BSCAN_VIRTEX6', keep=True),
    Cell('BSCANE2', keep=True), # Series 7, Ultrascale
    # DNA port.
    Cell('DNA_PORT'), # Virtex 5/6, Series 7, Spartan 3A/6
    Cell('DNA_PORTE2'), # Ultrascale
    # Frame ECC.
    Cell('FRAME_ECC_VIRTEX4'),
    Cell('FRAME_ECC_VIRTEX5'),
    Cell('FRAME_ECC_VIRTEX6'),
    Cell('FRAME_ECCE2'), # Series 7
    Cell('FRAME_ECCE3'), # Ultrascale
    # AXSS command access.
    Cell('USR_ACCESS_VIRTEX4'),
    Cell('USR_ACCESS_VIRTEX5'),
    Cell('USR_ACCESS_VIRTEX6'),
    Cell('USR_ACCESSE2'), # Series 7, Ultrascale
    # Misc.
    Cell('POST_CRC_INTERNAL'), # Spartan 6
    Cell('SUSPEND_SYNC', keep=True), # Spartan 6
    Cell('KEY_CLEAR', keep=True), # Virtex 5
    Cell('MASTER_JTAG', keep=True), # Ultrascale
    Cell('SPI_ACCESS', keep=True), # Spartan 3AN
    Cell('EFUSE_USR'),

    # ADC.
    Cell('SYSMON'), # Virtex 5/6
    Cell('XADC'), # Series 7
    Cell('SYSMONE1'), # Ultrascale
    Cell('SYSMONE4'), # Ultrascale+

    # Gigabit transceivers.
    # Spartan 6.
    Cell('GTPA1_DUAL'),
    # Virtex 2 Pro.
    # TODO: GT_*
    # TODO: GT10_*
    # Virtex 4.
    Cell('GT11_CUSTOM'),
    Cell('GT11_DUAL'),
    Cell('GT11CLK'),
    Cell('GT11CLK_MGT'),
    # Virtex 5.
    Cell('GTP_DUAL'),
    Cell('GTX_DUAL'),
    Cell('CRC32', port_attrs={'CRCCLK': ['clkbuf_sink']}),
    Cell('CRC64', port_attrs={'CRCCLK': ['clkbuf_sink']}),
    # Virtex 6.
    Cell('GTHE1_QUAD'),
    Cell('GTXE1'),
    Cell('IBUFDS_GTXE1', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    Cell('IBUFDS_GTHE1', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    # Series 7.
    Cell('GTHE2_CHANNEL'),
    Cell('GTHE2_COMMON'),
    Cell('GTPE2_CHANNEL'),
    Cell('GTPE2_COMMON'),
    Cell('GTXE2_CHANNEL'),
    Cell('GTXE2_COMMON'),
    Cell('IBUFDS_GTE2', port_attrs={'I': ['iopad_external_pin'], 'IB': ['iopad_external_pin']}),
    # Ultrascale.
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
    Cell('OBUFDS_GTE3', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFDS_GTE3_ADV', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFDS_GTE4', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFDS_GTE4_ADV', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),

    # PCIE IP.
    Cell('PCIE_A1'), # Spartan 6
    Cell('PCIE_EP'), # Virtex 5
    Cell('PCIE_2_0'), # Virtex 6
    Cell('PCIE_2_1'), # Series 7
    Cell('PCIE_3_0'), # Series 7
    Cell('PCIE_3_1'), # Ultrascale
    Cell('PCIE40E4'), # Ultrascale+

    # Ethernet IP.
    Cell('EMAC'), # Virtex 4
    Cell('TEMAC'), # Virtex 5
    Cell('TEMAC_SINGLE'), # Virtex 6
    Cell('CMAC'), # Ultrascale
    Cell('CMACE4'), # Ultrsacale+

    # PowerPC.
    # TODO PPC405 (Virtex 2)
    Cell('PPC405_ADV'), # Virtex 4
    Cell('PPC440'), # Virtex 5

    # Misc hard IP.
    Cell('MCB'), # Spartan 6 Memory Controller Block
    Cell('PS7', keep=True), # The Zynq 7000 ARM Processor System.
    Cell('PS8', keep=True), # The Zynq Ultrascale+ ARM Processor System.
    Cell('ILKN'), # Ultrascale Interlaken
    Cell('ILKNE4'), # Ultrascale+ Interlaken
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

    out = StringIO()
    for cell in CELLS:
        xtract_cell_decl(cell, dirs, out)

    with open('cells_xtra.v', 'w') as f:
        f.write('// Created by cells_xtra.py from Xilinx models\n')
        f.write('\n')
        f.write(out.getvalue())
