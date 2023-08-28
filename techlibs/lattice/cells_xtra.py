#!/usr/bin/env python3

# Based on Xilinx cells_xtra.py; modified for Lattice's structure

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
        self.found = False

class State(Enum):
    OUTSIDE = auto()
    IN_MODULE = auto()
    IN_OTHER_MODULE = auto()
    IN_FUNCTION = auto()
    IN_TASK = auto()

devices = [
    ("cells_bb_ecp5.v", "ecp5u", [
        #Cell("AND2"),
        #Cell("AND3"),
        #Cell("AND4"),
        #Cell("AND5"),
        #Cell("BB"),
        #Cell("BBPD"),
        #Cell("BBPU"),
        #Cell("CCU2C"),
        #Cell("FD1P3AX"),
        #Cell("FD1P3AY"),
        #Cell("FD1P3BX"),
        #Cell("FD1P3DX"),
        #Cell("FD1P3IX"),
        #Cell("FD1P3JX"),
        #Cell("FD1S3AX"),
        #Cell("FD1S3AY"),
        #Cell("FD1S3BX"),
        #Cell("FD1S3DX"),
        #Cell("FD1S3IX"),
        #Cell("FD1S3JX"),
        #Cell("FL1P3AY"),
        #Cell("FL1P3AZ"),
        #Cell("FL1P3BX"),
        #Cell("FL1P3DX"),
        #Cell("FL1P3IY"),
        #Cell("FL1P3JY"),
        #Cell("FL1S3AX"),
        #Cell("FL1S3AY"),
        Cell("GSR", True),
        #Cell("IB"),
        #Cell("IBPD"),
        #Cell("IBPU"),
        #Cell("IFS1P3BX"),
        #Cell("IFS1P3DX"),
        #Cell("IFS1P3IX"),
        #Cell("IFS1P3JX"),
        #Cell("IFS1S1B"),
        #Cell("IFS1S1D"),
        #Cell("IFS1S1I"),
        #Cell("IFS1S1J"),
        #Cell("ILVDS"),
        #Cell("INV"),
        #Cell("L6MUX21"),
        #Cell("LUT4"),
        #Cell("LUT5"),
        #Cell("LUT6"),
        #Cell("LUT7"),
        #Cell("LUT8"),
        #Cell("MUX161"),
        #Cell("MUX21"),
        #Cell("MUX321"),
        #Cell("MUX41"),
        #Cell("MUX81"),
        #Cell("ND2"),
        #Cell("ND3"),
        #Cell("ND4"),
        #Cell("ND5"),
        #Cell("NR2"),
        #Cell("NR3"),
        #Cell("NR4"),
        #Cell("NR5"),
        #Cell("OB"),
        #Cell("OBCO"),
        #Cell("OBZ"),
        #Cell("OBZPU"),
        #Cell("OFS1P3BX"),
        #Cell("OFS1P3DX"),
        #Cell("OFS1P3IX"),
        #Cell("OFS1P3JX"),
        #Cell("OLVDS"),
        #Cell("OR2"),
        #Cell("OR3"),
        #Cell("OR4"),
        #Cell("OR5"),
        #Cell("PFUMX"),
        Cell("PUR"),
        #Cell("ROM128X1A"),
        #Cell("ROM16X1A"),
        #Cell("ROM256X1A"),
        #Cell("ROM32X1A"),
        #Cell("ROM64X1A"),
        Cell("SGSR", True),
        #Cell("VHI"),
        #Cell("VLO"),
        #Cell("XNOR2"),
        #Cell("XNOR3"),
        #Cell("XNOR4"),
        #Cell("XNOR5"),
        #Cell("XOR11"),
        #Cell("XOR2"),
        #Cell("XOR21"),
        #Cell("XOR3"),
        #Cell("XOR4"),
        #Cell("XOR5"),
        Cell("DP16KD"),
        Cell("PDPW16KD"),
        #Cell("DPR16X4C"),
        #Cell("SPR16X4C"),
        #Cell("LVDSOB"),
        #Cell("IMIPI"),
        #Cell("MULT9X9C"),
        #Cell("MULT9X9D"),
        #Cell("MULT18X18C"),
        Cell("MULT18X18D"),
        #Cell("ALU24A"),
        #Cell("ALU54A"),
        #Cell("ALU24B"),
        Cell("ALU54B"),
        #Cell("PRADD9A"),
        #Cell("PRADD18A"),
        #Cell("BCINRD"),
        #Cell("BCLVDSOB"),
        #Cell("INRDB"),
        Cell("CLKDIVF"),
        Cell("PCSCLKDIV"),
        Cell("DCSC"),
        Cell("DCCA"),
        Cell("ECLKSYNCB"),
        Cell("ECLKBRIDGECS"),
        #Cell("PLLREFCS"),
        Cell("DELAYF"),
        Cell("DELAYG"),
        #Cell("START"),
        Cell("USRMCLK", True),
        Cell("DQSBUFM"),
        Cell("DDRDLLA"),
        Cell("DLLDELD"),
        Cell("IDDRX1F"),
        Cell("IDDRX2F"),
        Cell("IDDR71B"),
        Cell("IDDRX2DQA"),
        Cell("ODDRX1F"),
        Cell("ODDRX2F"),
        Cell("ODDR71B"),
        Cell("OSHX2A"),
        Cell("TSHX2DQA"),
        Cell("TSHX2DQSA"),
        Cell("ODDRX2DQA"),
        Cell("ODDRX2DQSB"),
        Cell("EHXPLLL"),
        Cell("DTR"),
        Cell("OSCG"),
        Cell("EXTREFB"),
        Cell("JTAGG", True, port_attrs={'TCK': ['iopad_external_pin'], 'TMS': ['iopad_external_pin'], 'TDO': ['iopad_external_pin'], 'TDI': ['iopad_external_pin']}),
        #Cell("SEDGA"),
        Cell("DCUA", True, port_attrs={'CH0_HDINP': ['iopad_external_pin'], 'CH1_HDINP': ['iopad_external_pin'], 'CH0_HDINN': ['iopad_external_pin'], 'CH1_HDINN': ['iopad_external_pin']}),
    ]),
    ("cells_bb_xo2.v", "machxo2", [
        #Cell("AGEB2"),
        #Cell("ALEB2"),
        #Cell("AND2"),
        #Cell("AND3"),
        #Cell("AND4"),
        #Cell("AND5"),
        #Cell("ANEB2"),
        #Cell("BB"),
        #Cell("BBPD"),
        #Cell("BBPU"),
        #Cell("BBW"),
        #Cell("CB2"),
        #Cell("CD2"),
        #Cell("CU2"),
        #Cell("FADD2B"),
        #Cell("FADSU2"),
        #Cell("FD1P3AX"),
        #Cell("FD1P3AY"),
        #Cell("FD1P3BX"),
        #Cell("FD1P3DX"),
        #Cell("FD1P3IX"),
        #Cell("FD1P3JX"),
        #Cell("FD1S1A"),
        #Cell("FD1S1AY"),
        #Cell("FD1S1B"),
        #Cell("FD1S1D"),
        #Cell("FD1S1I"),
        #Cell("FD1S1J"),
        #Cell("FD1S3AX"),
        #Cell("FD1S3AY"),
        #Cell("FD1S3BX"),
        #Cell("FD1S3DX"),
        #Cell("FD1S3IX"),
        #Cell("FD1S3JX"),
        #Cell("FL1P3AY"),
        #Cell("FL1P3AZ"),
        #Cell("FL1P3BX"),
        #Cell("FL1P3DX"),
        #Cell("FL1P3IY"),
        #Cell("FL1P3JY"),
        #Cell("FL1S1A"),
        #Cell("FL1S1AY"),
        #Cell("FL1S1B"),
        #Cell("FL1S1D"),
        #Cell("FL1S1I"),
        #Cell("FL1S1J"),
        #Cell("FL1S3AX"),
        #Cell("FL1S3AY"),
        #Cell("FSUB2B"),
        Cell("GSR", True),
        #Cell("IB"),
        #Cell("IBPD"),
        #Cell("IBPU"),
        #Cell("IFS1P3BX"),
        #Cell("IFS1P3DX"),
        #Cell("IFS1P3IX"),
        #Cell("IFS1P3JX"),
        #Cell("ILVDS"),
        #Cell("INV"),
        #Cell("L6MUX21"),
        #Cell("LB2P3AX"),
        #Cell("LB2P3AY"),
        #Cell("LB2P3BX"),
        #Cell("LB2P3DX"),
        #Cell("LB2P3IX"),
        #Cell("LB2P3JX"),
        #Cell("LD2P3AX"),
        #Cell("LD2P3AY"),
        #Cell("LD2P3BX"),
        #Cell("LD2P3DX"),
        #Cell("LD2P3IX"),
        #Cell("LD2P3JX"),
        #Cell("LU2P3AX"),
        #Cell("LU2P3AY"),
        #Cell("LU2P3BX"),
        #Cell("LU2P3DX"),
        #Cell("LU2P3IX"),
        #Cell("LU2P3JX"),
        #Cell("MULT2"),
        #Cell("MUX161"),
        #Cell("MUX21"),
        #Cell("MUX321"),
        #Cell("MUX41"),
        #Cell("MUX81"),
        #Cell("ND2"),
        #Cell("ND3"),
        #Cell("ND4"),
        #Cell("ND5"),
        #Cell("NR2"),
        #Cell("NR3"),
        #Cell("NR4"),
        #Cell("NR5"),
        #Cell("OB"),
        #Cell("OBCO"),
        #Cell("OBZ"),
        #Cell("OBZPU"),
        #Cell("OFS1P3BX"),
        #Cell("OFS1P3DX"),
        #Cell("OFS1P3IX"),
        #Cell("OFS1P3JX"),
        #Cell("OLVDS"),
        #Cell("OR2"),
        #Cell("OR3"),
        #Cell("OR4"),
        #Cell("OR5"),
        #Cell("LUT4"),
        #Cell("LUT5"),
        #Cell("LUT6"),
        #Cell("LUT7"),
        #Cell("LUT8"),
        #Cell("PFUMX"),
        #Cell("PUR"),
        #Cell("ROM128X1A"),
        #Cell("ROM16X1A"),
        #Cell("ROM256X1A"),
        #Cell("ROM32X1A"),
        #Cell("ROM64X1A"),
        #Cell("CCU2D"),
        #Cell("VHI"),
        #Cell("VLO"),
        #Cell("XNOR2"),
        #Cell("XNOR3"),
        #Cell("XNOR4"),
        #Cell("XNOR5"),
        #Cell("XOR11"),
        #Cell("XOR2"),
        #Cell("XOR21"),
        #Cell("XOR3"),
        #Cell("XOR4"),
        #Cell("XOR5"),
        #Cell("IFS1S1B"),
        #Cell("IFS1S1D"),
        #Cell("IFS1S1I"),
        #Cell("IFS1S1J"),
        #Cell("DPR16X4C"),
        #Cell("SPR16X4C"),
        Cell("SGSR", True),
        Cell("DP8KC"),
        Cell("PDPW8KC"),
        Cell("SP8KC"),
        Cell("FIFO8KB"),
        Cell("CLKDIVC"),
        Cell("DCMA"),
        Cell("ECLKSYNCA"),
        Cell("ECLKBRIDGECS"),
        Cell("DCCA"),
        #Cell("JTAGF", True, port_attrs={'TCK': ['iopad_external_pin'], 'TMS': ['iopad_external_pin'], 'TDO': ['iopad_external_pin'], 'TDI': ['iopad_external_pin']}),
        Cell("START", True),
        #Cell("SEDFA"),
        #Cell("SEDFB"),
        #Cell("IDDRXE"),
        #Cell("IDDRX2E"),
        #Cell("IDDRX4B"),
        #Cell("IDDRDQSX1A"),
        #Cell("IDDRX71A"),
        #Cell("ODDRXE"),
        #Cell("ODDRX2E"),
        #Cell("ODDRX4B"),
        #Cell("ODDRDQSX1A"),
        #Cell("ODDRX71A"),
        #Cell("TDDRA"),
        #Cell("DQSBUFH"),
        #Cell("DQSDLLC"),
        #Cell("DELAYE"),
        #Cell("DELAYD"),
        #Cell("DLLDELC"),
        #Cell("CLKFBBUFA"),
        #Cell("PCNTR"),
        #Cell("BCINRD"),
        #Cell("BCLVDSO"),
        #Cell("INRDB"),
        #Cell("LVDSOB"),
        #Cell("PG"),
        Cell("EHXPLLJ"),
        #Cell("PLLREFCS"),
        Cell("OSCH"),
        #Cell("EFB"),
        Cell("TSALL", True),
    ]),
    ("cells_bb_xo3.v", "machxo3lf", [
        #Cell("AGEB2"),
        #Cell("ALEB2"),
        #Cell("AND2"),
        #Cell("AND3"),
        #Cell("AND4"),
        #Cell("AND5"),
        #Cell("ANEB2"),
        #Cell("BB"),
        #Cell("BBPD"),
        #Cell("BBPU"),
        #Cell("BBW"),
        #Cell("CB2"),
        #Cell("CD2"),
        #Cell("CU2"),
        #Cell("FADD2B"),
        #Cell("FADSU2"),
        #Cell("FD1P3AX"),
        #Cell("FD1P3AY"),
        #Cell("FD1P3BX"),
        #Cell("FD1P3DX"),
        #Cell("FD1P3IX"),
        #Cell("FD1P3JX"),
        #Cell("FD1S1A"),
        #Cell("FD1S1AY"),
        #Cell("FD1S1B"),
        #Cell("FD1S1D"),
        #Cell("FD1S1I"),
        #Cell("FD1S1J"),
        #Cell("FD1S3AX"),
        #Cell("FD1S3AY"),
        #Cell("FD1S3BX"),
        #Cell("FD1S3DX"),
        #Cell("FD1S3IX"),
        #Cell("FD1S3JX"),
        #Cell("FL1P3AY"),
        #Cell("FL1P3AZ"),
        #Cell("FL1P3BX"),
        #Cell("FL1P3DX"),
        #Cell("FL1P3IY"),
        #Cell("FL1P3JY"),
        #Cell("FL1S1A"),
        #Cell("FL1S1AY"),
        #Cell("FL1S1B"),
        #Cell("FL1S1D"),
        #Cell("FL1S1I"),
        #Cell("FL1S1J"),
        #Cell("FL1S3AX"),
        #Cell("FL1S3AY"),
        #Cell("FSUB2B"),
        Cell("GSR", True),
        #Cell("IB"),
        #Cell("IBPD"),
        #Cell("IBPU"),
        #Cell("IFS1P3BX"),
        #Cell("IFS1P3DX"),
        #Cell("IFS1P3IX"),
        #Cell("IFS1P3JX"),
        #Cell("ILVDS"),
        #Cell("INV"),
        #Cell("L6MUX21"),
        #Cell("LB2P3AX"),
        #Cell("LB2P3AY"),
        #Cell("LB2P3BX"),
        #Cell("LB2P3DX"),
        #Cell("LB2P3IX"),
        #Cell("LB2P3JX"),
        #Cell("LD2P3AX"),
        #Cell("LD2P3AY"),
        #Cell("LD2P3BX"),
        #Cell("LD2P3DX"),
        #Cell("LD2P3IX"),
        #Cell("LD2P3JX"),
        #Cell("LU2P3AX"),
        #Cell("LU2P3AY"),
        #Cell("LU2P3BX"),
        #Cell("LU2P3DX"),
        #Cell("LU2P3IX"),
        #Cell("LU2P3JX"),
        #Cell("MULT2"),
        #Cell("MUX161"),
        #Cell("MUX21"),
        #Cell("MUX321"),
        #Cell("MUX41"),
        #Cell("MUX81"),
        #Cell("ND2"),
        #Cell("ND3"),
        #Cell("ND4"),
        #Cell("ND5"),
        #Cell("NR2"),
        #Cell("NR3"),
        #Cell("NR4"),
        #Cell("NR5"),
        #Cell("OB"),
        #Cell("OBCO"),
        #Cell("OBZ"),
        #Cell("OBZPU"),
        #Cell("OFS1P3BX"),
        #Cell("OFS1P3DX"),
        #Cell("OFS1P3IX"),
        #Cell("OFS1P3JX"),
        #Cell("OLVDS"),
        #Cell("OR2"),
        #Cell("OR3"),
        #Cell("OR4"),
        #Cell("OR5"),
        #Cell("LUT4"),
        #Cell("LUT5"),
        #Cell("LUT6"),
        #Cell("LUT7"),
        #Cell("LUT8"),
        #Cell("PFUMX"),
        #Cell("PUR"),
        #Cell("ROM128X1A"),
        #Cell("ROM16X1A"),
        #Cell("ROM256X1A"),
        #Cell("ROM32X1A"),
        #Cell("ROM64X1A"),
        #Cell("CCU2D"),
        #Cell("VHI"),
        #Cell("VLO"),
        #Cell("XNOR2"),
        #Cell("XNOR3"),
        #Cell("XNOR4"),
        #Cell("XNOR5"),
        #Cell("XOR11"),
        #Cell("XOR2"),
        #Cell("XOR21"),
        #Cell("XOR3"),
        #Cell("XOR4"),
        #Cell("XOR5"),
        #Cell("IFS1S1B"),
        #Cell("IFS1S1D"),
        #Cell("IFS1S1I"),
        #Cell("IFS1S1J"),
        #Cell("DPR16X4C"),
        #Cell("SPR16X4C"),
        Cell("SGSR", True),
        Cell("DP8KC"),
        Cell("PDPW8KC"),
        Cell("SP8KC"),
        Cell("FIFO8KB"),
        Cell("CLKDIVC"),
        Cell("DCMA"),
        Cell("ECLKSYNCA"),
        Cell("ECLKBRIDGECS"),
        Cell("DCCA"),
        #Cell("JTAGF", True, port_attrs={'TCK': ['iopad_external_pin'], 'TMS': ['iopad_external_pin'], 'TDO': ['iopad_external_pin'], 'TDI': ['iopad_external_pin']}),
        Cell("START", True),
        #Cell("SEDFA"),
        #Cell("SEDFB"),
        #Cell("IDDRXE"),
        #Cell("IDDRX2E"),
        #Cell("IDDRX4B"),
        #Cell("IDDRX71A"),
        #Cell("ODDRXE"),
        #Cell("ODDRX2E"),
        #Cell("ODDRX4B"),
        #Cell("ODDRX71A"),
        #Cell("DQSDLLC"),
        #Cell("DELAYE"),
        #Cell("DELAYD"),
        #Cell("DLLDELC"),
        #Cell("CLKFBBUFA"),
        #Cell("PCNTR"),
        #Cell("BCINRD"),
        #Cell("BCLVDSO"),
        #Cell("INRDB"),
        #Cell("LVDSOB"),
        #Cell("PG"),
        Cell("EHXPLLJ"),
        #Cell("PLLREFCS"),
        Cell("OSCH"),
        #Cell("EFB"),
        Cell("TSALL", True),
    ]),
    ("cells_bb_xo3d.v", "machxo3d", [
        #Cell("AGEB2"),
        #Cell("ALEB2"),
        #Cell("AND2"),
        #Cell("AND3"),
        #Cell("AND4"),
        #Cell("AND5"),
        #Cell("ANEB2"),
        #Cell("BB"),
        #Cell("BBPD"),
        #Cell("BBPU"),
        #Cell("BBI3C"),
        #Cell("BBW"),
        #Cell("CB2"),
        #Cell("CD2"),
        #Cell("CU2"),
        #Cell("FADD2B"),
        #Cell("FADSU2"),
        #Cell("FD1P3AX"),
        #Cell("FD1P3AY"),
        #Cell("FD1P3BX"),
        #Cell("FD1P3DX"),
        #Cell("FD1P3IX"),
        #Cell("FD1P3JX"),
        #Cell("FD1S1A"),
        #Cell("FD1S1AY"),
        #Cell("FD1S1B"),
        #Cell("FD1S1D"),
        #Cell("FD1S1I"),
        #Cell("FD1S1J"),
        #Cell("FD1S3AX"),
        #Cell("FD1S3AY"),
        #Cell("FD1S3BX"),
        #Cell("FD1S3DX"),
        #Cell("FD1S3IX"),
        #Cell("FD1S3JX"),
        #Cell("FL1P3AY"),
        #Cell("FL1P3AZ"),
        #Cell("FL1P3BX"),
        #Cell("FL1P3DX"),
        #Cell("FL1P3IY"),
        #Cell("FL1P3JY"),
        #Cell("FL1S1A"),
        #Cell("FL1S1AY"),
        #Cell("FL1S1B"),
        #Cell("FL1S1D"),
        #Cell("FL1S1I"),
        #Cell("FL1S1J"),
        #Cell("FL1S3AX"),
        #Cell("FL1S3AY"),
        #Cell("FSUB2B"),
        Cell("GSR", True),
        #Cell("IB"),
        #Cell("IBPD"),
        #Cell("IBPU"),
        #Cell("IFS1P3BX"),
        #Cell("IFS1P3DX"),
        #Cell("IFS1P3IX"),
        #Cell("IFS1P3JX"),
        #Cell("ILVDS"),
        #Cell("INV"),
        #Cell("L6MUX21"),
        #Cell("LB2P3AX"),
        #Cell("LB2P3AY"),
        #Cell("LB2P3BX"),
        #Cell("LB2P3DX"),
        #Cell("LB2P3IX"),
        #Cell("LB2P3JX"),
        #Cell("LD2P3AX"),
        #Cell("LD2P3AY"),
        #Cell("LD2P3BX"),
        #Cell("LD2P3DX"),
        #Cell("LD2P3IX"),
        #Cell("LD2P3JX"),
        #Cell("LU2P3AX"),
        #Cell("LU2P3AY"),
        #Cell("LU2P3BX"),
        #Cell("LU2P3DX"),
        #Cell("LU2P3IX"),
        #Cell("LU2P3JX"),
        #Cell("MULT2"),
        #Cell("MUX161"),
        #Cell("MUX21"),
        #Cell("MUX321"),
        #Cell("MUX41"),
        #Cell("MUX81"),
        #Cell("ND2"),
        #Cell("ND3"),
        #Cell("ND4"),
        #Cell("ND5"),
        #Cell("NR2"),
        #Cell("NR3"),
        #Cell("NR4"),
        #Cell("NR5"),
        #Cell("OB"),
        #Cell("OBCO"),
        #Cell("OBZ"),
        #Cell("OBZPU"),
        #Cell("OFS1P3BX"),
        #Cell("OFS1P3DX"),
        #Cell("OFS1P3IX"),
        #Cell("OFS1P3JX"),
        #Cell("OLVDS"),
        #Cell("OR2"),
        #Cell("OR3"),
        #Cell("OR4"),
        #Cell("OR5"),
        #Cell("LUT4"),
        #Cell("LUT5"),
        #Cell("LUT6"),
        #Cell("LUT7"),
        #Cell("LUT8"),
        #Cell("PFUMX"),
        #Cell("PUR"),
        #Cell("ROM128X1A"),
        #Cell("ROM16X1A"),
        #Cell("ROM256X1A"),
        #Cell("ROM32X1A"),
        #Cell("ROM64X1A"),
        #Cell("CCU2D"),
        #Cell("VHI"),
        #Cell("VLO"),
        #Cell("XNOR2"),
        #Cell("XNOR3"),
        #Cell("XNOR4"),
        #Cell("XNOR5"),
        #Cell("XOR11"),
        #Cell("XOR2"),
        #Cell("XOR21"),
        #Cell("XOR3"),
        #Cell("XOR4"),
        #Cell("XOR5"),
        #Cell("IFS1S1B"),
        #Cell("IFS1S1D"),
        #Cell("IFS1S1I"),
        #Cell("IFS1S1J"),
        #Cell("DPR16X4C"),
        #Cell("SPR16X4C"),
        Cell("SGSR", True),
        Cell("DP8KC"),
        Cell("PDPW8KC"),
        Cell("SP8KC"),
        Cell("FIFO8KB"),
        Cell("CLKDIVC"),
        Cell("DCMA"),
        Cell("ECLKSYNCA"),
        Cell("ECLKBRIDGECS"),
        Cell("DCCA"),
        #Cell("JTAGF", True, port_attrs={'TCK': ['iopad_external_pin'], 'TMS': ['iopad_external_pin'], 'TDO': ['iopad_external_pin'], 'TDI': ['iopad_external_pin']}),
        Cell("START", True),
        #Cell("SEDFA"),
        #Cell("SEDFB"),
        #Cell("IDDRXE"),
        #Cell("IDDRX2E"),
        #Cell("IDDRX4B"),
        #Cell("IDDRX71A"),
        #Cell("ODDRXE"),
        #Cell("ODDRX2E"),
        #Cell("ODDRX4B"),
        #Cell("ODDRX71A"),
        #Cell("DQSDLLC"),
        #Cell("DELAYE"),
        #Cell("DELAYD"),
        #Cell("DLLDELC"),
        #Cell("CLKFBBUFA"),
        #Cell("PCNTR"),
        #Cell("BCINRD"),
        #Cell("BCLVDSO"),
        #Cell("INRDB"),
        #Cell("LVDSOB"),
        #Cell("PG"),
        Cell("EHXPLLJ"),
        #Cell("PLLREFCS"),
        Cell("OSCJ"),
        #Cell("EFBB"),
        Cell("TSALL", True),
        #Cell("ESBA"),
        #Cell("BCSLEWRATEA"),
    ])
]

def xtract_cells_decl(device, cells, dirs, outf):
    fname = os.path.join(dir, device + '.v')
    with open(fname) as f:
        state = State.OUTSIDE
        # Probably the most horrible Verilog "parser" ever written.
        cell = None
        kind = None
        for l in f:
            l, _, comment = l.partition('//')
            l = l.strip()
            m = re.search(r'synthesis .*black_box_pad_pin="([^"]*)"', comment)
            if m:
                iopad_pin = set(m.group(1).split(","))

            if l.startswith("module "):
                cell_name = l[7:l.find('(')].strip()
                cell = None
                kind = None
                module_ports = []
                iopad_pin = set()
                if state != State.OUTSIDE:
                    print('Nested modules in {}.'.format(fname))
                    sys.exit(1)
                for c in cells:
                    if c.name != cell_name:
                        continue
                    cell = c
                    state = State.IN_MODULE
                    outf.write('(* blackbox *)')
                    if cell.keep:
                        outf.write(' (* keep *)\n')
                    else:
                        outf.write('\n')
                    outf.write('module {} (...);\n'.format(cell.name))
                    cell.found = True
                if cell is None:
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
                        if port in iopad_pin:
                            outf.write('    (* iopad_external_pin *)\n')
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
                l = l.strip()
                if l == "":
                    continue
                if l.endswith((';', ',', ")")):
                    l = l[:-1]
                l = l.replace(")","")
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
                l = l.strip()
                if l.endswith((';', ',')):
                    l = l[:-1]
                while '  ' in l:
                    l = l.replace('  ', ' ')

                if "INITVAL" in l:
                    l = l.replace('"0x', "320'h")
                    l = l.replace('"', '')
                if ';' in l:
                    print('Weird parameter line in {} [{}].'.format(fname, l))
                    sys.exit(1)
                outf.write('    {};\n'.format(l))
            elif kind is not None and state == State.IN_MODULE:
                l = l.strip()
                if l == "":
                    continue
                if l.endswith((';', ',', ")")):
                    l = l[:-1]
                l = l.replace(")","")
                if l == "":
                    continue
                if ';' in l:
                    print('Weird port line in {} [{}].'.format(fname, l))
                    sys.exit(1)
                ports = l
                for port in ports.split(','):
                    port = port.strip()
                    if port.startswith('['):
                        rng, port = port.split()
                    else:
                        rng = None
                    module_ports.append((kind, rng, port))

        if state != State.OUTSIDE:
            print('endmodule not found in {}.'.format(fname))
            sys.exit(1)
        for cell in cells:
            if not cell.found:
                print('cell {} not found in {}.'.format(cell.name, fname))
if __name__ == '__main__':
    parser = ArgumentParser(description='Extract Lattice blackbox cell definitions from Lattice Diamond.')
    parser.add_argument('diamond_dir', nargs='?', default='/usr/local/diamond/3.12/')
    args = parser.parse_args()

    dirs = [
        os.path.join(args.diamond_dir, 'cae_library/synthesis/verilog/'),
    ]
    for dir in dirs:
        if not os.path.isdir(dir):
            print('{} is not a directory'.format(dir))

    for fn, device, cells in devices:
        out = StringIO()
        xtract_cells_decl(device, cells, dirs, out)
        with open(fn, 'w') as f:
            f.write('// Created by cells_xtra.py from Lattice models\n')
            f.write('\n')
            f.write(out.getvalue())
