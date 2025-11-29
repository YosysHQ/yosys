#!/usr/bin/env python3

# Based on Xilinx cells_xtra.py; modified for Radiant's structure

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
    ("lifcl", [
        Cell("ACC54"),
        Cell("ADC"),
        Cell("ALUREG"),
        Cell("BB_ADC", keep=True),
        Cell("BB_CDR", keep=True),
        Cell("BB_I3C_A", keep=True),
        Cell("BFD1P3KX"),
        Cell("BFD1P3LX"),
        Cell("BNKREF18", keep=True),
        Cell("CONFIG_LMMI", keep=True),
        Cell("DCC"),
        Cell("DCS"),
        Cell("DDRDLL"),
        Cell("DELAYA"),
        Cell("DELAYB"),
        Cell("DIFFIO18", keep=True),
        Cell("DLLDEL"),
        Cell("DP16K_MODE"),
        Cell("DP16K"),
        Cell("DPHY", keep=True),
        Cell("DPSC512K"),
        Cell("DQSBUF"),
        Cell("EBR_CORE"),
        Cell("EBR"),
        Cell("ECLKDIV"),
        Cell("ECLKSYNC"),
        Cell("FBMUX"),
        Cell("FIFO16K_MODE"),
        Cell("FIFO16K"),
        Cell("GSR"),
        Cell("HSE"),
        Cell("I2CFIFO"),
        Cell("IDDR71"),
        Cell("IDDRX1"),
        Cell("IDDRX2DQ"),
        Cell("IDDRX2"),
        Cell("IDDRX4DQ"),
        Cell("IDDRX4"),
        Cell("IDDRX5"),
        Cell("IFD1P3BX"),
        Cell("IFD1P3DX"),
        Cell("IFD1P3IX"),
        Cell("IFD1P3JX"),
        Cell("JTAG", keep=True),
        Cell("LRAM"),
        Cell("M18X36"),
        Cell("MIPI"),
        Cell("MULT18"),
#        Cell("MULT18X18"),
#        Cell("MULT18X36"),
        Cell("MULT36"),
#        Cell("MULT36X36"),
        Cell("MULT9"),
#        Cell("MULT9X9"),
#        Cell("MULTADDSUB18X18"),
        Cell("MULTADDSUB18X18WIDE"),
#        Cell("MULTADDSUB18X36"),
#        Cell("MULTADDSUB36X36"),
        Cell("MULTADDSUB9X9WIDE"),
        Cell("MULTIBOOT", keep=True),
#        Cell("MULTPREADD18X18"),
#        Cell("MULTPREADD9X9"),
        Cell("ODDR71"),
        Cell("ODDRX1"),
        Cell("ODDRX2DQS"),
        Cell("ODDRX2DQ"),
        Cell("ODDRX2"),
        Cell("ODDRX4DQS"),
        Cell("ODDRX4DQ"),
        Cell("ODDRX4"),
        Cell("ODDRX5"),
        Cell("OFD1P3BX"),
        Cell("OFD1P3DX"),
        Cell("OFD1P3IX"),
        Cell("OFD1P3JX"),
        Cell("OSC"),
        Cell("OSCA"),
        Cell("OSHX2"),
        Cell("OSHX4"),
        Cell("PCIE"),
        Cell("PCLKDIV"),
        Cell("PCLKDIVSP"),
        Cell("PDP16K_MODE"),
        Cell("PDP16K"),
        Cell("PDPSC16K_MODE"),
        Cell("PDPSC16K"),
        Cell("PDPSC512K"),
        Cell("PLL"),
        Cell("PREADD9"),
        Cell("PUR", keep=True),
        Cell("REFMUX"),
        Cell("REG18"),
        Cell("SEDC", keep=True),
        Cell("SEIO18"),
        Cell("SEIO33"),
        Cell("SGMIICDR"),
        Cell("SP16K_MODE"),
        Cell("SP16K"),
        Cell("SP512K"),
        Cell("TSALLA"),
        Cell("TSHX2DQS"),
        Cell("TSHX2DQ"),
        Cell("TSHX4DQS"),
        Cell("TSHX4DQ"),
        Cell("WDT", keep=True),

        Cell("ACC54_CORE"),
        Cell("ADC_CORE"),
        Cell("ALUREG_CORE"),
        Cell("BNKREF18_CORE"),
        Cell("BNKREF33_CORE"),
        Cell("DIFFIO18_CORE"),
        Cell("CONFIG_CLKRST_CORE", keep=True),
        Cell("CONFIG_HSE_CORE", keep=True),
        Cell("CONFIG_IP_CORE", keep=True),
        Cell("CONFIG_JTAG_CORE", keep=True),
        Cell("CONFIG_LMMI_CORE", keep=True),
        Cell("CONFIG_MULTIBOOT_CORE", keep=True),
        Cell("CONFIG_SEDC_CORE", keep=True),
        Cell("CONFIG_WDT_CORE", keep=True),
        Cell("DDRDLL_CORE"),
        Cell("DLLDEL_CORE"),
        Cell("DPHY_CORE"),
        Cell("DQSBUF_CORE"),
        Cell("ECLKDIV_CORE"),
        Cell("ECLKSYNC_CORE"),
        Cell("FBMUX_CORE"),
        Cell("GSR_CORE"),
        Cell("I2CFIFO_CORE"),
        Cell("LRAM_CORE"),
        Cell("MULT18_CORE"),
        Cell("MULT18X36_CORE"),
        Cell("MULT36_CORE"),
        Cell("MULT9_CORE"),
        Cell("OSC_CORE"),
        Cell("PCIE_CORE"),
        Cell("PLL_CORE"),
        Cell("PREADD9_CORE"),
        Cell("REFMUX_CORE"),
        Cell("REG18_CORE"),
        Cell("SEIO18_CORE"),
        Cell("SEIO33_CORE"),
        Cell("SGMIICDR_CORE"),
    ])
]

def xtract_cells_decl(device, cells, dirs, outf):
    fname = os.path.join(dir, device + '.v')
    with open(fname) as f:
        state = State.OUTSIDE
        # Probably the most horrible Verilog "parser" ever written.
        cell = None
        for l in f:
            l, _, comment = l.partition('//')
            l = l.strip()
            if l.startswith("module "):
                cell_name = l[7:l.find('(')].strip()
                cell = None
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
                    if cell.keep:
                        outf.write('(* keep *)\n')
                    outf.write('module {} (...);\n'.format(cell.name))
                    cell.found = True

                    m = re.search(r'synthesis .*black_box_pad_pin="([^"]*)"', comment)
                    if m:
                        iopad_pin = set(m.group(1).split(","))

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
                if l.endswith((';', ',')):
                    l = l[:-1]
                while '  ' in l:
                    l = l.replace('  ', ' ')
                if ';' in l:
                    print('Weird parameter line in {} [{}].'.format(fname, l))
                    sys.exit(1)
                outf.write('    {};\n'.format(l))

        if state != State.OUTSIDE:
            print('endmodule not found in {}.'.format(fname))
            sys.exit(1)
        for cell in cells:
            if not cell.found:
                print('cell {} not found in {}.'.format(cell.name, fname))
if __name__ == '__main__':
    parser = ArgumentParser(description='Extract Lattice blackbox cell definitions from Radiant.')
    parser.add_argument('radiant_dir', nargs='?', default='/opt/lscc/radiant/2.0/')
    args = parser.parse_args()

    dirs = [
        os.path.join(args.radiant_dir, 'cae_library/synthesis/verilog/'),
    ]
    for dir in dirs:
        if not os.path.isdir(dir):
            print('{} is not a directory'.format(dir))

    out = StringIO()
    for device, cells in devices:
        xtract_cells_decl(device, cells, dirs, out)

    with open('cells_bb_nexus.v', 'w') as f:
        f.write('// Created by cells_xtra_nexus.py from Lattice models\n')
        f.write('\n')
        f.write(out.getvalue())
