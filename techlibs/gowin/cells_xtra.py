#!/usr/bin/env python3

# Base on Nexus cells_xtra.py

from argparse import ArgumentParser
import os.path
from enum import Enum, auto
import sys
import re

class State(Enum):
    OUTSIDE = auto()
    IN_MODULE = auto()
    IN_PARAMETER = auto()

_skip = { 'ALU', 'BANDGAP', 'DFF', 'DFFC', 'DFFCE', 'DFFE', 'DFFN', 'DFFNC', 'DFFNCE',
          'DFFNE', 'DFFNP', 'DFFNPE', 'DFFNR', 'DFFNRE', 'DFFNS', 'DFFNSE',
          'DFFP', 'DFFPE', 'DFFR', 'DFFRE', 'DFFS', 'DFFSE', 'DP', 'DPX9',
          'ELVDS_OBUF', 'GND', 'GSR', 'IBUF', 'IDDR', 'IDDRC', 'IDES10',
          'IDES16', 'IDES4', 'IDES8', 'IOBUF', 'IVIDEO', 'LUT1', 'LUT2',
          'LUT3', 'LUT4', 'MUX2', 'MUX2_LUT5', 'MUX2_LUT6', 'MUX2_LUT7',
          'MUX2_LUT8', 'OBUF', 'ODDR', 'ODDRC', 'OSC', 'OSCF', 'OSCH',
          'OSCO', 'OSCW', 'OSCZ', 'OSER10', 'OSER16', 'OSER10', 'OSER4',
          'OSER8', 'OVIDEO', 'PLLVR', 'RAM16S1', 'RAM16S2', 'RAM16S4',
          'RAM16SDP1', 'RAM16SDP2', 'RAM16SDP4', 'rPLL', 'SDP',
          'SDPX9', 'SP', 'SPX9', 'TBUF', 'TLVDS_OBUF', 'VCC', 'DCS', 'EMCU'
        }
def xtract_cells_decl(dir, fout):
    fname = os.path.join(dir, 'prim_sim.v')
    with open(fname) as f:
        state = State.OUTSIDE
        for l in f:
            l, _, comment = l.partition('//')
            if l.startswith("module "):
                cell_name = l[7:l.find('(')].strip()
                if cell_name not in _skip:
                    state = State.IN_MODULE
                    fout.write(f'\nmodule {cell_name} (...);\n')
            elif l.startswith(('input', 'output', 'inout')) and state == State.IN_MODULE:
                fout.write(l)
                if l[-1] != '\n':
                    fout.write('\n')
            elif l.startswith('parameter') and state == State.IN_MODULE:
                fout.write(l)
                if l.rstrip()[-1] == ',':
                    state = State.IN_PARAMETER
                if l[-1] != '\n':
                    fout.write('\n')
            elif state == State.IN_PARAMETER:
                fout.write(l)
                if l.rstrip()[-1] == ';':
                    state = State.IN_MODULE
                if l[-1] != '\n':
                    fout.write('\n')
            elif l.startswith('endmodule') and state == State.IN_MODULE:
                state = State.OUTSIDE
                fout.write('endmodule\n')
                if l[-1] != '\n':
                    fout.write('\n')

if __name__ == '__main__':
    parser = ArgumentParser(description='Extract Gowin blackbox cell definitions.')
    parser.add_argument('gowin_dir', nargs='?', default='/opt/gowin/')
    args = parser.parse_args()

    dirs = [
        os.path.join(args.gowin_dir, 'IDE/simlib/gw1n/'),
    ]

    with open('cells_xtra.v', 'w') as fout:
        fout.write('// Created by cells_xtra.py\n')
        fout.write('\n')
        for dir in dirs:
            if not os.path.isdir(dir):
                print(f'{dir} is not a directory')
            xtract_cells_decl(dir, fout)
