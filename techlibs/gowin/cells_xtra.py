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
    IN_MODULE_MULTILINE = auto()
    IN_PARAMETER = auto()

_skip = { # These are already described, no need to extract them from the vendor files
          'ALU', 'BANDGAP', 'DFF', 'DFFC', 'DFFCE', 'DFFE', 'DFFN', 'DFFNC', 'DFFNCE',
          'DFFNE', 'DFFNP', 'DFFNPE', 'DFFNR', 'DFFNRE', 'DFFNS', 'DFFNSE',
          'DFFP', 'DFFPE', 'DFFR', 'DFFRE', 'DFFS', 'DFFSE', 'DP', 'DPX9',
          'ELVDS_OBUF', 'GND', 'GSR', 'IBUF', 'IDDR', 'IDDRC', 'IDES10',
          'IDES16', 'IDES4', 'IDES8', 'IOBUF', 'IVIDEO', 'LUT1', 'LUT2',
          'LUT3', 'LUT4', 'MUX2', 'MUX2_LUT5', 'MUX2_LUT6', 'MUX2_LUT7',
          'MUX2_LUT8', 'OBUF', 'ODDR', 'ODDRC', 'OSC', 'OSCF', 'OSCH',
          'OSCO', 'OSCW', 'OSCZ', 'OSER10', 'OSER16', 'OSER10', 'OSER4',
          'OSER8', 'OVIDEO', 'PLLVR', 'RAM16S1', 'RAM16S2', 'RAM16S4',
          'RAM16SDP1', 'RAM16SDP2', 'RAM16SDP4', 'rPLL', 'SDP',
          'SDPX9', 'SP', 'SPX9', 'TBUF', 'TLVDS_OBUF', 'VCC', 'EMCU',
          # These are not planned for implementation
          'MUX2_MUX8', 'MUX2_MUX16', 'MUX2_MUX32', 'MUX4', 'MUX8', 'MUX16',
          'MUX32', 'DL', 'DLE', 'DLC', 'DLCE', 'DLP', 'DLPE', 'DLN', 'DLNE',
          'DLNC', 'DLNCE', 'DLNP', 'DLNPE', 'rSDP', 'rSDPX9', 'rROM', 'rROMX9',
          'TLVDS_OEN_BK', 'DLL', 'DCC', 'I3C', 'IODELAYA', 'IODELAYC', 'IODELAYB',
          'SPMI', 'PLLO', 'DCCG', 'MIPI_DPHY_RX', 'CLKDIVG', 'PWRGRD', 'FLASH96KA',
         # ADCs are in a separate file
         'ADCLRC', 'ADCULC', 'ADC', 'ADC_SAR', 'ADCA',
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
                if l.rstrip()[-1] != ';':
                    state = State.IN_MODULE_MULTILINE
            elif l.lstrip().startswith('parameter') and state == State.IN_MODULE:
                fout.write(l)
                if l.rstrip()[-1] == ',':
                    state = State.IN_PARAMETER
                if l[-1] != '\n':
                    fout.write('\n')
            elif l and state == State.IN_MODULE_MULTILINE:
                fout.write(l)
                if l[-1] != '\n':
                    fout.write('\n')
                if l.rstrip()[-1] == ';':
                    state = State.IN_MODULE
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

    families = {
        'gw1n': os.path.join(args.gowin_dir, 'IDE/simlib/gw1n/'),
        'gw2a': os.path.join(args.gowin_dir, 'IDE/simlib/gw2a/'),
        'gw5a': os.path.join(args.gowin_dir, 'IDE/simlib/gw5a/'),
    }

    for family, dir in families.items():
        if not os.path.isdir(dir):
            print(f'{dir} is not a directory')
        else:
            with open(f'cells_xtra_{family}.v', 'w') as fout:
                fout.write('// Created by cells_xtra.py\n')
                fout.write('\n')
                xtract_cells_decl(dir, fout)
                if family == 'gw5a':
                    fout.write('\n')
                    fout.write('// Added from adc.v\n')
                    fout.write('\n')
                    with open(f'adc.v', 'r') as fin:
                        for l in fin:
                            fout.write(l);

