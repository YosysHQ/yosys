#!/usr/bin/env python3

from argparse import ArgumentParser
from io import StringIO
from enum import Enum, auto
import os.path
import sys


class Cell:
    def __init__(self, name, keep=False, port_attrs={}):
        self.name = name
        self.keep = keep
        self.port_attrs = port_attrs


CELLS = [
    # Design elements types listed in Xilinx UG953
    Cell('BSCANE2', keep=True),
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
    Cell('CAPTUREE2', keep=True),
    # Cell('CARRY4'),
    Cell('CFGLUT5', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('DCIRESET', keep=True),
    Cell('DNA_PORT'),
    Cell('DSP48E1', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('EFUSE_USR'),
    # Cell('FDCE'),
    # Cell('FDPE'),
    # Cell('FDRE'),
    # Cell('FDSE'),
    Cell('FIFO18E1', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FIFO36E1', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('FRAME_ECCE2'),
    Cell('GTHE2_CHANNEL'),
    Cell('GTHE2_COMMON'),
    Cell('GTPE2_CHANNEL'),
    Cell('GTPE2_COMMON'),
    Cell('GTXE2_CHANNEL'),
    Cell('GTXE2_COMMON'),
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
    Cell('ICAPE2', keep=True),
    Cell('IDDR', port_attrs={'C': ['clkbuf_sink']}),
    Cell('IDDR_2CLK', port_attrs={'C': ['clkbuf_sink'], 'CB': ['clkbuf_sink']}),
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
    Cell('ISERDESE2', port_attrs={
        'CLK': ['clkbuf_sink'],
        'CLKB': ['clkbuf_sink'],
        'OCLK': ['clkbuf_sink'],
        'OCLKB': ['clkbuf_sink'],
        'CLKDIV': ['clkbuf_sink'],
        'CLKDIVP': ['clkbuf_sink'],
    }),
    Cell('KEEPER'),
    Cell('LDCE'),
    Cell('LDPE'),
    # Cell('LUT1'),
    # Cell('LUT2'),
    # Cell('LUT3'),
    # Cell('LUT4'),
    # Cell('LUT5'),
    # Cell('LUT6'),
    #Cell('LUT6_2'),
    Cell('MMCME2_ADV'),
    Cell('MMCME2_BASE'),
    # Cell('MUXF7'),
    # Cell('MUXF8'),
    # Cell('OBUF', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('OBUFT', port_attrs={'O': ['iopad_external_pin']}),
    Cell('OBUFTDS', port_attrs={'O': ['iopad_external_pin'], 'OB': ['iopad_external_pin']}),
    Cell('ODDR', port_attrs={'C': ['clkbuf_sink']}),
    Cell('ODELAYE2', port_attrs={'C': ['clkbuf_sink']}),
    Cell('OSERDESE2', port_attrs={'CLK': ['clkbuf_sink'], 'CLKDIV': ['clkbuf_sink']}),
    Cell('OUT_FIFO', port_attrs={'RDCLK': ['clkbuf_sink'], 'WRCLK': ['clkbuf_sink']}),
    Cell('PHASER_IN'),
    Cell('PHASER_IN_PHY'),
    Cell('PHASER_OUT'),
    Cell('PHASER_OUT_PHY'),
    Cell('PHASER_REF'),
    Cell('PHY_CONTROL'),
    Cell('PLLE2_ADV'),
    Cell('PLLE2_BASE'),
    Cell('PS7', keep=True),
    Cell('PULLDOWN'),
    Cell('PULLUP'),
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
    Cell('RAM64X2S', port_attrs={'WCLK': ['clkbuf_sink']}),
    # Cell('RAMB18E1', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),
    # Cell('RAMB36E1', port_attrs={'CLKARDCLK': ['clkbuf_sink'], 'CLKBWRCLK': ['clkbuf_sink']}),
    Cell('ROM128X1'),
    Cell('ROM256X1'),
    Cell('ROM32X1'),
    Cell('ROM64X1'),
    #Cell('SRL16E', port_attrs={'CLK': ['clkbuf_sink']}),
    #Cell('SRLC32E', port_attrs={'CLK': ['clkbuf_sink']}),
    Cell('STARTUPE2', keep=True),
    Cell('USR_ACCESSE2'),
    Cell('XADC'),
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
                            for attr in cell.port_attrs.get(port, []):
                                outf.write('    (* {} *)\n'.format(attr))
                            outf.write('    {} {};\n'.format(kind, port))
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
    parser = ArgumentParser(description='Extract Xilinx blackbox cell definitions from Vivado.')
    parser.add_argument('vivado_dir', nargs='?', default='/opt/Xilinx/Vivado/2018.1')
    args = parser.parse_args()

    dirs = [
        os.path.join(args.vivado_dir, 'data/verilog/src/xeclib'),
        os.path.join(args.vivado_dir, 'data/verilog/src/retarget'),
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
