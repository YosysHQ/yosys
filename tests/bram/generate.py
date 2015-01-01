#!/usr/bin/python

from __future__ import division
from __future__ import print_function

import sys
import random

def create_bram(dsc_f, sim_f, k1, k2):
    while True:
        init = random.randrange(2)
        abits  = random.randrange(1, 16)
        dbits  = random.randrange(1, 16)
        groups = random.randrange(5)

        if random.randrange(2):
            abits = 2 ** random.randrange(1, 4)
        if random.randrange(2):
            dbits = 2 ** random.randrange(1, 4)

        ports  = [ random.randrange(3) for i in range(groups) ]
        wrmode = [ random.randrange(2) for i in range(groups) ]
        enable = [ random.randrange(4) for i in range(groups) ]
        transp = [ random.randrange(4) for i in range(groups) ]
        clocks = [ random.randrange(4) for i in range(groups) ]
        clkpol = [ random.randrange(4) for i in range(groups) ]

        for p1 in range(groups):
            if wrmode[p1] == 0:
                enable[p1] = 0
            else:
                enable[p1] = 2**enable[p1]
                while dbits < enable[p1] or dbits % enable[p1] != 0:
                    enable[p1] //= 2

        config_ok = True
        if wrmode.count(1) <= ports.count(0): config_ok = False
        if wrmode.count(0) <= ports.count(0): config_ok = False
        if config_ok: break

    print('bram bram_%03d_%03d' % (k1, k2), file=dsc_f)
    print('  init %d' % init, file=dsc_f)
    print('  abits %d' % abits, file=dsc_f)
    print('  dbits %d' % dbits, file=dsc_f)
    print('  groups %d' % groups, file=dsc_f)
    print('  ports  %s' % " ".join(["%d" % i for i in ports]), file=dsc_f)
    print('  wrmode %s' % " ".join(["%d" % i for i in wrmode]), file=dsc_f)
    print('  enable %s' % " ".join(["%d" % i for i in enable]), file=dsc_f)
    print('  transp %s' % " ".join(["%d" % i for i in transp]), file=dsc_f)
    print('  clocks %s' % " ".join(["%d" % i for i in clocks]), file=dsc_f)
    print('  clkpol %s' % " ".join(["%d" % i for i in clkpol]), file=dsc_f)
    print('endbram', file=dsc_f)
    print('match bram_%03d_%03d' % (k1, k2), file=dsc_f)
    print('endmatch', file=dsc_f)

    states = set()
    v_ports = set()
    v_stmts = list()

    v_stmts.append("reg [%d:0] memory [0:%d];" % (dbits-1, 2**abits-1))

    for p1 in range(groups):
        for p2 in range(ports[p1]):
            pf = "%c%d" % (chr(ord('A') + p1), p2 + 1)

            if clocks[p1] and not ("CLK%d" % clocks[p1]) in v_ports:
                v_ports.add("CLK%d" % clocks[p1])
                v_stmts.append("input CLK%d;" % clocks[p1])

            v_ports.add("%sADDR" % pf)
            v_stmts.append("input [%d:0] %sADDR;" % (abits-1, pf))

            v_ports.add("%sDATA" % pf)
            v_stmts.append("%s [%d:0] %sDATA;" % ("input" if wrmode[p1] else "output reg", dbits-1, pf))

            if wrmode[p1] and enable[p1]:
                v_ports.add("%sEN" % pf)
                v_stmts.append("input [%d:0] %sEN;" % (enable[p1]-1, pf))

            assign_op = "<="
            if clocks[p1] == 0:
                v_stmts.append("always @* begin")
                assign_op = "="
            elif clkpol[p1] == 0:
                v_stmts.append("always @(negedge CLK%d) begin" % clocks[p1])
            elif clkpol[p1] == 1:
                v_stmts.append("always @(posedge CLK%d) begin" % clocks[p1])
            else:
                if not ('CP', clkpol[p1]) in states:
                    v_stmts.append("parameter CLKPOL%d = 0;" % clkpol[p1])
                    states.add(('CP', clkpol[p1]))
                if not ('CPW', clocks[p1], clkpol[p1]) in states:
                    v_stmts.append("wire CLK%d_CLKPOL%d = CLK%d == CLKPOL%d;" % (clocks[p1], clkpol[p1], clocks[p1], clkpol[p1]))
                    states.add(('CPW', clocks[p1], clkpol[p1]))
                v_stmts.append("always @(posedge CLK%d_CLKPOL%d) begin" % (clocks[p1], clkpol[p1]))

            if wrmode[p1]:
                for i in range(enable[p1]):
                    enrange = "[%d:%d]" % ((i+1)*dbits/enable[p1]-1, i*dbits/enable[p1])
                    v_stmts.append("  if (%sEN[%d]) memory[%sADDR]%s %s %sDATA%s;" % (pf, i, pf, enrange, assign_op, pf, enrange))
            else:
                v_stmts.append("  %sDATA %s memory[%sADDR];" % (pf, assign_op, pf))
            v_stmts.append("end")

    print('module bram_%03d_%03d(%s);' % (k1, k2, ", ".join(v_ports)), file=sim_f)
    for stmt in v_stmts:
        print('  %s' % stmt, file=sim_f)
    print('endmodule', file=sim_f)

for k1 in range(10):
    dsc_f = file('temp/brams_%03d.txt' % k1, 'w');
    sim_f = file('temp/brams_%03d.v' % k1, 'w');

    for k2 in range(10):
        create_bram(dsc_f, sim_f, k1, k2)

    dsc_f.close()
    sim_f.close()

