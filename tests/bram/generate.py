#!/usr/bin/env python3

import argparse
import os
import sys
import random

debug_mode = False

def create_bram(dsc_f, sim_f, ref_f, tb_f, k1, k2, or_next):
    while True:
        init = 0 # random.randrange(2)
        abits  = random.randrange(1, 8)
        dbits  = random.randrange(1, 8)
        groups = random.randrange(2, 5)

        if random.randrange(2):
            abits = 2 ** random.randrange(1, 4)
        if random.randrange(2):
            dbits = 2 ** random.randrange(1, 4)

        while True:
            wrmode = [ random.randrange(0, 2) for i in range(groups) ]
            if wrmode.count(1) == 0: continue
            if wrmode.count(0) == 0: continue
            break

        if random.randrange(2):
            maxpol = 4
            maxtransp = 1
            maxclocks = 4
        else:
            maxpol = None
            clkpol = random.randrange(4)
            maxtransp = 2
            maxclocks = 1

        def generate_enable(i):
            if wrmode[i]:
                v = 2 ** random.randrange(0, 4)
                while dbits < v or dbits % v != 0:
                    v //= 2
                return v
            return 0

        def generate_transp(i):
            if wrmode[i] == 0:
                return random.randrange(maxtransp)
            return 0

        def generate_clkpol(i):
            if maxpol is None:
                return clkpol
            return random.randrange(maxpol)

        ports  = [ random.randrange(1, 3)           for i in range(groups) ]
        enable = [ generate_enable(i)               for i in range(groups) ]
        transp = [ generate_transp(i)               for i in range(groups) ]
        clocks = [ random.randrange(maxclocks)+1    for i in range(groups) ]
        clkpol = [ generate_clkpol(i)               for i in range(groups) ]
        break

    print("bram bram_%02d_%02d" % (k1, k2), file=dsc_f)
    print("  init %d" % init, file=dsc_f)
    print("  abits %d" % abits, file=dsc_f)
    print("  dbits %d" % dbits, file=dsc_f)
    print("  groups %d" % groups, file=dsc_f)
    print("  ports  %s" % " ".join(["%d" % i for i in ports]), file=dsc_f)
    print("  wrmode %s" % " ".join(["%d" % i for i in wrmode]), file=dsc_f)
    print("  enable %s" % " ".join(["%d" % i for i in enable]), file=dsc_f)
    print("  transp %s" % " ".join(["%d" % i for i in transp]), file=dsc_f)
    print("  clocks %s" % " ".join(["%d" % i for i in clocks]), file=dsc_f)
    print("  clkpol %s" % " ".join(["%d" % i for i in clkpol]), file=dsc_f)
    print("endbram", file=dsc_f)
    print("match bram_%02d_%02d" % (k1, k2), file=dsc_f)
    if random.randrange(2):
        non_zero_enables = [chr(ord('A') + i) for i in range(len(enable)) if enable[i]]
        if len(non_zero_enables):
            print("  shuffle_enable %c" % random.choice(non_zero_enables), file=dsc_f)
    if or_next:
        print("  or_next_if_better", file=dsc_f)
    print("endmatch", file=dsc_f)

    states = set()
    v_ports = set()
    v_stmts = list()
    v_always = dict()

    tb_decls = list()
    tb_clocks = list()
    tb_addr = list()
    tb_din = list()
    tb_dout = list()
    tb_addrlist = list()

    for i in range(10):
        tb_addrlist.append(random.randrange(1048576))

    t = random.randrange(1048576)
    for i in range(10):
        tb_addrlist.append(t ^ (1 << i))

    v_stmts.append("(* nomem2reg *) reg [%d:0] memory [0:%d];" % (dbits-1, 2**abits-1))

    portindex = 0
    last_always_hdr = (-1, "")

    for p1 in range(groups):
        for p2 in range(ports[p1]):
            pf = "%c%d" % (chr(ord("A") + p1), p2 + 1)
            portindex += 1

            v_stmts.append("`ifndef SYNTHESIS")
            v_stmts.append("  event UPDATE_%s;" % pf)
            v_stmts.append("`endif")

            if clocks[p1] and not ("CLK%d" % clocks[p1]) in v_ports:
                v_ports.add("CLK%d" % clocks[p1])
                v_stmts.append("input CLK%d;" % clocks[p1])
                tb_decls.append("reg CLK%d = 0;" % clocks[p1])
                tb_clocks.append("CLK%d" % clocks[p1])

            v_ports.add("%sADDR" % pf)
            v_stmts.append("input [%d:0] %sADDR;" % (abits-1, pf))
            if transp[p1]:
                v_stmts.append("reg [%d:0] %sADDR_Q;" % (abits-1, pf))
            tb_decls.append("reg [%d:0] %sADDR;" % (abits-1, pf))
            tb_addr.append("%sADDR" % pf)

            v_ports.add("%sDATA" % pf)
            v_stmts.append("%s [%d:0] %sDATA;" % ("input" if wrmode[p1] else "output reg", dbits-1, pf))

            if wrmode[p1]:
                tb_decls.append("reg [%d:0] %sDATA;" % (dbits-1, pf))
                tb_din.append("%sDATA" % pf)
            else:
                tb_decls.append("wire [%d:0] %sDATA;" % (dbits-1, pf))
                tb_decls.append("wire [%d:0] %sDATA_R;" % (dbits-1, pf))
                tb_dout.append("%sDATA" % pf)

            if wrmode[p1] and enable[p1]:
                v_ports.add("%sEN" % pf)
                v_stmts.append("input [%d:0] %sEN;" % (enable[p1]-1, pf))
                tb_decls.append("reg [%d:0] %sEN;" % (enable[p1]-1, pf))
                tb_din.append("%sEN" % pf)

            assign_op = "<="
            if clocks[p1] == 0:
                always_hdr = "always @* begin"
                assign_op = "="
            elif clkpol[p1] == 0:
                always_hdr = "always @(negedge CLK%d) begin" % clocks[p1]
            elif clkpol[p1] == 1:
                always_hdr = "always @(posedge CLK%d) begin" % clocks[p1]
            else:
                if not ("CP", clkpol[p1]) in states:
                    v_stmts.append("parameter CLKPOL%d = 0;" % clkpol[p1])
                    states.add(("CP", clkpol[p1]))
                if not ("CPW", clocks[p1], clkpol[p1]) in states:
                    v_stmts.append("wire CLK%d_CLKPOL%d = CLK%d == CLKPOL%d;" % (clocks[p1], clkpol[p1], clocks[p1], clkpol[p1]))
                    states.add(("CPW", clocks[p1], clkpol[p1]))
                always_hdr = "always @(posedge CLK%d_CLKPOL%d) begin" % (clocks[p1], clkpol[p1])

            if last_always_hdr[1] != always_hdr:
                last_always_hdr = (portindex, always_hdr)
                v_always[last_always_hdr] = list()

            if wrmode[p1]:
                for i in range(enable[p1]):
                    enrange = "[%d:%d]" % ((i+1)*dbits/enable[p1]-1, i*dbits/enable[p1])
                    v_always[last_always_hdr].append((portindex, pf, "if (%sEN[%d]) memory[%sADDR]%s = %sDATA%s;" % (pf, i, pf, enrange, pf, enrange)))
            elif transp[p1]:
                v_always[last_always_hdr].append((sum(ports)+1, pf, "%sADDR_Q %s %sADDR;" % (pf, assign_op, pf)))
                v_stmts.append("always @* %sDATA = memory[%sADDR_Q];" % (pf, pf))
            else:
                v_always[last_always_hdr].append((0, pf, "%sDATA %s memory[%sADDR];" % (pf, assign_op, pf)))

    for always_hdr in sorted(v_always):
        v_stmts.append(always_hdr[1])
        triggered_events = set()
        time_cursor = 0
        v_always[always_hdr].sort()
        for t, p, s in v_always[always_hdr]:
            if time_cursor != t or not p in triggered_events:
                v_stmts.append("  `ifndef SYNTHESIS")
                stmt = ""
                if time_cursor != t:
                    stmt += " #%d;" % (t-time_cursor)
                    time_cursor = t
                if not p in triggered_events:
                    stmt += (" -> UPDATE_%s;" % p)
                    triggered_events.add(p)
                v_stmts.append("   %s" % stmt)
                v_stmts.append("  `endif")
            v_stmts.append("  %s" % s)
        v_stmts.append("end")

    print("module bram_%02d_%02d(%s);" % (k1, k2, ", ".join(v_ports)), file=sim_f)
    for stmt in v_stmts:
        print("  %s" % stmt, file=sim_f)
    print("endmodule", file=sim_f)

    print("module bram_%02d_%02d_ref(%s);" % (k1, k2, ", ".join(v_ports)), file=ref_f)
    for stmt in v_stmts:
        print("  %s" % stmt, file=ref_f)
    print("endmodule", file=ref_f)

    print("module bram_%02d_%02d_tb;" % (k1, k2), file=tb_f)
    for stmt in tb_decls:
        print("  %s" % stmt, file=tb_f)
    print("  bram_%02d_%02d uut (" % (k1, k2), file=tb_f)
    print("    " + ",\n    ".join([".%s(%s)" % (p, p) for p in (tb_clocks + tb_addr + tb_din + tb_dout)]), file=tb_f)
    print("  );", file=tb_f)
    print("  bram_%02d_%02d_ref ref (" % (k1, k2), file=tb_f)
    print("    " + ",\n    ".join([".%s(%s)" % (p, p) for p in (tb_clocks + tb_addr + tb_din)]) + ",", file=tb_f)
    print("    " + ",\n    ".join([".%s(%s_R)" % (p, p) for p in tb_dout]), file=tb_f)
    print("  );", file=tb_f)

    expr_dout = "{%s}" % ", ".join(tb_dout)
    expr_dout_ref = "{%s}" % ", ".join(i + "_R" for i in tb_dout)

    print("  wire error = %s !== %s;" % (expr_dout, expr_dout_ref), file=tb_f)

    print("  initial begin", file=tb_f)

    if debug_mode:
        print("    $dumpfile(`vcd_file);", file=tb_f)
        print("    $dumpvars(0, bram_%02d_%02d_tb);" % (k1, k2), file=tb_f)
    print("    #%d;" % (1000 + k2), file=tb_f)

    for p in (tb_clocks + tb_addr + tb_din):
        if p[-2:] == "EN":
            print("    %s <= ~0;" % p, file=tb_f)
        else:
            print("    %s <= 0;" % p, file=tb_f)
    print("    #1000;", file=tb_f)

    for v in [1, 0, 1, 0]:
        for p in tb_clocks:
            print("    %s = %d;" % (p, v), file=tb_f)
        print("    #1000;", file=tb_f)

    for i in range(20 if debug_mode else 100):
        if len(tb_clocks):
            c = random.choice(tb_clocks)
            print("    %s = !%s;" % (c, c), file=tb_f)
        print("    #100;", file=tb_f)
        print("    $display(\"bram_%02d_%02d %3d: %%b %%b %%s\", %s, %s, error ? \"ERROR\" : \"OK\");" %
                (k1, k2, i, expr_dout, expr_dout_ref), file=tb_f)
        for p in tb_din:
            print("    %s <= %d;" % (p, random.randrange(1048576)), file=tb_f)
        for p in tb_addr:
            print("    %s <= %d;" % (p, random.choice(tb_addrlist)), file=tb_f)
        print("    #900;", file=tb_f)

    print("  end", file=tb_f)
    print("endmodule", file=tb_f)

parser = argparse.ArgumentParser(formatter_class = argparse.ArgumentDefaultsHelpFormatter)
parser.add_argument('-S', '--seed',  type = int, help = 'seed for PRNG')
parser.add_argument('-c', '--count', type = int, default = 5, help = 'number of test cases to generate')
parser.add_argument('-d', '--debug', action='store_true')
args = parser.parse_args()

debug_mode = args.debug

if args.seed is not None:
    seed = args.seed
else:
    seed = (int(os.times()[4]*100) + os.getpid()) % 900000 + 100000

print("PRNG seed: %d" % seed)
random.seed(seed)

for k1 in range(args.count):
    dsc_f = open("temp/brams_%02d.txt" % k1, "w")
    sim_f = open("temp/brams_%02d.v" % k1, "w")
    ref_f = open("temp/brams_%02d_ref.v" % k1, "w")
    tb_f = open("temp/brams_%02d_tb.v" % k1, "w")

    for f in [sim_f, ref_f, tb_f]:
        print("`timescale 1 ns / 1 ns", file=f)

    lenk2 = 1 if debug_mode else 10
    for k2 in range(lenk2):
        create_bram(dsc_f, sim_f, ref_f, tb_f, k1, k2, random.randrange(2 if k2+1 < lenk2 else 1))

