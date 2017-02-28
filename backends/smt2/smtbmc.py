#!/usr/bin/env python3
#
# yosys -- Yosys Open SYnthesis Suite
#
# Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#

import os, sys, getopt, re
##yosys-sys-path##
from smtio import SmtIo, SmtOpts, MkVcd
from collections import defaultdict

got_topt = False
skip_steps = 0
step_size = 1
num_steps = 20
append_steps = 0
vcdfile = None
cexfile = None
aimfile = None
aiwfile = None
aigheader = True
vlogtbfile = None
inconstr = list()
outconstr = None
gentrace = False
covermode = False
tempind = False
dumpall = False
assume_skipped = None
final_only = False
topmod = None
noinfo = False
so = SmtOpts()


def usage():
    print("""
yosys-smtbmc [options] <yosys_smt2_output>

    -t <num_steps>
    -t <skip_steps>:<num_steps>
    -t <skip_steps>:<step_size>:<num_steps>
        default: skip_steps=0, step_size=1, num_steps=20

    -g
        generate an arbitrary trace that satisfies
        all assertions and assumptions.

    -i
        instead of BMC run temporal induction

    -c
        instead of regular BMC run cover analysis

    -m <module_name>
        name of the top module

    --smtc <constr_filename>
        read constraints file

    --cex <cex_filename>
        read cex file as written by ABC's "write_cex -n"

    --aig <prefix>
        read AIGER map file (as written by Yosys' "write_aiger -map")
        and AIGER witness file. The file names are <prefix>.aim for
        the map file and <prefix>.aiw for the witness file.

    --aig <aim_filename>:<aiw_filename>
        like above, but for map files and witness files that do not
        share a filename prefix (or use differen file extensions).

    --aig-noheader
        the AIGER witness file does not include the status and
        properties lines.

    --noinfo
        only run the core proof, do not collect and print any
        additional information (e.g. which assert failed)

    --final-only
        only check final constraints, assume base case

    --assume-skipped <start_step>
        assume asserts in skipped steps in BMC.
        no assumptions are created for skipped steps
        before <start_step>.

    --dump-vcd <vcd_filename>
        write trace to this VCD file
        (hint: use 'write_smt2 -wires' for maximum
        coverage of signals in generated VCD file)

    --dump-vlogtb <verilog_filename>
        write trace as Verilog test bench

    --dump-smtc <constr_filename>
        write trace as constraints file

    --dump-all
        when using -g or -i, create a dump file for each
        step. The character '%' is replaces in all dump
        filenames with the step number.

    --append <num_steps>
        add <num_steps> time steps at the end of the trace
        when creating a counter example (this additional time
        steps will still be constrained by assumtions)
""" + so.helpmsg())
    sys.exit(1)


try:
    opts, args = getopt.getopt(sys.argv[1:], so.shortopts + "t:igcm:", so.longopts +
            ["final-only", "assume-skipped=", "smtc=", "cex=", "aig=", "aig-noheader",
             "dump-vcd=", "dump-vlogtb=", "dump-smtc=", "dump-all", "noinfo", "append="])
except:
    usage()

for o, a in opts:
    if o == "-t":
        got_topt = True
        a = a.split(":")
        if len(a) == 1:
            num_steps = int(a[0])
        elif len(a) == 2:
            skip_steps = int(a[0])
            num_steps = int(a[1])
        elif len(a) == 3:
            skip_steps = int(a[0])
            step_size = int(a[1])
            num_steps = int(a[2])
        else:
            assert False
    elif o == "--assume-skipped":
        assume_skipped = int(a)
    elif o == "--final-only":
        final_only = True
    elif o == "--smtc":
        inconstr.append(a)
    elif o == "--cex":
        cexfile = a
    elif o == "--aig":
        if ":" in a:
            aimfile, aiwfile = a.split(":")
        else:
            aimfile = a + ".aim"
            aiwfile = a + ".aiw"
    elif o == "--aig-noheader":
        aigheader = False
    elif o == "--dump-vcd":
        vcdfile = a
    elif o == "--dump-vlogtb":
        vlogtbfile = a
    elif o == "--dump-smtc":
        outconstr = a
    elif o == "--dump-all":
        dumpall = True
    elif o == "--noinfo":
        noinfo = True
    elif o == "--append":
        append_steps = int(a)
    elif o == "-i":
        tempind = True
    elif o == "-g":
        gentrace = True
    elif o == "-c":
        covermode = True
    elif o == "-m":
        topmod = a
    elif so.handle(o, a):
        pass
    else:
        usage()

if len(args) != 1:
    usage()

if sum([tempind, gentrace, covermode]) > 1:
    usage()

constr_final_start = None
constr_asserts = defaultdict(list)
constr_assumes = defaultdict(list)
constr_write = list()

for fn in inconstr:
    current_states = None
    current_line = 0

    with open(fn, "r") as f:
        for line in f:
            current_line += 1

            if line.startswith("#"):
                continue

            tokens = line.split()

            if len(tokens) == 0:
                continue

            if tokens[0] == "initial":
                current_states = set()
                if not tempind:
                    current_states.add(0)
                continue

            if tokens[0] == "final":
                constr_final = True
                if len(tokens) == 1:
                    current_states = set(["final-%d" % i for i in range(0, num_steps+1)])
                    constr_final_start = 0
                elif len(tokens) == 2:
                    arg = abs(int(tokens[1]))
                    current_states = set(["final-%d" % i for i in range(arg, num_steps+1)])
                    constr_final_start = arg if constr_final_start is None else min(constr_final_start, arg)
                else:
                    assert False
                continue

            if tokens[0] == "state":
                current_states = set()
                if not tempind:
                    for token in tokens[1:]:
                        tok = token.split(":")
                        if len(tok) == 1:
                            current_states.add(int(token))
                        elif len(tok) == 2:
                            lower = int(tok[0])
                            if tok[1] == "*":
                                upper = num_steps
                            else:
                                upper = int(tok[1])
                            for i in range(lower, upper+1):
                                current_states.add(i)
                        else:
                            assert False
                continue

            if tokens[0] == "always":
                if len(tokens) == 1:
                    current_states = set(range(0, num_steps+1))
                elif len(tokens) == 2:
                    arg = abs(int(tokens[1]))
                    current_states = set(range(arg, num_steps+1))
                else:
                    assert False
                continue

            if tokens[0] == "assert":
                assert current_states is not None

                for state in current_states:
                    constr_asserts[state].append(("%s:%d" % (fn, current_line), " ".join(tokens[1:])))

                continue

            if tokens[0] == "assume":
                assert current_states is not None

                for state in current_states:
                    constr_assumes[state].append(("%s:%d" % (fn, current_line), " ".join(tokens[1:])))

                continue

            if tokens[0] == "write":
                constr_write.append(" ".join(tokens[1:]))
                continue

            if tokens[0] == "logic":
                so.logic = " ".join(tokens[1:])
                continue

            assert False


def get_constr_expr(db, state, final=False, getvalues=False):
    if final:
        if ("final-%d" % state) not in db:
            return ([], [], []) if getvalues else "true"
    else:
        if state not in db:
            return ([], [], []) if getvalues else "true"

    netref_regex = re.compile(r'(^|[( ])\[(-?[0-9]+:|)([^\]]*)\](?=[ )]|$)')

    def replace_netref(match):
        state_sel = match.group(2)

        if state_sel == "":
            st = state
        elif state_sel[0] == "-":
            st = state + int(state_sel[:-1])
        else:
            st = int(state_sel[:-1])

        expr = smt.net_expr(topmod, "s%d" % st, smt.get_path(topmod, match.group(3)))

        return match.group(1) + expr

    expr_list = list()
    for loc, expr in db[("final-%d" % state) if final else state]:
        actual_expr = netref_regex.sub(replace_netref, expr)
        if getvalues:
            expr_list.append((loc, expr, actual_expr))
        else:
            expr_list.append(actual_expr)

    if getvalues:
        loc_list, expr_list, acual_expr_list = zip(*expr_list)
        value_list = smt.get_list(acual_expr_list)
        return loc_list, expr_list, value_list

    if len(expr_list) == 0:
        return "true"

    if len(expr_list) == 1:
        return expr_list[0]

    return "(and %s)" % " ".join(expr_list)


smt = SmtIo(opts=so)

if noinfo and vcdfile is None and vlogtbfile is None and outconstr is None:
    smt.produce_models = False

def print_msg(msg):
    print("%s %s" % (smt.timestamp(), msg))
    sys.stdout.flush()

print_msg("Solver: %s" % (so.solver))

with open(args[0], "r") as f:
    for line in f:
        smt.write(line)

for line in constr_write:
    smt.write(line)

if topmod is None:
    topmod = smt.topmod

assert topmod is not None
assert topmod in smt.modinfo

if cexfile is not None:
    if not got_topt:
        assume_skipped = 0
        skip_steps = 0
        num_steps = 0

    with open(cexfile, "r") as f:
        cex_regex = re.compile(r'([^\[@=]+)(\[\d+\])?([^@=]*)(@\d+)=([01])')
        for entry in f.read().split():
            match = cex_regex.match(entry)
            assert match

            name, bit, extra_name, step, val = match.group(1), match.group(2), match.group(3), match.group(4), match.group(5)

            if extra_name != "":
                continue

            if name not in smt.modinfo[topmod].inputs:
                continue

            if bit is None:
                bit = 0
            else:
                bit = int(bit[1:-1])

            step = int(step[1:])
            val = int(val)

            if smt.modinfo[topmod].wsize[name] == 1:
                assert bit == 0
                smtexpr = "(= [%s] %s)" % (name, "true" if val else "false")
            else:
                smtexpr = "(= ((_ extract %d %d) [%s]) #b%d)" % (bit, bit, name, val)

            # print("cex@%d: %s" % (step, smtexpr))
            constr_assumes[step].append((cexfile, smtexpr))

            if not got_topt:
                skip_steps = max(skip_steps, step)
                num_steps = max(num_steps, step+1)

if aimfile is not None:
    input_map = dict()
    init_map = dict()
    latch_map = dict()

    if not got_topt:
        assume_skipped = 0
        skip_steps = 0
        num_steps = 0

    with open(aimfile, "r") as f:
        for entry in f.read().splitlines():
            entry = entry.split()

            if entry[0] == "input":
                input_map[int(entry[1])] = (entry[3], int(entry[2]))
                continue

            if entry[0] == "init":
                init_map[int(entry[1])] = (entry[3], int(entry[2]))
                continue

            if entry[0] in ["latch", "invlatch"]:
                latch_map[int(entry[1])] = (entry[3], int(entry[2]), entry[0] == "invlatch")
                continue

            if entry[0] in ["output", "wire"]:
                continue

            assert False

    with open(aiwfile, "r") as f:
        got_state = False
        got_ffinit = False
        step = 0

        if not aigheader:
            got_state = True

        for entry in f.read().splitlines():
            if len(entry) == 0 or entry[0] in "bcjfu.":
                continue

            if not got_state:
                got_state = True
                assert entry == "1"
                continue

            if not got_ffinit:
                got_ffinit = True
                if len(init_map) == 0:
                    for i in range(len(entry)):
                        if entry[i] == "x":
                            continue

                        if i in latch_map:
                            value = int(entry[i])
                            name = latch_map[i][0]
                            bitidx = latch_map[i][1]
                            invert = latch_map[i][2]

                            if invert:
                                value = 1 - value

                            path = smt.get_path(topmod, name)
                            width = smt.net_width(topmod, path)

                            if width == 1:
                                assert bitidx == 0
                                smtexpr = "(= [%s] %s)" % (name, "true" if value else "false")
                            else:
                                smtexpr = "(= ((_ extract %d %d) [%s]) #b%d)" % (bitidx, bitidx, name, value)

                            constr_assumes[0].append((cexfile, smtexpr))
                continue

            for i in range(len(entry)):
                if entry[i] == "x":
                    continue

                if (step == 0) and (i in init_map):
                    value = int(entry[i])
                    name = init_map[i][0]
                    bitidx = init_map[i][1]

                    path = smt.get_path(topmod, name)

                    if not smt.net_exists(topmod, path):
                        match = re.match(r"(.*)\[(\d+)\]$", path[-1])
                        if match:
                            path[-1] = match.group(1)
                            addr = int(match.group(2))

                        if not match or not smt.mem_exists(topmod, path):
                            print_msg("Ignoring init value for unknown net: %s" % (name))
                            continue

                        meminfo = smt.mem_info(topmod, path)
                        smtexpr = "(select [%s] #b%s)" % (".".join(path), bin(addr)[2:].zfill(meminfo[0]))
                        width = meminfo[1]

                    else:
                        smtexpr = "[%s]" % name
                        width = smt.net_width(topmod, path)

                    if width == 1:
                        assert bitidx == 0
                        smtexpr = "(= %s %s)" % (smtexpr, "true" if value else "false")
                    else:
                        smtexpr = "(= ((_ extract %d %d) %s) #b%d)" % (bitidx, bitidx, smtexpr, value)

                    constr_assumes[0].append((cexfile, smtexpr))

                if i in input_map:
                    value = int(entry[i])
                    name = input_map[i][0]
                    bitidx = input_map[i][1]

                    path = smt.get_path(topmod, name)
                    width = smt.net_width(topmod, path)

                    if width == 1:
                        assert bitidx == 0
                        smtexpr = "(= [%s] %s)" % (name, "true" if value else "false")
                    else:
                        smtexpr = "(= ((_ extract %d %d) [%s]) #b%d)" % (bitidx, bitidx, name, value)

                    constr_assumes[step].append((cexfile, smtexpr))

            if not got_topt:
                skip_steps = max(skip_steps, step)
                num_steps = max(num_steps, step+1)
            step += 1

def write_vcd_trace(steps_start, steps_stop, index):
    filename = vcdfile.replace("%", index)
    print_msg("Writing trace to VCD file: %s" % (filename))

    with open(filename, "w") as vcd_file:
        vcd = MkVcd(vcd_file)
        path_list = list()

        for netpath in sorted(smt.hiernets(topmod)):
            hidden_net = False
            for n in netpath:
                if n.startswith("$"):
                    hidden_net = True
            if not hidden_net:
                vcd.add_net([topmod] + netpath, smt.net_width(topmod, netpath))
                path_list.append(netpath)

        mem_trace_data = dict()
        for mempath in sorted(smt.hiermems(topmod)):
            abits, width, rports, wports = smt.mem_info(topmod, mempath)

            expr_id = list()
            expr_list = list()
            for i in range(steps_start, steps_stop):
                for j in range(rports):
                    expr_id.append(('R', i-steps_start, j, 'A'))
                    expr_id.append(('R', i-steps_start, j, 'D'))
                    expr_list.append(smt.mem_expr(topmod, "s%d" % i, mempath, "R%dA" % j))
                    expr_list.append(smt.mem_expr(topmod, "s%d" % i, mempath, "R%dD" % j))
                for j in range(wports):
                    expr_id.append(('W', i-steps_start, j, 'A'))
                    expr_id.append(('W', i-steps_start, j, 'D'))
                    expr_id.append(('W', i-steps_start, j, 'M'))
                    expr_list.append(smt.mem_expr(topmod, "s%d" % i, mempath, "W%dA" % j))
                    expr_list.append(smt.mem_expr(topmod, "s%d" % i, mempath, "W%dD" % j))
                    expr_list.append(smt.mem_expr(topmod, "s%d" % i, mempath, "W%dM" % j))

            rdata = list()
            wdata = list()
            addrs = set()

            for eid, edat in zip(expr_id, smt.get_list(expr_list)):
                t, i, j, f = eid

                if t == 'R':
                    c = rdata
                elif t == 'W':
                    c = wdata
                else:
                    assert False

                while len(c) <= i:
                    c.append(list())
                c = c[i]

                while len(c) <= j:
                    c.append(dict())
                c = c[j]

                c[f] = smt.bv2bin(edat)

                if f == 'A':
                    addrs.add(c[f])

            for addr in addrs:
                tdata = list()
                data = ["x"] * width
                gotread = False

                assert len(rdata) == len(wdata)

                for i in range(len(wdata)):
                    if not gotread:
                        for j_data in rdata[i]:
                            if j_data["A"] == addr:
                                data = list(j_data["D"])
                                gotread = True
                                break

                        if gotread:
                            buf = data[:]
                            for i in reversed(range(len(tdata))):
                                for k in range(width):
                                    if tdata[i][k] == "x":
                                        tdata[i][k] = buf[k]
                                    else:
                                        buf[k] = tdata[i][k]

                    tdata.append(data[:])

                    for j_data in wdata[i]:
                        if j_data["A"] != addr:
                            continue

                        D = j_data["D"]
                        M = j_data["M"]

                        for k in range(width):
                            if M[k] == "1":
                                data[k] = D[k]

                assert len(tdata) == len(rdata)

                netpath = mempath[:]
                netpath[-1] += "<%0*x>" % ((len(addr)+3) // 4, int(addr, 2))
                vcd.add_net([topmod] + netpath, width)

                for i in range(steps_start, steps_stop):
                    if i not in mem_trace_data:
                        mem_trace_data[i] = list()
                    mem_trace_data[i].append((netpath, "".join(tdata[i-steps_start])))

        for i in range(steps_start, steps_stop):
            vcd.set_time(i)
            value_list = smt.get_net_bin_list(topmod, path_list, "s%d" % i)
            for path, value in zip(path_list, value_list):
                vcd.set_net([topmod] + path, value)
            if i in mem_trace_data:
                for path, value in mem_trace_data[i]:
                    vcd.set_net([topmod] + path, value)

        vcd.set_time(steps_stop)


def write_vlogtb_trace(steps_start, steps_stop, index):
    filename = vlogtbfile.replace("%", index)
    print_msg("Writing trace to Verilog testbench: %s" % (filename))

    with open(filename, "w") as f:
        print("module testbench;", file=f)
        print("  reg [4095:0] vcdfile;", file=f)
        print("  reg clock = 0, genclock = 1;", file=f)

        primary_inputs = list()
        clock_inputs = set()

        for name in smt.modinfo[topmod].inputs:
            if name in ["clk", "clock", "CLK", "CLOCK"]:
                clock_inputs.add(name)
            width = smt.modinfo[topmod].wsize[name]
            primary_inputs.append((name, width))

        for name, width in primary_inputs:
            if name in clock_inputs:
                print("  wire [%d:0] PI_%s = clock;" % (width-1, name), file=f)
            else:
                print("  reg [%d:0] PI_%s;" % (width-1, name), file=f)

        print("  %s UUT (" % topmod, file=f)
        print(",\n".join("    .{name}(PI_{name})".format(name=name) for name, _ in primary_inputs), file=f)
        print("  );", file=f)

        print("  initial begin", file=f)
        print("    if ($value$plusargs(\"vcd=%s\", vcdfile)) begin", file=f)
        print("      $dumpfile(vcdfile);", file=f)
        print("      $dumpvars(0, testbench);", file=f)
        print("    end", file=f)
        print("    while (genclock) begin", file=f)
        print("      #5; clock = 0;", file=f)
        print("      #5; clock = 1;", file=f)
        print("    end", file=f)
        print("  end", file=f)

        print("  initial begin", file=f)

        regs = sorted(smt.hiernets(topmod, regs_only=True))
        regvals = smt.get_net_bin_list(topmod, regs, "s%d" % steps_start)

        print("    #1;", file=f)
        for reg, val in zip(regs, regvals):
            hidden_net = False
            for n in reg:
                if n.startswith("$"):
                    hidden_net = True
            print("    %sUUT.%s = %d'b%s;" % ("// " if hidden_net else "", ".".join(reg), len(val), val), file=f)

        mems = sorted(smt.hiermems(topmod))
        for mempath in mems:
            abits, width, rports, wports = smt.mem_info(topmod, mempath)

            addr_expr_list = list()
            data_expr_list = list()
            for i in range(steps_start, steps_stop):
                for j in range(rports):
                    addr_expr_list.append(smt.mem_expr(topmod, "s%d" % i, mempath, "R%dA" % j))
                    data_expr_list.append(smt.mem_expr(topmod, "s%d" % i, mempath, "R%dD" % j))

            addr_list = smt.get_list(addr_expr_list)
            data_list = smt.get_list(data_expr_list)

            addr_data = dict()
            for addr, data in zip(addr_list, data_list):
                addr = smt.bv2bin(addr)
                data = smt.bv2bin(data)
                if addr not in addr_data:
                    addr_data[addr] = data

            for addr, data in addr_data.items():
                print("    UUT.%s[%d'b%s] = %d'b%s;" % (".".join(mempath), len(addr), addr, len(data), data), file=f)

        for i in range(steps_start, steps_stop):
            pi_names = [[name] for name, _ in primary_inputs if name not in clock_inputs]
            pi_values = smt.get_net_bin_list(topmod, pi_names, "s%d" % i)

            print("    #1;", file=f)
            print("    // state %d" % i, file=f)
            if i > 0:
                print("    @(posedge clock);", file=f)
            for name, val in zip(pi_names, pi_values):
                print("    PI_%s <= %d'b%s;" % (".".join(name), len(val), val), file=f)

        print("    genclock = 0;", file=f)
        print("  end", file=f)

        print("endmodule", file=f)


def write_constr_trace(steps_start, steps_stop, index):
    filename = outconstr.replace("%", index)
    print_msg("Writing trace to constraints file: %s" % (filename))

    with open(filename, "w") as f:
        primary_inputs = list()

        for name in smt.modinfo[topmod].inputs:
            width = smt.modinfo[topmod].wsize[name]
            primary_inputs.append((name, width))

        if steps_start == 0:
            print("initial", file=f)
        else:
            print("state %d" % steps_start, file=f)

        regnames = sorted(smt.hiernets(topmod, regs_only=True))
        regvals = smt.get_net_list(topmod, regnames, "s%d" % steps_start)

        for name, val in zip(regnames, regvals):
            print("assume (= [%s] %s)" % (".".join(name), val), file=f)

        mems = sorted(smt.hiermems(topmod))
        for mempath in mems:
            abits, width, rports, wports = smt.mem_info(topmod, mempath)

            addr_expr_list = list()
            data_expr_list = list()
            for i in range(steps_start, steps_stop):
                for j in range(rports):
                    addr_expr_list.append(smt.mem_expr(topmod, "s%d" % i, mempath, "R%dA" % j))
                    data_expr_list.append(smt.mem_expr(topmod, "s%d" % i, mempath, "R%dD" % j))

            addr_list = smt.get_list(addr_expr_list)
            data_list = smt.get_list(data_expr_list)

            addr_data = dict()
            for addr, data in zip(addr_list, data_list):
                if addr not in addr_data:
                    addr_data[addr] = data

            for addr, data in addr_data.items():
                print("assume (= (select [%s] %s) %s)" % (".".join(mempath), addr, data), file=f)

        for k in range(steps_start, steps_stop):
            print("", file=f)
            print("state %d" % k, file=f)

            pi_names = [[name] for name, _ in sorted(primary_inputs)]
            pi_values = smt.get_net_list(topmod, pi_names, "s%d" % k)

            for name, val in zip(pi_names, pi_values):
                print("assume (= [%s] %s)" % (".".join(name), val), file=f)


def write_trace(steps_start, steps_stop, index):
    if vcdfile is not None:
        write_vcd_trace(steps_start, steps_stop, index)

    if vlogtbfile is not None:
        write_vlogtb_trace(steps_start, steps_stop, index)

    if outconstr is not None:
        write_constr_trace(steps_start, steps_stop, index)


def print_failed_asserts_worker(mod, state, path, extrainfo):
    assert mod in smt.modinfo
    found_failed_assert = False

    if smt.get("(|%s_a| %s)" % (mod, state)) in ["true", "#b1"]:
        return

    for cellname, celltype in smt.modinfo[mod].cells.items():
        if print_failed_asserts_worker(celltype, "(|%s_h %s| %s)" % (mod, cellname, state), path + "." + cellname, extrainfo):
            found_failed_assert = True

    for assertfun, assertinfo in smt.modinfo[mod].asserts.items():
        if smt.get("(|%s| %s)" % (assertfun, state)) in ["false", "#b0"]:
            print_msg("Assert failed in %s: %s%s" % (path, assertinfo, extrainfo))
            found_failed_assert = True

    return found_failed_assert


def print_failed_asserts(state, final=False, extrainfo=""):
    if noinfo: return
    loc_list, expr_list, value_list = get_constr_expr(constr_asserts, state, final=final, getvalues=True)
    found_failed_assert = False

    for loc, expr, value in zip(loc_list, expr_list, value_list):
        if smt.bv2int(value) == 0:
            print_msg("Assert %s failed: %s%s" % (loc, expr, extrainfo))
            found_failed_assert = True

    if not final:
        if print_failed_asserts_worker(topmod, "s%d" % state, topmod, extrainfo):
            found_failed_assert = True

    return found_failed_assert


def print_anyconsts_worker(mod, state, path):
    assert mod in smt.modinfo

    for cellname, celltype in smt.modinfo[mod].cells.items():
        print_anyconsts_worker(celltype, "(|%s_h %s| %s)" % (mod, cellname, state), path + "." + cellname)

    for fun, info in smt.modinfo[mod].anyconsts.items():
        print_msg("Value for anyconst in %s (%s): %d" % (path, info, smt.bv2int(smt.get("(|%s| %s)" % (fun, state)))))


def print_anyconsts(state):
    if noinfo: return
    print_anyconsts_worker(topmod, "s%d" % state, topmod)


def get_cover_list(mod, base):
    assert mod in smt.modinfo

    cover_expr = list()
    cover_desc = list()

    for expr, desc in smt.modinfo[mod].covers.items():
        cover_expr.append("(ite (|%s| %s) #b1 #b0)" % (expr, base))
        cover_desc.append(desc)

    for cell, submod in smt.modinfo[mod].cells.items():
        e, d = get_cover_list(submod, "(|%s_h %s| %s)" % (mod, cell, base))
        cover_expr += e
        cover_desc += d

    return cover_expr, cover_desc


if tempind:
    retstatus = False
    skip_counter = step_size
    for step in range(num_steps, -1, -1):
        smt.write("(declare-fun s%d () |%s_s|)" % (step, topmod))
        smt.write("(assert (|%s_u| s%d))" % (topmod, step))
        smt.write("(assert (|%s_h| s%d))" % (topmod, step))
        smt.write("(assert (not (|%s_is| s%d)))" % (topmod, step))
        smt.write("(assert %s)" % get_constr_expr(constr_assumes, step))

        if step == num_steps:
            smt.write("(assert (not (and (|%s_a| s%d) %s)))" % (topmod, step, get_constr_expr(constr_asserts, step)))

        else:
            smt.write("(assert (|%s_t| s%d s%d))" % (topmod, step, step+1))
            smt.write("(assert (|%s_a| s%d))" % (topmod, step))
            smt.write("(assert %s)" % get_constr_expr(constr_asserts, step))

        if step > num_steps-skip_steps:
            print_msg("Skipping induction in step %d.." % (step))
            continue

        skip_counter += 1
        if skip_counter < step_size:
            print_msg("Skipping induction in step %d.." % (step))
            continue

        skip_counter = 0
        print_msg("Trying induction in step %d.." % (step))

        if smt.check_sat() == "sat":
            if step == 0:
                print("%s Temporal induction failed!" % smt.timestamp())
                print_anyconsts(num_steps)
                print_failed_asserts(num_steps)
                write_trace(step, num_steps+1, '%')

            elif dumpall:
                print_anyconsts(num_steps)
                print_failed_asserts(num_steps)
                write_trace(step, num_steps+1, "%d" % step)

        else:
            print("%s Temporal induction successful." % smt.timestamp())
            retstatus = True
            break

elif covermode:
    cover_expr, cover_desc = get_cover_list(topmod, "state")
    cover_mask = "1" * len(cover_desc)

    if len(cover_expr) > 1:
        cover_expr = "(concat %s)" % " ".join(cover_expr)
    elif len(cover_expr) == 1:
        cover_expr = cover_expr[0]
    else:
        cover_expr = "#b0"

    coveridx = 0
    smt.write("(define-fun covers_0 ((state |%s_s|)) (_ BitVec %d) %s)" % (topmod, len(cover_desc), cover_expr))

    step = 0
    retstatus = False
    found_failed_assert = False

    assert step_size == 1

    while step < num_steps:
        smt.write("(declare-fun s%d () |%s_s|)" % (step, topmod))
        smt.write("(assert (|%s_u| s%d))" % (topmod, step))
        smt.write("(assert (|%s_h| s%d))" % (topmod, step))
        smt.write("(assert %s)" % get_constr_expr(constr_assumes, step))

        if step == 0:
            smt.write("(assert (|%s_i| s0))" % (topmod))
            smt.write("(assert (|%s_is| s0))" % (topmod))

        else:
            smt.write("(assert (|%s_t| s%d s%d))" % (topmod, step-1, step))
            smt.write("(assert (not (|%s_is| s%d)))" % (topmod, step))

        while "1" in cover_mask:
            print_msg("Checking cover reachability in step %d.." % (step))
            smt.write("(push 1)")
            smt.write("(assert (distinct (covers_%d s%d) #b%s))" % (coveridx, step, "0" * len(cover_desc)))

            if smt.check_sat() == "unsat":
                smt.write("(pop 1)")
                break

            if append_steps > 0:
                for i in range(step+1, step+1+append_steps):
                    print_msg("Appending additional step %d." % i)
                    smt.write("(declare-fun s%d () |%s_s|)" % (i, topmod))
                    smt.write("(assert (not (|%s_is| s%d)))" % (topmod, i))
                    smt.write("(assert (|%s_u| s%d))" % (topmod, i))
                    smt.write("(assert (|%s_h| s%d))" % (topmod, i))
                    smt.write("(assert (|%s_t| s%d s%d))" % (topmod, i-1, i))
                    smt.write("(assert %s)" % get_constr_expr(constr_assumes, i))
                print_msg("Re-solving with appended steps..")
                assert smt.check_sat() == "sat"

            reached_covers = smt.bv2bin(smt.get("(covers_%d s%d)" % (coveridx, step)))
            assert len(reached_covers) == len(cover_desc)

            new_cover_mask = []

            for i in range(len(reached_covers)):
                if reached_covers[i] == "0":
                    new_cover_mask.append(cover_mask[i])
                    continue

                print_msg("Reached cover statement at %s in step %d." % (cover_desc[i], step))
                new_cover_mask.append("0")

            cover_mask = "".join(new_cover_mask)

            for i in range(step+1+append_steps):
                if print_failed_asserts(i, extrainfo=" (step %d)" % i):
                    found_failed_assert = True

            write_trace(0, step+1+append_steps, "%d" % coveridx)

            if found_failed_assert:
                break

            coveridx += 1
            smt.write("(pop 1)")
            smt.write("(define-fun covers_%d ((state |%s_s|)) (_ BitVec %d) (bvand (covers_%d state) #b%s))" % (coveridx, topmod, len(cover_desc), coveridx-1, cover_mask))

        if found_failed_assert:
            break

        if "1" not in cover_mask:
            retstatus = True
            break

        step += 1

    if "1" in cover_mask:
        for i in range(len(cover_mask)):
            if cover_mask[i] == "1":
                print_msg("Unreached cover statement at %s." % cover_desc[i])

else:  # not tempind, covermode
    step = 0
    retstatus = True
    while step < num_steps:
        smt.write("(declare-fun s%d () |%s_s|)" % (step, topmod))
        smt.write("(assert (|%s_u| s%d))" % (topmod, step))
        smt.write("(assert (|%s_h| s%d))" % (topmod, step))
        smt.write("(assert %s)" % get_constr_expr(constr_assumes, step))

        if step == 0:
            smt.write("(assert (|%s_i| s0))" % (topmod))
            smt.write("(assert (|%s_is| s0))" % (topmod))

        else:
            smt.write("(assert (|%s_t| s%d s%d))" % (topmod, step-1, step))
            smt.write("(assert (not (|%s_is| s%d)))" % (topmod, step))

        if step < skip_steps:
            if assume_skipped is not None and step >= assume_skipped:
                print_msg("Skipping step %d (and assuming pass).." % (step))
                smt.write("(assert (|%s_a| s%d))" % (topmod, step))
                smt.write("(assert %s)" % get_constr_expr(constr_asserts, step))
            else:
                print_msg("Skipping step %d.." % (step))
            step += 1
            continue

        last_check_step = step
        for i in range(1, step_size):
            if step+i < num_steps:
                smt.write("(declare-fun s%d () |%s_s|)" % (step+i, topmod))
                smt.write("(assert (not (|%s_is| s%d)))" % (topmod, step+i))
                smt.write("(assert (|%s_u| s%d))" % (topmod, step+i))
                smt.write("(assert (|%s_h| s%d))" % (topmod, step+i))
                smt.write("(assert (|%s_t| s%d s%d))" % (topmod, step+i-1, step+i))
                smt.write("(assert %s)" % get_constr_expr(constr_assumes, step+i))
                last_check_step = step+i

        if not gentrace:
            if not final_only:
                if last_check_step == step:
                    print_msg("Checking asserts in step %d.." % (step))
                else:
                    print_msg("Checking asserts in steps %d to %d.." % (step, last_check_step))
                smt.write("(push 1)")

                smt.write("(assert (not (and %s)))" % " ".join(["(|%s_a| s%d)" % (topmod, i) for i in range(step, last_check_step+1)] +
                        [get_constr_expr(constr_asserts, i) for i in range(step, last_check_step+1)]))

                if smt.check_sat() == "sat":
                    print("%s BMC failed!" % smt.timestamp())
                    if append_steps > 0:
                        for i in range(last_check_step+1, last_check_step+1+append_steps):
                            print_msg("Appending additional step %d." % i)
                            smt.write("(declare-fun s%d () |%s_s|)" % (i, topmod))
                            smt.write("(assert (not (|%s_is| s%d)))" % (topmod, i))
                            smt.write("(assert (|%s_u| s%d))" % (topmod, i))
                            smt.write("(assert (|%s_h| s%d))" % (topmod, i))
                            smt.write("(assert (|%s_t| s%d s%d))" % (topmod, i-1, i))
                            smt.write("(assert %s)" % get_constr_expr(constr_assumes, i))
                        print_msg("Re-solving with appended steps..")
                        assert smt.check_sat() == "sat"
                    print_anyconsts(step)
                    for i in range(step, last_check_step+1):
                        print_failed_asserts(i)
                    write_trace(0, last_check_step+1+append_steps, '%')
                    retstatus = False
                    break

                smt.write("(pop 1)")

            if (constr_final_start is not None) or (last_check_step+1 != num_steps):
                for i in range(step, last_check_step+1):
                    smt.write("(assert (|%s_a| s%d))" % (topmod, i))
                    smt.write("(assert %s)" % get_constr_expr(constr_asserts, i))

            if constr_final_start is not None:
                for i in range(step, last_check_step+1):
                    if i < constr_final_start:
                        continue

                    print_msg("Checking final constraints in step %d.." % (i))
                    smt.write("(push 1)")

                    smt.write("(assert %s)" % get_constr_expr(constr_assumes, i, final=True))
                    smt.write("(assert (not %s))" % get_constr_expr(constr_asserts, i, final=True))

                    if smt.check_sat() == "sat":
                        print("%s BMC failed!" % smt.timestamp())
                        print_anyconsts(i)
                        print_failed_asserts(i, final=True)
                        write_trace(0, i+1, '%')
                        retstatus = False
                        break

                    smt.write("(pop 1)")
                if not retstatus:
                    break

        else:  # gentrace
            for i in range(step, last_check_step+1):
                smt.write("(assert (|%s_a| s%d))" % (topmod, i))
                smt.write("(assert %s)" % get_constr_expr(constr_asserts, i))

            print_msg("Solving for step %d.." % (last_check_step))
            if smt.check_sat() != "sat":
                print("%s No solution found!" % smt.timestamp())
                retstatus = False
                break

            elif dumpall:
                print_anyconsts(0)
                write_trace(0, last_check_step+1, "%d" % step)

        step += step_size

    if gentrace:
        print_anyconsts(0)
        write_trace(0, num_steps, '%')


smt.write("(exit)")
smt.wait()

print_msg("Status: %s" % ("PASSED" if retstatus else "FAILED (!)"))
sys.exit(0 if retstatus else 1)
