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

import sys, subprocess, re
from select import select
from time import time


hex_dict = {
    "0": "0000", "1": "0001", "2": "0010", "3": "0011",
    "4": "0100", "5": "0101", "6": "0110", "7": "0111",
    "8": "1000", "9": "1001", "A": "1010", "B": "1011",
    "C": "1100", "D": "1101", "E": "1110", "F": "1111",
    "a": "1010", "b": "1011", "c": "1100", "d": "1101",
    "e": "1110", "f": "1111"
}


class SmtModInfo:
    def __init__(self):
        self.inputs = set()
        self.outputs = set()
        self.registers = set()
        self.memories = dict()
        self.wires = set()
        self.wsize = dict()
        self.cells = dict()
        self.asserts = dict()
        self.anyconsts = dict()


class SmtIo:
    def __init__(self, solver=None, debug_print=None, debug_file=None, timeinfo=None, opts=None):
        if opts is not None:
            self.solver = opts.solver
            self.debug_print = opts.debug_print
            self.debug_file = opts.debug_file
            self.timeinfo = opts.timeinfo

        else:
            self.solver = "z3"
            self.debug_print = False
            self.debug_file = None
            self.timeinfo = True

        if solver is not None:
            self.solver = solver

        if debug_print is not None:
            self.debug_print = debug_print

        if debug_file is not None:
            self.debug_file = debug_file

        if timeinfo is not None:
            self.timeinfo = timeinfo

        if self.solver == "yices":
            popen_vargs = ['yices-smt2', '--incremental']

        if self.solver == "z3":
            popen_vargs = ['z3', '-smt2', '-in']

        if self.solver == "cvc4":
            popen_vargs = ['cvc4', '--incremental', '--lang', 'smt2']

        if self.solver == "mathsat":
            popen_vargs = ['mathsat']

        if self.solver == "boolector":
            self.declared_sorts = list()
            popen_vargs = ['boolector', '--smt2', '-i']

        self.p = subprocess.Popen(popen_vargs, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.start_time = time()

        self.modinfo = dict()
        self.curmod = None
        self.topmod = None

    def setup(self, logic="ALL", info=None):
        self.write("(set-logic %s)" % logic)
        if info is not None:
            self.write("(set-info :source |%s|)" % info)
            self.write("(set-info :smt-lib-version 2.5)")
            self.write("(set-info :category \"industrial\")")

    def timestamp(self):
        secs = int(time() - self.start_time)
        return "## %6d %3d:%02d:%02d " % (secs, secs // (60*60), (secs // 60) % 60, secs % 60)

    def write(self, stmt):
        stmt = stmt.strip()

        if self.solver == "boolector":
            if stmt.startswith("(declare-sort"):
                self.declared_sorts.append(stmt.split()[1])
                return
            for n in self.declared_sorts:
                stmt = stmt.replace(n, "(_ BitVec 16)")

        if self.debug_print:
            print("> %s" % stmt)

        if self.debug_file:
            print(stmt, file=self.debug_file)
            self.debug_file.flush()

        self.p.stdin.write(bytes(stmt + "\n", "ascii"))
        self.p.stdin.flush()

    def info(self, stmt):
        if not stmt.startswith("; yosys-smt2-"):
            return

        fields = stmt.split()

        if fields[1] == "yosys-smt2-module":
            self.curmod = fields[2]
            self.modinfo[self.curmod] = SmtModInfo()

        if fields[1] == "yosys-smt2-cell":
            self.modinfo[self.curmod].cells[fields[3]] = fields[2]

        if fields[1] == "yosys-smt2-topmod":
            self.topmod = fields[2]

        if fields[1] == "yosys-smt2-input":
            self.modinfo[self.curmod].inputs.add(fields[2])
            self.modinfo[self.curmod].wsize[fields[2]] = int(fields[3])

        if fields[1] == "yosys-smt2-output":
            self.modinfo[self.curmod].outputs.add(fields[2])
            self.modinfo[self.curmod].wsize[fields[2]] = int(fields[3])

        if fields[1] == "yosys-smt2-register":
            self.modinfo[self.curmod].registers.add(fields[2])
            self.modinfo[self.curmod].wsize[fields[2]] = int(fields[3])

        if fields[1] == "yosys-smt2-memory":
            self.modinfo[self.curmod].memories[fields[2]] = (int(fields[3]), int(fields[4]), int(fields[5]))

        if fields[1] == "yosys-smt2-wire":
            self.modinfo[self.curmod].wires.add(fields[2])
            self.modinfo[self.curmod].wsize[fields[2]] = int(fields[3])

        if fields[1] == "yosys-smt2-assert":
            self.modinfo[self.curmod].asserts[fields[2]] = fields[3]

        if fields[1] == "yosys-smt2-anyconst":
            self.modinfo[self.curmod].anyconsts[fields[2]] = fields[3]

    def hiernets(self, top, regs_only=False):
        def hiernets_worker(nets, mod, cursor):
            for netname in sorted(self.modinfo[mod].wsize.keys()):
                if not regs_only or netname in self.modinfo[mod].registers:
                    nets.append(cursor + [netname])
            for cellname, celltype in sorted(self.modinfo[mod].cells.items()):
                hiernets_worker(nets, celltype, cursor + [cellname])

        nets = list()
        hiernets_worker(nets, top, [])
        return nets

    def hiermems(self, top):
        def hiermems_worker(mems, mod, cursor):
            for memname in sorted(self.modinfo[mod].memories.keys()):
                mems.append(cursor + [memname])
            for cellname, celltype in sorted(self.modinfo[mod].cells.items()):
                hiermems_worker(mems, celltype, cursor + [cellname])

        mems = list()
        hiermems_worker(mems, top, [])
        return mems

    def read(self):
        stmt = []
        count_brackets = 0

        while True:
            line = self.p.stdout.readline().decode("ascii").strip()
            count_brackets += line.count("(")
            count_brackets -= line.count(")")
            stmt.append(line)
            if self.debug_print:
                print("< %s" % line)
            if count_brackets == 0:
                break
            if self.p.poll():
                print("SMT Solver terminated unexpectedly: %s" % "".join(stmt))
                sys.exit(1)

        stmt = "".join(stmt)
        if stmt.startswith("(error"):
            print("SMT Solver Error: %s" % stmt, file=sys.stderr)
            sys.exit(1)

        return stmt

    def check_sat(self):
        if self.debug_print:
            print("> (check-sat)")
        if self.debug_file:
            print("; running check-sat..", file=self.debug_file)
            self.debug_file.flush()

        self.p.stdin.write(bytes("(check-sat)\n", "ascii"))
        self.p.stdin.flush()

        if self.timeinfo:
            i = 0
            s = "/-\|"

            count = 0
            num_bs = 0
            while select([self.p.stdout], [], [], 0.1) == ([], [], []):
                count += 1

                if count < 25:
                    continue

                if count % 10 == 0 or count == 25:
                    secs = count // 10

                    if secs < 60:
                        m = "(%d seconds)" % secs
                    elif secs < 60*60:
                        m = "(%d seconds -- %d:%02d)" % (secs, secs // 60, secs % 60)
                    else:
                        m = "(%d seconds -- %d:%02d:%02d)" % (secs, secs // (60*60), (secs // 60) % 60, secs % 60)

                    print("%s %s %c" % ("\b \b" * num_bs, m, s[i]), end="", file=sys.stderr)
                    num_bs = len(m) + 3

                else:
                    print("\b" + s[i], end="", file=sys.stderr)

                sys.stderr.flush()
                i = (i + 1) % len(s)

            if num_bs != 0:
                print("\b \b" * num_bs, end="", file=sys.stderr)
                sys.stderr.flush()

        result = self.read()
        if self.debug_file:
            print("(set-info :status %s)" % result, file=self.debug_file)
            print("(check-sat)", file=self.debug_file)
            self.debug_file.flush()
        return result

    def parse(self, stmt):
        def worker(stmt):
            if stmt[0] == '(':
                expr = []
                cursor = 1
                while stmt[cursor] != ')':
                    el, le = worker(stmt[cursor:])
                    expr.append(el)
                    cursor += le
                return expr, cursor+1

            if stmt[0] == '|':
                expr = "|"
                cursor = 1
                while stmt[cursor] != '|':
                    expr += stmt[cursor]
                    cursor += 1
                expr += "|"
                return expr, cursor+1

            if stmt[0] in [" ", "\t", "\r", "\n"]:
                el, le = worker(stmt[1:])
                return el, le+1

            expr = ""
            cursor = 0
            while stmt[cursor] not in ["(", ")", "|", " ", "\t", "\r", "\n"]:
                expr += stmt[cursor]
                cursor += 1
            return expr, cursor
        return worker(stmt)[0]

    def bv2hex(self, v):
        h = ""
        v = self.bv2bin(v)
        while len(v) > 0:
            d = 0
            if len(v) > 0 and v[-1] == "1": d += 1
            if len(v) > 1 and v[-2] == "1": d += 2
            if len(v) > 2 and v[-3] == "1": d += 4
            if len(v) > 3 and v[-4] == "1": d += 8
            h = hex(d)[2:] + h
            if len(v) < 4: break
            v = v[:-4]
        return h

    def bv2bin(self, v):
        if v == "true": return "1"
        if v == "false": return "0"
        if v.startswith("#b"):
            return v[2:]
        if v.startswith("#x"):
            return "".join(hex_dict.get(x) for x in v[2:])
        assert False

    def bv2int(self, v):
        return int(self.bv2bin(v), 2)

    def get(self, expr):
        self.write("(get-value (%s))" % (expr))
        return self.parse(self.read())[0][1]

    def get_list(self, expr_list):
        if len(expr_list) == 0:
            return []
        self.write("(get-value (%s))" % " ".join(expr_list))
        return [n[1] for n in self.parse(self.read())]

    def get_path(self, mod, path):
        assert mod in self.modinfo
        path = path.split(".")

        for i in range(len(path)-1):
            first = ".".join(path[0:i+1])
            second = ".".join(path[i+1:])

            if first in self.modinfo[mod].cells:
                nextmod = self.modinfo[mod].cells[first]
                return [first] + self.get_path(nextmod, second)

        return [".".join(path)]

    def net_expr(self, mod, base, path):
        if len(path) == 1:
            assert mod in self.modinfo
            if path[0] in self.modinfo[mod].wsize:
                return "(|%s_n %s| %s)" % (mod, path[0], base)
            if path[0] in self.modinfo[mod].memories:
                return "(|%s_m %s| %s)" % (mod, path[0], base)
            assert 0

        assert mod in self.modinfo
        assert path[0] in self.modinfo[mod].cells

        nextmod = self.modinfo[mod].cells[path[0]]
        nextbase = "(|%s_h %s| %s)" % (mod, path[0], base)
        return self.net_expr(nextmod, nextbase, path[1:])

    def net_width(self, mod, net_path):
        for i in range(len(net_path)-1):
            assert mod in self.modinfo
            assert net_path[i] in self.modinfo[mod].cells
            mod = self.modinfo[mod].cells[net_path[i]]

        assert mod in self.modinfo
        assert net_path[-1] in self.modinfo[mod].wsize
        return self.modinfo[mod].wsize[net_path[-1]]

    def mem_expr(self, mod, base, path, portidx=None, infomode=False):
        if len(path) == 1:
            assert mod in self.modinfo
            assert path[0] in self.modinfo[mod].memories
            if infomode:
                return self.modinfo[mod].memories[path[0]]
            return "(|%s_m%s %s| %s)" % (mod, "" if portidx is None else ":%d" % portidx, path[0], base)

        assert mod in self.modinfo
        assert path[0] in self.modinfo[mod].cells

        nextmod = self.modinfo[mod].cells[path[0]]
        nextbase = "(|%s_h %s| %s)" % (mod, path[0], base)
        return self.mem_expr(nextmod, nextbase, path[1:], portidx=portidx, infomode=infomode)

    def mem_info(self, mod, base, path):
        return self.mem_expr(mod, base, path, infomode=True)

    def get_net(self, mod_name, net_path, state_name):
        return self.get(self.net_expr(mod_name, state_name, net_path))

    def get_net_list(self, mod_name, net_path_list, state_name):
        return self.get_list([self.net_expr(mod_name, state_name, n) for n in net_path_list])

    def get_net_hex(self, mod_name, net_path, state_name):
        return self.bv2hex(self.get_net(mod_name, net_path, state_name))

    def get_net_hex_list(self, mod_name, net_path_list, state_name):
        return [self.bv2hex(v) for v in self.get_net_list(mod_name, net_path_list, state_name)]

    def get_net_bin(self, mod_name, net_path, state_name):
        return self.bv2bin(self.get_net(mod_name, net_path, state_name))

    def get_net_bin_list(self, mod_name, net_path_list, state_name):
        return [self.bv2bin(v) for v in self.get_net_list(mod_name, net_path_list, state_name)]

    def wait(self):
        self.p.wait()


class SmtOpts:
    def __init__(self):
        self.shortopts = "s:v"
        self.longopts = ["no-progress", "dump-smt2="]
        self.solver = "z3"
        self.debug_print = False
        self.debug_file = None
        self.timeinfo = True

    def handle(self, o, a):
        if o == "-s":
            self.solver = a
        elif o == "-v":
            self.debug_print = True
        elif o == "--no-progress":
            self.timeinfo = True
        elif o == "--dump-smt2":
            self.debug_file = open(a, "w")
        else:
            return False
        return True

    def helpmsg(self):
        return """
    -s <solver>
        set SMT solver: z3, cvc4, yices, mathsat
        default: z3

    -v
        enable debug output

    --no-progress
        disable running timer display during solving

    --dump-smt2 <filename>
        write smt2 statements to file
"""


class MkVcd:
    def __init__(self, f):
        self.f = f
        self.t = -1
        self.nets = dict()

    def add_net(self, path, width):
        path = tuple(path)
        assert self.t == -1
        key = "n%d" % len(self.nets)
        self.nets[path] = (key, width)

    def set_net(self, path, bits):
        path = tuple(path)
        assert self.t >= 0
        assert path in self.nets
        print("b%s %s" % (bits, self.nets[path][0]), file=self.f)

    def set_time(self, t):
        assert t >= self.t
        if t != self.t:
            if self.t == -1:
                print("$var event 1 ! smt_clock $end", file=self.f)
                scope = []
                for path in sorted(self.nets):
                    while len(scope)+1 > len(path) or (len(scope) > 0 and scope[-1] != path[len(scope)-1]):
                        print("$upscope $end", file=self.f)
                        scope = scope[:-1]
                    while len(scope)+1 < len(path):
                        print("$scope module %s $end" % path[len(scope)], file=self.f)
                        scope.append(path[len(scope)-1])
                    key, width = self.nets[path]
                    print("$var wire %d %s %s $end" % (width, key, path[-1]), file=self.f)
                for i in range(len(scope)):
                    print("$upscope $end", file=self.f)
                print("$enddefinitions $end", file=self.f)
            self.t = t
            assert self.t >= 0
            print("#%d" % self.t, file=self.f)
            print("1!", file=self.f)

