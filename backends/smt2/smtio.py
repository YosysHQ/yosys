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

import sys
import subprocess
from select import select
from time import time

class smtio:
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

        self.p = subprocess.Popen(popen_vargs, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.start_time = time()

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
        if self.debug_print:
            print("> %s" % stmt)
        if self.debug_file:
            print(stmt, file=self.debug_file)
            self.debug_file.flush()
        self.p.stdin.write(bytes(stmt + "\n", "ascii"))
        self.p.stdin.flush()

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
            if not self.p.poll():
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
        v = bv2bin(v)
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
            digits = []
            for d in v[2:]:
                if d == "0": digits.append("0000")
                if d == "1": digits.append("0001")
                if d == "2": digits.append("0010")
                if d == "3": digits.append("0011")
                if d == "4": digits.append("0100")
                if d == "5": digits.append("0101")
                if d == "6": digits.append("0110")
                if d == "7": digits.append("0111")
                if d == "8": digits.append("1000")
                if d == "9": digits.append("1001")
                if d in ("a", "A"): digits.append("1010")
                if d in ("b", "B"): digits.append("1011")
                if d in ("c", "C"): digits.append("1100")
                if d in ("d", "D"): digits.append("1101")
                if d in ("e", "E"): digits.append("1110")
                if d in ("f", "F"): digits.append("1111")
            return "".join(digits)
        assert False

    def get(self, expr):
        self.write("(get-value (%s))" % (expr))
        return self.parse(self.read())[0][1]

    def get_net(self, mod_name, net_name, state_name):
        return self.get("(|%s_n %s| %s)" % (mod_name, net_name, state_name))

    def get_net_bool(self, mod_name, net_name, state_name):
        v = self.get_net(mod_name, net_name, state_name)
        assert v in ["true", "false"]
        return 1 if v == "true" else 0

    def get_net_hex(self, mod_name, net_name, state_name):
        return self.bv2hex(self.get_net(mod_name, net_name, state_name))

    def get_net_bin(self, mod_name, net_name, state_name):
        return self.bv2bin(self.get_net(mod_name, net_name, state_name))

    def wait(self):
        self.p.wait()


class smtopts:
    def __init__(self):
        self.optstr = "s:d:vp"
        self.solver = "z3"
        self.debug_print = False
        self.debug_file = None
        self.timeinfo = True

    def handle(self, o, a):
        if o == "-s":
            self.solver = a
        elif o == "-v":
            self.debug_print = True
        elif o == "-p":
            self.timeinfo = True
        elif o == "-d":
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

    -p
        disable timer display during solving

    -d <filename>
        write smt2 statements to file
"""


class mkvcd:
    def __init__(self, f):
        self.f = f
        self.t = -1
        self.nets = dict()

    def add_net(self, name, width):
        assert self.t == -1
        key = "n%d" % len(self.nets)
        self.nets[name] = (key, width)

    def set_net(self, name, bits):
        assert name in self.nets
        assert self.t >= 0
        print("b%s %s" % (bits, self.nets[name][0]), file=self.f)

    def set_time(self, t):
        assert t >= self.t
        if t != self.t:
            if self.t == -1:
                print("$var event 1 ! smt_clock $end", file=self.f)
                for name in sorted(self.nets):
                    key, width = self.nets[name]
                    print("$var wire %d %s %s $end" % (width, key, name), file=self.f)
                print("$enddefinitions $end", file=self.f)
            self.t = t
            assert self.t >= 0
            print("#%d" % self.t, file=self.f)
            print("1!", file=self.f)

