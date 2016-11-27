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
from copy import deepcopy
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
    def __init__(self, opts=None):
        self.logic = None
        self.logic_qf = True
        self.logic_ax = True
        self.logic_uf = True
        self.logic_bv = True
        self.produce_models = True
        self.smt2cache = [list()]
        self.p = None

        if opts is not None:
            self.logic = opts.logic
            self.solver = opts.solver
            self.debug_print = opts.debug_print
            self.debug_file = opts.debug_file
            self.dummy_file = opts.dummy_file
            self.timeinfo = opts.timeinfo
            self.unroll = opts.unroll
            self.noincr = opts.noincr
            self.info_stmts = opts.info_stmts
            self.nocomments = opts.nocomments

        else:
            self.solver = "z3"
            self.debug_print = False
            self.debug_file = None
            self.dummy_file = None
            self.timeinfo = True
            self.unroll = False
            self.noincr = False
            self.info_stmts = list()
            self.nocomments = False

        if self.solver == "yices":
            self.popen_vargs = ['yices-smt2', '--incremental']

        if self.solver == "z3":
            self.popen_vargs = ['z3', '-smt2', '-in']

        if self.solver == "cvc4":
            self.popen_vargs = ['cvc4', '--incremental', '--lang', 'smt2']

        if self.solver == "mathsat":
            self.popen_vargs = ['mathsat']

        if self.solver == "boolector":
            self.popen_vargs = ['boolector', '--smt2', '-i']
            self.unroll = True

        if self.solver == "abc":
            self.popen_vargs = ['yosys-abc', '-S', '%blast; &sweep -C 5000; &syn4; &cec -s -m -C 2000']
            self.logic_ax = False
            self.unroll = True
            self.noincr = True

        if self.solver == "dummy":
            assert self.dummy_file is not None
            self.dummy_fd = open(self.dummy_file, "r")
        else:
            if self.dummy_file is not None:
                self.dummy_fd = open(self.dummy_file, "w")
            if not self.noincr:
                self.p = subprocess.Popen(self.popen_vargs, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

        if self.unroll:
            self.logic_uf = False
            self.unroll_idcnt = 0
            self.unroll_buffer = ""
            self.unroll_sorts = set()
            self.unroll_objs = set()
            self.unroll_decls = dict()
            self.unroll_cache = dict()
            self.unroll_stack = list()

        self.start_time = time()

        self.modinfo = dict()
        self.curmod = None
        self.topmod = None
        self.setup_done = False

    def setup(self):
        assert not self.setup_done

        if self.logic is None:
            self.logic = ""
            if self.logic_qf: self.logic += "QF_"
            if self.logic_ax: self.logic += "A"
            if self.logic_uf: self.logic += "UF"
            if self.logic_bv: self.logic += "BV"

        self.setup_done = True

        if self.produce_models:
            self.write("(set-option :produce-models true)")

        self.write("(set-logic %s)" % self.logic)

        for stmt in self.info_stmts:
            self.write(stmt)

    def timestamp(self):
        secs = int(time() - self.start_time)
        return "## %6d %3d:%02d:%02d " % (secs, secs // (60*60), (secs // 60) % 60, secs % 60)

    def replace_in_stmt(self, stmt, pat, repl):
        if stmt == pat:
            return repl

        if isinstance(stmt, list):
            return [self.replace_in_stmt(s, pat, repl) for s in stmt]

        return stmt

    def unroll_stmt(self, stmt):
        if not isinstance(stmt, list):
            return stmt

        stmt = [self.unroll_stmt(s) for s in stmt]

        if len(stmt) >= 2 and not isinstance(stmt[0], list) and stmt[0] in self.unroll_decls:
            assert stmt[1] in self.unroll_objs

            key = tuple(stmt)
            if key not in self.unroll_cache:
                decl = deepcopy(self.unroll_decls[key[0]])

                self.unroll_cache[key] = "|UNROLL#%d|" % self.unroll_idcnt
                decl[1] = self.unroll_cache[key]
                self.unroll_idcnt += 1

                if decl[0] == "declare-fun":
                    if isinstance(decl[3], list) or decl[3] not in self.unroll_sorts:
                        self.unroll_objs.add(decl[1])
                        decl[2] = list()
                    else:
                        self.unroll_objs.add(decl[1])
                        decl = list()

                elif decl[0] == "define-fun":
                    arg_index = 1
                    for arg_name, arg_sort in decl[2]:
                        decl[4] = self.replace_in_stmt(decl[4], arg_name, key[arg_index])
                        arg_index += 1
                    decl[2] = list()

                if len(decl) > 0:
                    decl = self.unroll_stmt(decl)
                    self.write(self.unparse(decl), unroll=False)

            return self.unroll_cache[key]

        return stmt

    def write(self, stmt, unroll=True):
        if stmt.startswith(";"):
            self.info(stmt)
        elif not self.setup_done:
            self.setup()

        stmt = stmt.strip()

        if self.nocomments or self.unroll:
            if stmt.startswith(";"):
                return
            stmt = re.sub(r" ;.*", "", stmt)

        if unroll and self.unroll:
            stmt = self.unroll_buffer + stmt
            self.unroll_buffer = ""

            s = re.sub(r"\|[^|]*\|", "", stmt)
            if s.count("(") != s.count(")"):
                self.unroll_buffer = stmt + " "
                return

            s = self.parse(stmt)

            if self.debug_print:
                print("-> %s" % s)

            if len(s) == 3 and s[0] == "declare-sort" and s[2] == "0":
                self.unroll_sorts.add(s[1])
                return

            elif len(s) == 4 and s[0] == "declare-fun" and s[2] == [] and s[3] in self.unroll_sorts:
                self.unroll_objs.add(s[1])
                return

            elif len(s) >= 4 and s[0] == "declare-fun":
                for arg_sort in s[2]:
                    if arg_sort in self.unroll_sorts:
                        self.unroll_decls[s[1]] = s
                        return

            elif len(s) >= 4 and s[0] == "define-fun":
                for arg_name, arg_sort in s[2]:
                    if arg_sort in self.unroll_sorts:
                        self.unroll_decls[s[1]] = s
                        return

            stmt = self.unparse(self.unroll_stmt(s))

            if stmt == "(push 1)":
                self.unroll_stack.append((
                    deepcopy(self.unroll_sorts),
                    deepcopy(self.unroll_objs),
                    deepcopy(self.unroll_decls),
                    deepcopy(self.unroll_cache),
                ))

            if stmt == "(pop 1)":
                self.unroll_sorts, self.unroll_objs, self.unroll_decls, self.unroll_cache = self.unroll_stack.pop()

        if self.debug_print:
            print("> %s" % stmt)

        if self.debug_file:
            print(stmt, file=self.debug_file)
            self.debug_file.flush()

        if self.solver != "dummy":
            if self.noincr:
                if self.p is not None and not stmt.startswith("(get-"):
                    self.p.stdin.close()
                    self.p = None
                if stmt == "(push 1)":
                    self.smt2cache.append(list())
                elif stmt == "(pop 1)":
                    self.smt2cache.pop()
                else:
                    if self.p is not None:
                        self.p.stdin.write(bytes(stmt + "\n", "ascii"))
                        self.p.stdin.flush()
                    self.smt2cache[-1].append(stmt)
            else:
                self.p.stdin.write(bytes(stmt + "\n", "ascii"))
                self.p.stdin.flush()

    def info(self, stmt):
        if not stmt.startswith("; yosys-smt2-"):
            return

        fields = stmt.split()

        if fields[1] == "yosys-smt2-nomem":
            if self.logic is None:
                self.logic_ax = False

        if fields[1] == "yosys-smt2-nobv":
            if self.logic is None:
                self.logic_bv = False

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
            if self.solver == "dummy":
                line = self.dummy_fd.readline().strip()
            else:
                line = self.p.stdout.readline().decode("ascii").strip()
                if self.dummy_file is not None:
                    self.dummy_fd.write(line + "\n")

            count_brackets += line.count("(")
            count_brackets -= line.count(")")
            stmt.append(line)

            if self.debug_print:
                print("< %s" % line)
            if count_brackets == 0:
                break
            if self.solver != "dummy" and self.p.poll():
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
        if self.debug_file and not self.nocomments:
            print("; running check-sat..", file=self.debug_file)
            self.debug_file.flush()

        if self.solver != "dummy":
            if self.noincr:
                if self.p is not None:
                    self.p.stdin.close()
                    self.p = None
                self.p = subprocess.Popen(self.popen_vargs, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                for cache_ctx in self.smt2cache:
                    for cache_stmt in cache_ctx:
                        self.p.stdin.write(bytes(cache_stmt + "\n", "ascii"))

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

    def unparse(self, stmt):
        if isinstance(stmt, list):
            return "(" + " ".join([self.unparse(s) for s in stmt]) + ")"
        return stmt

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
            if path[0] == "":
                return base
            if path[0] in self.modinfo[mod].cells:
                return "(|%s_h %s| %s)" % (mod, path[0], base)
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
        if self.p is not None:
            self.p.wait()


class SmtOpts:
    def __init__(self):
        self.shortopts = "s:v"
        self.longopts = ["unroll", "noincr", "noprogress", "dump-smt2=", "logic=", "dummy=", "info=", "nocomments"]
        self.solver = "z3"
        self.debug_print = False
        self.debug_file = None
        self.dummy_file = None
        self.unroll = False
        self.noincr = False
        self.timeinfo = True
        self.logic = None
        self.info_stmts = list()
        self.nocomments = False

    def handle(self, o, a):
        if o == "-s":
            self.solver = a
        elif o == "-v":
            self.debug_print = True
        elif o == "--unroll":
            self.unroll = True
        elif o == "--noincr":
            self.noincr = True
        elif o == "--noprogress":
            self.timeinfo = True
        elif o == "--dump-smt2":
            self.debug_file = open(a, "w")
        elif o == "--logic":
            self.logic = a
        elif o == "--dummy":
            self.dummy_file = a
        elif o == "--info":
            self.info_stmts.append(a)
        elif o == "--nocomments":
            self.nocomments = True
        else:
            return False
        return True

    def helpmsg(self):
        return """
    -s <solver>
        set SMT solver: z3, cvc4, yices, mathsat, boolector, dummy
        default: z3

    --logic <smt2_logic>
        use the specified SMT2 logic (e.g. QF_AUFBV)

    --dummy <filename>
        if solver is "dummy", read solver output from that file
        otherwise: write solver output to that file

    -v
        enable debug output

    --unroll
        unroll uninterpreted functions

    --noincr
        don't use incremental solving, instead restart solver for
        each (check-sat). This also avoids (push) and (pop).

    --noprogress
        disable timer display during solving

    --dump-smt2 <filename>
        write smt2 statements to file

    --info <smt2-info-stmt>
        include the specified smt2 info statement in the smt2 output

    --nocomments
        strip all comments from the generated smt2 code
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
                print("$var integer 32 t smt_step $end", file=self.f)
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
            print("#%d" % (10 * self.t), file=self.f)
            print("1!", file=self.f)
            print("b%s t" % format(self.t, "032b"), file=self.f)

