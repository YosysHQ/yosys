#
# yosys -- Yosys Open SYnthesis Suite
#
# Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

import sys, re, os, signal, json
import subprocess
if os.name == "posix":
    import resource
from copy import copy
from select import select
from time import time
from queue import Queue, Empty
from threading import Thread


# This is needed so that the recursive SMT2 S-expression parser
# does not run out of stack frames when parsing large expressions
if os.name == "posix":
    smtio_reclimit = 64 * 1024
    if sys.getrecursionlimit() < smtio_reclimit:
        sys.setrecursionlimit(smtio_reclimit)

    current_rlimit_stack = resource.getrlimit(resource.RLIMIT_STACK)
    if current_rlimit_stack[0] != resource.RLIM_INFINITY:
        smtio_stacksize = 128 * 1024 * 1024
        if os.uname().sysname == "Darwin":
            # MacOS has rather conservative stack limits
            smtio_stacksize = 8 * 1024 * 1024
        if current_rlimit_stack[1] != resource.RLIM_INFINITY:
            smtio_stacksize = min(smtio_stacksize, current_rlimit_stack[1])
        if current_rlimit_stack[0] < smtio_stacksize:
            try:
                resource.setrlimit(resource.RLIMIT_STACK, (smtio_stacksize, current_rlimit_stack[1]))
            except ValueError:
                # couldn't get more stack, just run with what we have
                pass


# currently running solvers (so we can kill them)
running_solvers = dict()
forced_shutdown = False
solvers_index = 0

def force_shutdown(signum, frame):
    global forced_shutdown
    if not forced_shutdown:
        forced_shutdown = True
        if signum is not None:
            print("<%s>" % signal.Signals(signum).name)
        for p in running_solvers.values():
            # os.killpg(os.getpgid(p.pid), signal.SIGTERM)
            os.kill(p.pid, signal.SIGTERM)
    sys.exit(1)

if os.name == "posix":
    signal.signal(signal.SIGHUP, force_shutdown)
signal.signal(signal.SIGINT, force_shutdown)
signal.signal(signal.SIGTERM, force_shutdown)

def except_hook(exctype, value, traceback):
    if not forced_shutdown:
        sys.__excepthook__(exctype, value, traceback)
    force_shutdown(None, None)

sys.excepthook = except_hook


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
        self.clocks = dict()
        self.cells = dict()
        self.asserts = dict()
        self.covers = dict()
        self.maximize = set()
        self.minimize = set()
        self.anyconsts = dict()
        self.anyseqs = dict()
        self.allconsts = dict()
        self.allseqs = dict()
        self.asize = dict()
        self.witness = []


class SmtIo:
    def __init__(self, opts=None):
        global solvers_index

        self.logic = None
        self.logic_qf = True
        self.logic_ax = True
        self.logic_uf = True
        self.logic_bv = True
        self.logic_dt = False
        self.forall = False
        self.timeout = 0
        self.produce_models = True
        self.recheck = False
        self.smt2cache = [list()]
        self.smt2_options = dict()
        self.p = None
        self.p_index = solvers_index
        solvers_index += 1

        if opts is not None:
            self.logic = opts.logic
            self.solver = opts.solver
            self.solver_opts = opts.solver_opts
            self.debug_print = opts.debug_print
            self.debug_file = opts.debug_file
            self.dummy_file = opts.dummy_file
            self.timeinfo = opts.timeinfo
            self.timeout = opts.timeout
            self.unroll = opts.unroll
            self.noincr = opts.noincr
            self.info_stmts = opts.info_stmts
            self.nocomments = opts.nocomments

        else:
            self.solver = "yices"
            self.solver_opts = list()
            self.debug_print = False
            self.debug_file = None
            self.dummy_file = None
            self.timeinfo = os.name != "nt"
            self.timeout = 0
            self.unroll = False
            self.noincr = False
            self.info_stmts = list()
            self.nocomments = False

        self.start_time = time()

        self.modinfo = dict()
        self.curmod = None
        self.topmod = None
        self.setup_done = False

    def __del__(self):
        if self.p is not None and not forced_shutdown:
            os.killpg(os.getpgid(self.p.pid), signal.SIGTERM)
            if running_solvers is not None:
                del running_solvers[self.p_index]

    def setup(self):
        assert not self.setup_done

        if self.forall:
            self.unroll = False

        if self.solver == "yices":
            if self.forall:
                self.noincr = True

            if self.noincr:
                self.popen_vargs = ['yices-smt2'] + self.solver_opts
            else:
                self.popen_vargs = ['yices-smt2', '--incremental'] + self.solver_opts
            if self.timeout != 0:
                self.popen_vargs.append('-t')
                self.popen_vargs.append('%d' % self.timeout);

        if self.solver == "z3":
            self.popen_vargs = ['z3', '-smt2', '-in'] + self.solver_opts
            if self.timeout != 0:
                self.popen_vargs.append('-T:%d' % self.timeout);

        if self.solver in ["cvc4", "cvc5"]:
            self.recheck = True
            if self.noincr:
                self.popen_vargs = [self.solver, '--lang', 'smt2.6' if self.logic_dt else 'smt2'] + self.solver_opts
            else:
                self.popen_vargs = [self.solver, '--incremental', '--lang', 'smt2.6' if self.logic_dt else 'smt2'] + self.solver_opts
            if self.timeout != 0:
                self.popen_vargs.append('--tlimit=%d000' % self.timeout);

        if self.solver == "mathsat":
            self.popen_vargs = ['mathsat'] + self.solver_opts
            if self.timeout != 0:
                print('timeout option is not supported for mathsat.')
                sys.exit(1)

        if self.solver in ["boolector", "bitwuzla"]:
            if self.noincr:
                self.popen_vargs = [self.solver, '--smt2'] + self.solver_opts
            else:
                self.popen_vargs = [self.solver, '--smt2', '-i'] + self.solver_opts
            self.unroll = True
            if self.timeout != 0:
                print('timeout option is not supported for %s.' % self.solver)
                sys.exit(1)

        if self.solver == "abc":
            if len(self.solver_opts) > 0:
                self.popen_vargs = ['yosys-abc', '-S', '; '.join(self.solver_opts)]
            else:
                self.popen_vargs = ['yosys-abc', '-S', '%blast; &sweep -C 5000; &syn4; &cec -s -m -C 2000']
            self.logic_ax = False
            self.unroll = True
            self.noincr = True
            if self.timeout != 0:
                print('timeout option is not supported for abc.')
                sys.exit(1)

        if self.solver == "dummy":
            assert self.dummy_file is not None
            self.dummy_fd = open(self.dummy_file, "r")
        else:
            if self.dummy_file is not None:
                self.dummy_fd = open(self.dummy_file, "w")
            if not self.noincr:
                self.p_open()

        if self.unroll:
            assert not self.forall
            self.logic_uf = False
            self.unroll_idcnt = 0
            self.unroll_buffer = ""
            self.unroll_sorts = set()
            self.unroll_objs = set()
            self.unroll_decls = dict()
            self.unroll_cache = dict()
            self.unroll_stack = list()

        if self.logic is None:
            self.logic = ""
            if self.logic_qf: self.logic += "QF_"
            if self.logic_ax: self.logic += "A"
            if self.logic_uf: self.logic += "UF"
            if self.logic_bv: self.logic += "BV"
            if self.logic_dt: self.logic = "ALL"
            if self.solver == "yices" and self.forall: self.logic = "BV"

        self.setup_done = True

        for stmt in self.info_stmts:
            self.write(stmt)

        if self.produce_models:
            self.write("(set-option :produce-models true)")

        #See the SMT-LIB Standard, Section 4.1.7
        modestart_options = [":global-declarations", ":interactive-mode", ":produce-assertions", ":produce-assignments", ":produce-models", ":produce-proofs", ":produce-unsat-assumptions", ":produce-unsat-cores", ":random-seed"]
        for key, val in self.smt2_options.items():
            if key in modestart_options:
                self.write("(set-option {} {})".format(key, val))

        self.write("(set-logic %s)" % self.logic)

        if self.forall and self.solver == "yices":
            self.write("(set-option :yices-ef-max-iters 1000000000)")

        for key, val in self.smt2_options.items():
            if key not in modestart_options:
                self.write("(set-option {} {})".format(key, val))

    def timestamp(self):
        secs = int(time() - self.start_time)
        return "## %3d:%02d:%02d " % (secs // (60*60), (secs // 60) % 60, secs % 60)

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
                decl = copy(self.unroll_decls[key[0]])

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

    def p_thread_main(self):
        while True:
            data = self.p.stdout.readline().decode("utf-8")
            if data == "": break
            self.p_queue.put(data)
        self.p_queue.put("")
        self.p_running = False

    def p_open(self):
        assert self.p is None
        try:
            self.p = subprocess.Popen(self.popen_vargs, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        except FileNotFoundError:
            print("%s SMT Solver '%s' not found in path." % (self.timestamp(), self.popen_vargs[0]), flush=True)
            sys.exit(1)
        running_solvers[self.p_index] = self.p
        self.p_running = True
        self.p_next = None
        self.p_queue = Queue()
        self.p_thread = Thread(target=self.p_thread_main)
        self.p_thread.start()

    def p_write(self, data, flush):
        assert self.p is not None
        self.p.stdin.write(bytes(data, "utf-8"))
        if flush: self.p.stdin.flush()

    def p_read(self):
        assert self.p is not None
        if self.p_next is not None:
            data = self.p_next
            self.p_next = None
            return data
        if not self.p_running:
            return ""
        return self.p_queue.get()

    def p_poll(self, timeout=0.1):
        assert self.p is not None
        assert self.p_running
        if self.p_next is not None:
            return False
        try:
            self.p_next = self.p_queue.get(True, timeout)
            return False
        except Empty:
            return True

    def p_close(self):
        assert self.p is not None
        self.p.stdin.close()
        self.p_thread.join()
        assert not self.p_running
        del running_solvers[self.p_index]
        self.p = None
        self.p_next = None
        self.p_queue = None
        self.p_thread = None

    def write(self, stmt, unroll=True):
        if stmt.startswith(";"):
            self.info(stmt)
            if not self.setup_done:
                self.info_stmts.append(stmt)
                return
        elif not self.setup_done:
            self.setup()

        stmt = stmt.strip()

        if self.nocomments or self.unroll:
            stmt = re.sub(r" *;.*", "", stmt)
            if stmt == "": return

        recheck = None

        if self.solver != "dummy":
            if self.noincr:
                # Don't close the solver yet, if we're just unrolling definitions
                # required for a (get-...) statement
                if self.p is not None and not stmt.startswith("(get-") and unroll:
                    self.p_close()

        if unroll and self.unroll:
            stmt = self.unroll_buffer + stmt
            self.unroll_buffer = ""

            s = re.sub(r"\|[^|]*\|", "", stmt)
            if s.count("(") != s.count(")"):
                self.unroll_buffer = stmt + " "
                return

            s = self.parse(stmt)

            if self.recheck and s and s[0].startswith("get-"):
                recheck = self.unroll_idcnt

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

            if recheck is not None and recheck != self.unroll_idcnt:
                self.check_sat(["sat"])

            if stmt == "(push 1)":
                self.unroll_stack.append((
                    copy(self.unroll_sorts),
                    copy(self.unroll_objs),
                    copy(self.unroll_decls),
                    copy(self.unroll_cache),
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
                if stmt == "(push 1)":
                    self.smt2cache.append(list())
                elif stmt == "(pop 1)":
                    self.smt2cache.pop()
                else:
                    if self.p is not None:
                        self.p_write(stmt + "\n", True)
                    self.smt2cache[-1].append(stmt)
            else:
                self.p_write(stmt + "\n", True)

    def info(self, stmt):
        if not stmt.startswith("; yosys-smt2-"):
            return

        fields = stmt.split()

        if fields[1] == "yosys-smt2-solver-option":
            self.smt2_options[fields[2]] = fields[3]

        if fields[1] == "yosys-smt2-nomem":
            if self.logic is None:
                self.logic_ax = False

        if fields[1] == "yosys-smt2-nobv":
            if self.logic is None:
                self.logic_bv = False

        if fields[1] == "yosys-smt2-stdt":
            if self.logic is None:
                self.logic_dt = True

        if fields[1] == "yosys-smt2-forall":
            if self.logic is None:
                self.logic_qf = False
            self.forall = True

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
            self.modinfo[self.curmod].memories[fields[2]] = (int(fields[3]), int(fields[4]), int(fields[5]), int(fields[6]), fields[7] == "async")

        if fields[1] == "yosys-smt2-wire":
            self.modinfo[self.curmod].wires.add(fields[2])
            self.modinfo[self.curmod].wsize[fields[2]] = int(fields[3])

        if fields[1] == "yosys-smt2-clock":
            for edge in fields[3:]:
                if fields[2] not in self.modinfo[self.curmod].clocks:
                    self.modinfo[self.curmod].clocks[fields[2]] = edge
                elif self.modinfo[self.curmod].clocks[fields[2]] != edge:
                    self.modinfo[self.curmod].clocks[fields[2]] = "event"

        if fields[1] == "yosys-smt2-assert":
            if len(fields) > 4:
                self.modinfo[self.curmod].asserts["%s_a %s" % (self.curmod, fields[2])] = f'{fields[4]} ({fields[3]})'
            else:
                self.modinfo[self.curmod].asserts["%s_a %s" % (self.curmod, fields[2])] = fields[3]

        if fields[1] == "yosys-smt2-cover":
            if len(fields) > 4:
                self.modinfo[self.curmod].covers["%s_c %s" % (self.curmod, fields[2])] = f'{fields[4]} ({fields[3]})'
            else:
                self.modinfo[self.curmod].covers["%s_c %s" % (self.curmod, fields[2])] = fields[3]

        if fields[1] == "yosys-smt2-maximize":
            self.modinfo[self.curmod].maximize.add(fields[2])

        if fields[1] == "yosys-smt2-minimize":
            self.modinfo[self.curmod].minimize.add(fields[2])

        if fields[1] == "yosys-smt2-anyconst":
            self.modinfo[self.curmod].anyconsts[fields[2]] = (fields[4], None if len(fields) <= 5 else fields[5])
            self.modinfo[self.curmod].asize[fields[2]] = int(fields[3])

        if fields[1] == "yosys-smt2-anyseq":
            self.modinfo[self.curmod].anyseqs[fields[2]] = (fields[4], None if len(fields) <= 5 else fields[5])
            self.modinfo[self.curmod].asize[fields[2]] = int(fields[3])

        if fields[1] == "yosys-smt2-allconst":
            self.modinfo[self.curmod].allconsts[fields[2]] = (fields[4], None if len(fields) <= 5 else fields[5])
            self.modinfo[self.curmod].asize[fields[2]] = int(fields[3])

        if fields[1] == "yosys-smt2-allseq":
            self.modinfo[self.curmod].allseqs[fields[2]] = (fields[4], None if len(fields) <= 5 else fields[5])
            self.modinfo[self.curmod].asize[fields[2]] = int(fields[3])

        if fields[1] == "yosys-smt2-witness":
            data = json.loads(stmt.split(None, 2)[2])
            if data.get("type") in ["cell", "mem", "posedge", "negedge", "input", "reg", "init", "seq", "blackbox"]:
                self.modinfo[self.curmod].witness.append(data)

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

    def hieranyconsts(self, top):
        def worker(results, mod, cursor):
            for name, value in sorted(self.modinfo[mod].anyconsts.items()):
                width = self.modinfo[mod].asize[name]
                results.append((cursor, name, value[0], value[1], width))
            for cellname, celltype in sorted(self.modinfo[mod].cells.items()):
                worker(results, celltype, cursor + [cellname])

        results = list()
        worker(results, top, [])
        return results

    def hieranyseqs(self, top):
        def worker(results, mod, cursor):
            for name, value in sorted(self.modinfo[mod].anyseqs.items()):
                width = self.modinfo[mod].asize[name]
                results.append((cursor, name, value[0], value[1], width))
            for cellname, celltype in sorted(self.modinfo[mod].cells.items()):
                worker(results, celltype, cursor + [cellname])

        results = list()
        worker(results, top, [])
        return results

    def hierallconsts(self, top):
        def worker(results, mod, cursor):
            for name, value in sorted(self.modinfo[mod].allconsts.items()):
                width = self.modinfo[mod].asize[name]
                results.append((cursor, name, value[0], value[1], width))
            for cellname, celltype in sorted(self.modinfo[mod].cells.items()):
                worker(results, celltype, cursor + [cellname])

        results = list()
        worker(results, top, [])
        return results

    def hierallseqs(self, top):
        def worker(results, mod, cursor):
            for name, value in sorted(self.modinfo[mod].allseqs.items()):
                width = self.modinfo[mod].asize[name]
                results.append((cursor, name, value[0], value[1], width))
            for cellname, celltype in sorted(self.modinfo[mod].cells.items()):
                worker(results, celltype, cursor + [cellname])

        results = list()
        worker(results, top, [])
        return results

    def hiermems(self, top):
        def hiermems_worker(mems, mod, cursor):
            for memname in sorted(self.modinfo[mod].memories.keys()):
                mems.append(cursor + [memname])
            for cellname, celltype in sorted(self.modinfo[mod].cells.items()):
                hiermems_worker(mems, celltype, cursor + [cellname])

        mems = list()
        hiermems_worker(mems, top, [])
        return mems

    def hierwitness(self, top, allregs=False, blackbox=True):
        init_witnesses = []
        seq_witnesses = []
        clk_witnesses = []
        mem_witnesses = []

        def absolute(path, cursor, witness):
            return {
                **witness,
                "path": path + tuple(witness["path"]),
                "smtpath": cursor + [witness["smtname"]],
            }

        for witness in self.modinfo[top].witness:
            if witness["type"] == "input":
                seq_witnesses.append(absolute((), [], witness))
            if witness["type"] in ("posedge", "negedge"):
                clk_witnesses.append(absolute((), [], witness))

        init_types = ["init"]
        if allregs:
            init_types.append("reg")

        seq_types = ["seq"]
        if blackbox:
            seq_types.append("blackbox")

        def worker(mod, path, cursor):
            cell_paths = {}
            for witness in self.modinfo[mod].witness:
                if witness["type"] in init_types:
                    init_witnesses.append(absolute(path, cursor, witness))
                if witness["type"] in seq_types:
                    seq_witnesses.append(absolute(path, cursor, witness))
                if witness["type"] == "mem":
                    if allregs and not witness["rom"]:
                        width, size = witness["width"], witness["size"]
                        witness = {**witness, "uninitialized": [{"width": width * size, "offset": 0}]}
                    if not witness["uninitialized"]:
                        continue

                    mem_witnesses.append(absolute(path, cursor, witness))
                if witness["type"] == "cell":
                    cell_paths[witness["smtname"]] = tuple(witness["path"])

            for cellname, celltype in sorted(self.modinfo[mod].cells.items()):
                worker(celltype, path + cell_paths.get(cellname, ("?" + cellname,)), cursor + [cellname])

        worker(top, (), [])
        return init_witnesses, seq_witnesses, clk_witnesses, mem_witnesses

    def read(self):
        stmt = []
        count_brackets = 0

        while True:
            if self.solver == "dummy":
                line = self.dummy_fd.readline().strip()
            else:
                line = self.p_read().strip()
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
                print("%s Solver terminated unexpectedly: %s" % (self.timestamp(), "".join(stmt)), flush=True)
                sys.exit(1)

        stmt = "".join(stmt)
        if stmt.startswith("(error"):
            print("%s Solver Error: %s" % (self.timestamp(), stmt), flush=True)
            if self.solver != "dummy":
                self.p_close()
            sys.exit(1)

        return stmt

    def check_sat(self, expected=["sat", "unsat", "unknown", "timeout", "interrupted"]):
        if self.debug_print:
            print("> (check-sat)")
        if self.debug_file and not self.nocomments:
            print("; running check-sat..", file=self.debug_file)
            self.debug_file.flush()

        if self.solver != "dummy":
            if self.noincr:
                if self.p is not None:
                    self.p_close()
                self.p_open()
                for cache_ctx in self.smt2cache:
                    for cache_stmt in cache_ctx:
                        self.p_write(cache_stmt + "\n", False)

            self.p_write("(check-sat)\n", True)

            if self.timeinfo:
                i = 0
                s = r"/-\|"

                count = 0
                num_bs = 0
                while self.p_poll():
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

            else:
                count = 0
                while self.p_poll(60):
                    count += 1
                    msg = None

                    if count == 1:
                        msg = "1 minute"

                    elif count in [5, 10, 15, 30]:
                        msg = "%d minutes" % count

                    elif count == 60:
                        msg = "1 hour"

                    elif count % 60 == 0:
                        msg = "%d hours" % (count // 60)

                    if msg is not None:
                        print("%s waiting for solver (%s)" % (self.timestamp(), msg), flush=True)

        if self.forall:
            result = self.read()
            while result not in ["sat", "unsat", "unknown", "timeout", "interrupted", ""]:
                print("%s %s: %s" % (self.timestamp(), self.solver, result))
                result = self.read()
        else:
            result = self.read()

        if self.debug_file:
            print("(set-info :status %s)" % result, file=self.debug_file)
            print("(check-sat)", file=self.debug_file)
            self.debug_file.flush()

        if result not in expected:
            if result == "":
                print("%s Unexpected EOF response from solver." % (self.timestamp()), flush=True)
            else:
                print("%s Unexpected response from solver: %s" % (self.timestamp(), result), flush=True)
            if self.solver != "dummy":
                self.p_close()
            sys.exit(1)

        return result

    def parse(self, stmt):
        def worker(stmt, cursor=0):
            while stmt[cursor] in [" ", "\t", "\r", "\n"]:
                cursor += 1

            if stmt[cursor] == '(':
                expr = []
                cursor += 1
                while stmt[cursor] != ')':
                    el, cursor = worker(stmt, cursor)
                    expr.append(el)
                return expr, cursor+1

            if stmt[cursor] == '|':
                expr = "|"
                cursor += 1
                while stmt[cursor] != '|':
                    expr += stmt[cursor]
                    cursor += 1
                expr += "|"
                return expr, cursor+1

            expr = ""
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
        if type(v) is list and len(v) == 3 and v[0] == "_" and v[1].startswith("bv"):
            x, n = int(v[1][2:]), int(v[2])
            return "".join("1" if (x & (1 << i)) else "0" for i in range(n-1, -1, -1))
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
        path = path.replace("\\", "/").split(".")

        for i in range(len(path)-1):
            first = ".".join(path[0:i+1])
            second = ".".join(path[i+1:])

            if first in self.modinfo[mod].cells:
                nextmod = self.modinfo[mod].cells[first]
                return [first] + self.get_path(nextmod, second)

        return [".".join(path)]

    def net_expr(self, mod, base, path):
        if len(path) == 0:
            return base

        if len(path) == 1:
            assert mod in self.modinfo
            if path[0] == "":
                return base
            if isinstance(path[0], int):
                return "(|%s#%d| %s)" % (mod, path[0], base)
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

    def witness_net_expr(self, mod, base, witness):
        net = self.net_expr(mod, base, witness["smtpath"])
        is_bool = self.net_width(mod, witness["smtpath"]) == 1
        if is_bool:
            assert witness["width"] == 1
            assert witness["smtoffset"] == 0
            return net
        return "((_ extract %d %d) %s)" % (witness["smtoffset"] + witness["width"] - 1, witness["smtoffset"], net)

    def net_width(self, mod, net_path):
        for i in range(len(net_path)-1):
            assert mod in self.modinfo
            assert net_path[i] in self.modinfo[mod].cells
            mod = self.modinfo[mod].cells[net_path[i]]

        assert mod in self.modinfo
        if isinstance(net_path[-1], int):
            return None
        assert net_path[-1] in self.modinfo[mod].wsize
        return self.modinfo[mod].wsize[net_path[-1]]

    def net_clock(self, mod, net_path):
        for i in range(len(net_path)-1):
            assert mod in self.modinfo
            assert net_path[i] in self.modinfo[mod].cells
            mod = self.modinfo[mod].cells[net_path[i]]

        assert mod in self.modinfo
        if net_path[-1] not in self.modinfo[mod].clocks:
            return None
        return self.modinfo[mod].clocks[net_path[-1]]

    def net_exists(self, mod, net_path):
        for i in range(len(net_path)-1):
            if mod not in self.modinfo: return False
            if net_path[i] not in self.modinfo[mod].cells: return False
            mod = self.modinfo[mod].cells[net_path[i]]

        if mod not in self.modinfo: return False
        if net_path[-1] not in self.modinfo[mod].wsize: return False
        return True

    def mem_exists(self, mod, mem_path):
        for i in range(len(mem_path)-1):
            if mod not in self.modinfo: return False
            if mem_path[i] not in self.modinfo[mod].cells: return False
            mod = self.modinfo[mod].cells[mem_path[i]]

        if mod not in self.modinfo: return False
        if mem_path[-1] not in self.modinfo[mod].memories: return False
        return True

    def mem_expr(self, mod, base, path, port=None, infomode=False):
        if len(path) == 1:
            assert mod in self.modinfo
            assert path[0] in self.modinfo[mod].memories
            if infomode:
                return self.modinfo[mod].memories[path[0]]
            return "(|%s_m%s %s| %s)" % (mod, "" if port is None else ":%s" % port, path[0], base)

        assert mod in self.modinfo
        assert path[0] in self.modinfo[mod].cells

        nextmod = self.modinfo[mod].cells[path[0]]
        nextbase = "(|%s_h %s| %s)" % (mod, path[0], base)
        return self.mem_expr(nextmod, nextbase, path[1:], port=port, infomode=infomode)

    def mem_info(self, mod, path):
        return self.mem_expr(mod, "", path, infomode=True)

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
            self.p_close()


class SmtOpts:
    def __init__(self):
        self.shortopts = "s:S:v"
        self.longopts = ["unroll", "noincr", "noprogress", "timeout=", "dump-smt2=", "logic=", "dummy=", "info=", "nocomments"]
        self.solver = "yices"
        self.solver_opts = list()
        self.debug_print = False
        self.debug_file = None
        self.dummy_file = None
        self.unroll = False
        self.noincr = False
        self.timeinfo = os.name != "nt"
        self.timeout = 0
        self.logic = None
        self.info_stmts = list()
        self.nocomments = False

    def handle(self, o, a):
        if o == "-s":
            self.solver = a
        elif o == "-S":
            self.solver_opts.append(a)
        elif o == "--timeout":
            self.timeout = int(a)
        elif o == "-v":
            self.debug_print = True
        elif o == "--unroll":
            self.unroll = True
        elif o == "--noincr":
            self.noincr = True
        elif o == "--noprogress":
            self.timeinfo = False
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
        set SMT solver: z3, yices, boolector, bitwuzla, cvc4, mathsat, dummy
        default: yices

    -S <opt>
        pass <opt> as command line argument to the solver

    --timeout <value>
        set the solver timeout to the specified value (in seconds).

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
        (this option is set implicitly on Windows)

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
        self.clocks = dict()

    def add_net(self, path, width):
        path = tuple(path)
        assert self.t == -1
        key = "n%d" % len(self.nets)
        self.nets[path] = (key, width)

    def add_clock(self, path, edge):
        path = tuple(path)
        assert self.t == -1
        key = "n%d" % len(self.nets)
        self.nets[path] = (key, 1)
        self.clocks[path] = (key, edge)

    def set_net(self, path, bits):
        path = tuple(path)
        assert self.t >= 0
        assert path in self.nets
        if path not in self.clocks:
            print("b%s %s" % (bits, self.nets[path][0]), file=self.f)

    def escape_name(self, name):
        name = re.sub(r"\[([0-9a-zA-Z_]*[a-zA-Z_][0-9a-zA-Z_]*)\]", r"<\1>", name)
        if re.match(r"[\[\]]", name) and name[0] != "\\":
            name = "\\" + name
        return name

    def set_time(self, t):
        assert t >= self.t
        if t != self.t:
            if self.t == -1:
                print("$version Generated by Yosys-SMTBMC $end", file=self.f)
                print("$timescale 1ns $end", file=self.f)
                print("$var integer 32 t smt_step $end", file=self.f)
                print("$var event 1 ! smt_clock $end", file=self.f)

                def vcdescape(n):
                    if n.startswith("$") or ":" in n:
                        return "\\" + n
                    return n

                scope = []
                for path in sorted(self.nets):
                    key, width = self.nets[path]

                    uipath = list(path)
                    if "." in uipath[-1] and not uipath[-1].startswith("$"):
                        uipath = uipath[0:-1] + uipath[-1].split(".")
                    for i in range(len(uipath)):
                        uipath[i] = re.sub(r"\[([^\]]*)\]", r"<\1>", uipath[i])

                    while uipath[:len(scope)] != scope:
                        print("$upscope $end", file=self.f)
                        scope = scope[:-1]

                    while uipath[:-1] != scope:
                        scopename = uipath[len(scope)]
                        print("$scope module %s $end" % vcdescape(scopename), file=self.f)
                        scope.append(uipath[len(scope)])

                    if path in self.clocks and self.clocks[path][1] == "event":
                        print("$var event 1 %s %s $end" % (key, vcdescape(uipath[-1])), file=self.f)
                    else:
                        print("$var wire %d %s %s $end" % (width, key, vcdescape(uipath[-1])), file=self.f)

                for i in range(len(scope)):
                    print("$upscope $end", file=self.f)

                print("$enddefinitions $end", file=self.f)

            self.t = t
            assert self.t >= 0

            if self.t > 0:
                print("#%d" % (10 * self.t - 5), file=self.f)
                for path in sorted(self.clocks.keys()):
                    if self.clocks[path][1] == "posedge":
                        print("b0 %s" % self.nets[path][0], file=self.f)
                    elif self.clocks[path][1] == "negedge":
                        print("b1 %s" % self.nets[path][0], file=self.f)

            print("#%d" % (10 * self.t), file=self.f)
            print("1!", file=self.f)
            print("b%s t" % format(self.t, "032b"), file=self.f)

            for path in sorted(self.clocks.keys()):
                if self.clocks[path][1] == "negedge":
                    print("b0 %s" % self.nets[path][0], file=self.f)
                else:
                    print("b1 %s" % self.nets[path][0], file=self.f)
