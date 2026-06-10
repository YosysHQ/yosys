#!/usr/bin/env python3
# Differential check of Yosys's UDP lowering against Icarus Verilog.
#
# For the `primitive` in the given .v file, drive random single-input changes
# (4-state: 0/1/x/z), simulate with iverilog (which evaluates the UDP natively)
# and with `yosys sim` (which simulates the lowered netlist), and assert that the
# two output traces are equal under multi-valued logic.
#
# Usage: udp_cosim.py <udp.v> [num_stimuli] [steps]
# Requires: iverilog, vvp, python3, and $YOSYS pointing at the yosys binary.

import os, sys, re, subprocess, random, tempfile

YOSYS = os.environ.get("YOSYS", "yosys")

def sh(cmd):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True)

def parse_primitive(path):
    txt = open(path).read()
    m = re.search(r'primitive\s+(\w+)\s*\(([^)]*)\)', txt)
    ports = [re.sub(r'\b(output|input|reg)\b', '', p).strip()
             for p in m.group(2).split(',')]
    return m.group(1), ports[0], ports[1:]

def gen_tb(name, out, ins, stim):
    decl = "\n".join("  reg %s;" % s for s in ins)
    inst = ", ".join([out] + ins)
    body = "\n".join("    #10 %s = 1'b%s;" % (ins[i], v) for (i, v) in stim)
    return ("module tb;\n%s\n  wire %s;\n  %s dut(%s);\n"
            "  initial begin\n    $dumpfile(\"wave\");\n    $dumpvars(0, tb);\n"
            "%s\n    #10 $finish;\n  end\nendmodule\n"
            % (decl, out, name, inst, body))

def trace(vcd, signame):
    sid = None
    for line in vcd.splitlines():
        m = re.match(r'\$var\s+\w+\s+1\s+(\S+)\s+(\S+)', line)
        if m and m.group(2) == signame:
            sid = m.group(1); break
    if sid is None:
        return None
    t, out = 0, []
    for line in vcd.splitlines():
        line = line.strip()
        if line.startswith('#'):
            t = int(line[1:])
        elif len(line) >= 2 and line[0] in '01xz' and line[1:] == sid:
            out.append((t, line[0]))
        else:
            mm = re.match(r'b(\S+)\s+(\S+)', line)
            if mm and mm.group(2) == sid:
                out.append((t, mm.group(1)[-1]))
    return out

def value_at(tr, t):
    v = 'x'
    for (tt, vv) in tr:
        if tt <= t: v = vv
        else: break
    return v

def run_one(udp_file, name, out, ins, stim):
    with tempfile.TemporaryDirectory() as wd:
        open(os.path.join(wd, "tb.v"), "w").write(gen_tb(name, out, ins, stim))
        if sh("iverilog -o %s/sim.vvp %s %s/tb.v" % (wd, udp_file, wd)).returncode != 0:
            return None  # iverilog rejected this table; skip
        sh("cd %s && vvp sim.vvp -fst >/dev/null 2>&1" % wd)
        sh("cd %s && vvp sim.vvp >/dev/null 2>&1" % wd)
        ref = trace(open("%s/wave.vcd" % wd).read(), out)
        r = sh("%s -q -p 'read_verilog %s; sim -r %s/wave.fst -scope tb -vcd %s/y.vcd'"
               % (YOSYS, udp_file, wd, wd))
        if r.returncode != 0:
            raise SystemExit("yosys sim failed:\n" + r.stdout + r.stderr)
        mod = trace(open("%s/y.vcd" % wd).read(), out)
        end = 10 * (len(stim) + 1)
        ts = sorted(set([t for t, _ in ref] + [t for t, _ in mod] + list(range(0, end + 1, 10))))
        return [(t, value_at(ref, t), value_at(mod, t)) for t in ts
                if value_at(ref, t) != value_at(mod, t)]

if __name__ == "__main__":
    udp_file = sys.argv[1]
    nstim = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    name, out, ins = parse_primitive(udp_file)
    tested = 0
    for seed in range(nstim):
        rnd = random.Random(seed * 1009 + 1)
        vals4 = ['0', '1', 'x', 'z']
        stim = [(rnd.randrange(len(ins)),
                 rnd.choice(vals4) if rnd.random() < 0.3 else rnd.choice('01'))
                for _ in range(steps)]
        mm = run_one(udp_file, name, out, ins, stim)
        if mm is None:
            continue
        tested += 1
        if mm:
            print("MISMATCH in %s (seed %d):" % (name, seed))
            for (t, a, b) in mm[:12]:
                print("  t=%d iverilog=%s yosys=%s" % (t, a, b))
            print("stimulus:", stim)
            raise SystemExit(1)
    if tested == 0:
        raise SystemExit("iverilog rejected %s for all stimuli" % name)
    print("OK %s (%d stimuli matched)" % (name, tested))
