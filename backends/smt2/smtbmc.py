#!/usr/bin/env python3

import os, sys, getopt, re
from smtio import smtio, smtopts, mkvcd

max_steps = 20
min_steps = None
vcdfile = None
tempind = False
topmod = "main"
so = smtopts()


def usage():
    print("""
yosys-smtbmc [options] <yosys_smt2_output>

    -t <max_steps>
        default: 20

    -c <vcd_filename>
        write counter-example to this VCD file
        (hint: use 'write_smt2 -wires' for maximum
        coverage of signals in generated VCD file)

    -i <min_steps>
        instead of BMC run temporal induction

    -m <module_name>
        name of the top module, default: main
""" + so.helpmsg())
    sys.exit(1)


try:
    opts, args = getopt.getopt(sys.argv[1:], so.optstr + "t:c:i:m:")
except:
    usage()

for o, a in opts:
    if o == "-t":
        max_steps = int(a)
    elif o == "-c":
        vcdfile = a
    elif o == "-i":
        tempind = True
        min_steps = int(a)
    elif o == "-m":
        topmod = a
    elif so.handle(o, a):
        pass
    else:
        usage()

if len(args) != 1:
    usage()


smt = smtio(opts=so)

print("Solver: %s" % so.solver)
smt.setup("QF_AUFBV")

debug_nets = set()
debug_nets_re = re.compile(r"^; yosys-smt2-(input|output|register|wire) (\S+) (\d+)")

with open(args[0], "r") as f:
    for line in f:
        match = debug_nets_re.match(line)
        if match:
            debug_nets.add(match.group(2))
        smt.write(line)


def write_vcd_model():
    print("%s Writing model to VCD file." % smt.timestamp())

    vcd = mkvcd(open(vcdfile, "w"))
    for netname in sorted(debug_nets):
        width = len(smt.get_net_bin("main", netname, "s0"))
        vcd.add_net(netname, width)

    for i in range(step+1):
        vcd.set_time(i)
        for netname in debug_nets:
            vcd.set_net(netname, smt.get_net_bin("main", netname, "s%d" % i))

    vcd.set_time(step+1)


if tempind:
    for step in range(max_steps, -1, -1):
        smt.write("(declare-fun s%d () %s_s)" % (step, topmod))
        smt.write("(assert (%s_u s%d))" % (topmod, step))

        if step == max_steps:
            smt.write("(assert (not (%s_a s%d)))" % (topmod, step))

        else:
            smt.write("(assert (%s_t s%d s%d))" % (topmod, step, step+1))
            smt.write("(assert (%s_a s%d))" % (topmod, step))

        if step > max_steps-min_steps:
            print("%s Skipping induction in step %d.." % (smt.timestamp(), step))
            continue

        print("%s Trying induction in step %d.." % (smt.timestamp(), step))

        if smt.check_sat() == "sat":
            if step == 0:
                print("%s temporal induction failed!" % smt.timestamp())
                if vcdfile is not None:
                    write_vcd_model()

        else:
            print("%s PASSED." % smt.timestamp())
            break


else: # not tempind
    for step in range(max_steps+1):
        smt.write("(declare-fun s%d () %s_s)" % (step, topmod))
        smt.write("(assert (%s_u s%d))" % (topmod, step))

        if step == 0:
            smt.write("(assert (%s_i s0))" % (topmod))

        else:
            smt.write("(assert (%s_t s%d s%d))" % (topmod, step-1, step))

        print("%s Checking asserts in step %d.." % (smt.timestamp(), step))
        smt.write("(push 1)")

        smt.write("(assert (not (%s_a s%d)))" % (topmod, step))

        if smt.check_sat() == "sat":
            print("%s BMC failed!" % smt.timestamp())
            if vcdfile is not None:
                write_vcd_model()
            break

        else: # unsat
            smt.write("(pop 1)")
            smt.write("(assert (%s_a s%d))" % (topmod, step))


print("%s Done." % smt.timestamp())
smt.write("(exit)")
smt.wait()

