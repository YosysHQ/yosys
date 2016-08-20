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
from smtio import smtio, smtopts, mkvcd

skip_steps = 0
step_size = 1
num_steps = 20
vcdfile = None
tempind = False
assume_skipped = None
topmod = None
so = smtopts()


def usage():
    print("""
yosys-smtbmc [options] <yosys_smt2_output>

    -t <num_steps>, -t <skip_steps>:<num_steps>
        default: skip_steps=0, num_steps=20

    -u <start_step>
        assume asserts in skipped steps in BMC

    -S <step_size>
        prove <step_size> time steps at once

    -i
        instead of BMC run temporal induction

    -m <module_name>
        name of the top module

    --dump-vcd <vcd_filename>
        write counter-example to this VCD file
        (hint: use 'write_smt2 -wires' for maximum
        coverage of signals in generated VCD file)
""" + so.helpmsg())
    sys.exit(1)


try:
    opts, args = getopt.getopt(sys.argv[1:], so.shortopts + "t:u:S:im:", so.longopts + ["dump-vcd="])
except:
    usage()

for o, a in opts:
    if o == "-t":
        match = re.match(r"(\d+):(.*)", a)
        if match:
            skip_steps = int(match.group(1))
            num_steps = int(match.group(2))
        else:
            num_steps = int(a)
    elif o == "-u":
        assume_skipped = int(a)
    elif o == "-S":
        step_size = int(a)
    elif o == "--dump-vcd":
        vcdfile = a
    elif o == "-i":
        tempind = True
    elif o == "-m":
        topmod = a
    elif so.handle(o, a):
        pass
    else:
        usage()

if len(args) != 1:
    usage()


smt = smtio(opts=so)

print("%s Solver: %s" % (smt.timestamp(), so.solver))
smt.setup("QF_AUFBV")

with open(args[0], "r") as f:
    for line in f:
        smt.write(line)
        smt.info(line)

if topmod is None:
    topmod = smt.topmod

assert topmod is not None
assert topmod in smt.modinfo


def write_vcd_model(steps):
    print("%s Writing model to VCD file." % smt.timestamp())

    vcd = mkvcd(open(vcdfile, "w"))

    for netpath in sorted(smt.hiernets(topmod)):
        vcd.add_net([topmod] + netpath, smt.net_width(topmod, netpath))

    for i in range(steps):
        vcd.set_time(i)
        path_list = sorted(smt.hiernets(topmod))
        value_list = smt.get_net_bin_list(topmod, path_list, "s%d" % i)
        for path, value in zip(path_list, value_list):
            vcd.set_net([topmod] + path, value)

    vcd.set_time(steps)


def print_failed_asserts(mod, state, path):
    assert mod in smt.modinfo

    if smt.get("(|%s_a| %s)" % (mod, state)) == "true":
        return

    for cellname, celltype in smt.modinfo[mod].cells.items():
        print_failed_asserts(celltype, "(|%s_h %s| %s)" % (mod, cellname, state), path + "." + cellname)

    for assertfun, assertinfo in smt.modinfo[mod].asserts.items():
        if smt.get("(|%s| %s)" % (assertfun, state)) == "false":
            print("%s Assert failed in %s: %s" % (smt.timestamp(), path, assertinfo))


if tempind:
    retstatus = False
    skip_counter = step_size
    for step in range(num_steps, -1, -1):
        smt.write("(declare-fun s%d () %s_s)" % (step, topmod))
        smt.write("(assert (%s_u s%d))" % (topmod, step))
        smt.write("(assert (%s_h s%d))" % (topmod, step))
        smt.write("(assert (not (%s_is s%d)))" % (topmod, step))

        if step == num_steps:
            smt.write("(assert (not (%s_a s%d)))" % (topmod, step))

        else:
            smt.write("(assert (%s_t s%d s%d))" % (topmod, step, step+1))
            smt.write("(assert (%s_a s%d))" % (topmod, step))

        if step > num_steps-skip_steps:
            print("%s Skipping induction in step %d.." % (smt.timestamp(), step))
            continue

        skip_counter += 1
        if skip_counter < step_size:
            print("%s Skipping induction in step %d.." % (smt.timestamp(), step))
            continue

        skip_counter = 0
        print("%s Trying induction in step %d.." % (smt.timestamp(), step))

        if smt.check_sat() == "sat":
            if step == 0:
                print("%s Temporal induction failed!" % smt.timestamp())
                print_failed_asserts(topmod, "s%d" % step, topmod)
                if vcdfile is not None:
                    write_vcd_model(num_steps+1)

        else:
            print("%s Temporal induction successful." % smt.timestamp())
            retstatus = True
            break


else: # not tempind
    step = 0
    retstatus = True
    while step < num_steps:
        smt.write("(declare-fun s%d () %s_s)" % (step, topmod))
        smt.write("(assert (%s_u s%d))" % (topmod, step))
        smt.write("(assert (%s_h s%d))" % (topmod, step))

        if step == 0:
            smt.write("(assert (%s_i s0))" % (topmod))
            smt.write("(assert (%s_is s0))" % (topmod))

        else:
            smt.write("(assert (%s_t s%d s%d))" % (topmod, step-1, step))
            smt.write("(assert (not (%s_is s%d)))" % (topmod, step))

        if step < skip_steps:
            if assume_skipped is not None and step >= assume_skipped:
                print("%s Skipping step %d (and assuming pass).." % (smt.timestamp(), step))
                smt.write("(assert (%s_a s%d))" % (topmod, step))
            else:
                print("%s Skipping step %d.." % (smt.timestamp(), step))
            step += 1
            continue

        last_check_step = step
        for i in range(1, step_size):
            if step+i < num_steps:
                smt.write("(declare-fun s%d () %s_s)" % (step+i, topmod))
                smt.write("(assert (%s_u s%d))" % (topmod, step+i))
                smt.write("(assert (%s_h s%d))" % (topmod, step+i))
                smt.write("(assert (%s_t s%d s%d))" % (topmod, step+i-1, step+i))
                last_check_step = step+i

        if last_check_step == step:
            print("%s Checking asserts in step %d.." % (smt.timestamp(), step))
        else:
            print("%s Checking asserts in steps %d to %d.." % (smt.timestamp(), step, last_check_step))
        smt.write("(push 1)")

        smt.write("(assert (not (and %s)))" % " ".join(["(%s_a s%d)" % (topmod, i) for i in range(step, last_check_step+1)]))

        if smt.check_sat() == "sat":
            print("%s BMC failed!" % smt.timestamp())
            print_failed_asserts(topmod, "s%d" % step, topmod)
            if vcdfile is not None:
                write_vcd_model(step+step_size)
            retstatus = False
            break

        else: # unsat
            smt.write("(pop 1)")
            for i in range(step, last_check_step+1):
                smt.write("(assert (%s_a s%d))" % (topmod, i))

        step += step_size


smt.write("(exit)")
smt.wait()

print("%s Status: %s" % (smt.timestamp(), "PASSED" if retstatus else "FAILED (!)"))
sys.exit(0 if retstatus else 1)

