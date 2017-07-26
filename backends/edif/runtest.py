#!/usr/bin/env python3

import os
import numpy as np

enable_upto = True
enable_offset = True
enable_hierarchy = True
enable_logic = True

def make_module(f, modname, width, subs):
    print("module %s (A, B, C, X, Y, Z);" % modname, file=f)
    inbits = list()
    outbits = list()

    for p in "ABC":
        offset = np.random.randint(10) if enable_offset else 0
        if enable_upto and np.random.randint(2):
            print("  input [%d:%d] %s;" % (offset, offset+width-1, p), file=f)
        else:
            print("  input [%d:%d] %s;" % (offset+width-1, offset, p), file=f)
        for i in range(offset, offset+width):
            inbits.append("%s[%d]" % (p, i))

    for p in "XYZ":
        offset = np.random.randint(10) if enable_offset else 0
        if enable_upto and np.random.randint(2):
            print("  output [%d:%d] %s;" % (offset, offset+width-1, p), file=f)
        else:
            print("  output [%d:%d] %s;" % (offset+width-1, offset, p), file=f)
        for i in range(offset, offset+width):
            outbits.append("%s[%d]" % (p, i))

    instidx = 0
    subcandidates = list(subs.keys())

    while len(outbits) > 0:
        submod = None
        if len(subcandidates):
            submod = np.random.choice(subcandidates)
            subcandidates.remove(submod)

        if submod is None or 3*subs[submod] >= len(outbits):
            for bit in outbits:
                if enable_logic:
                    print("  assign %s = %s & ~%s;" % (bit,  np.random.choice(inbits), np.random.choice(inbits)), file=f)
                else:
                    print("  assign %s = %s;" % (bit,  np.random.choice(inbits)), file=f)
            break

        instidx += 1
        print("  %s inst%d (" % (submod, instidx), file=f)

        for p in "ABC":
            print("    .%s({%s})," % (p, ",".join(np.random.choice(inbits, subs[submod]))), file=f)

        for p in "XYZ":
            bits = list(np.random.choice(outbits, subs[submod], False))
            for bit in bits:
                outbits.remove(bit)
            print("    .%s({%s})%s" % (p, ",".join(bits), "," if p != "Z" else ""), file=f)

        print("  );", file=f);

    print("endmodule", file=f)

with open("test_top.v", "w") as f:
    if enable_hierarchy:
        make_module(f, "sub1", 2, {})
        make_module(f, "sub2", 3, {})
        make_module(f, "sub3", 4, {})
        make_module(f, "sub4", 8, {"sub1": 2, "sub2": 3, "sub3": 4})
        make_module(f, "sub5", 8, {"sub1": 2, "sub2": 3, "sub3": 4})
        make_module(f, "sub6", 8, {"sub1": 2, "sub2": 3, "sub3": 4})
        make_module(f, "top", 32, {"sub4": 8, "sub5": 8, "sub6": 8})
    else:
        make_module(f, "top", 32, {})

os.system("set -x; ../../yosys -p 'synth_xilinx -top top; write_edif -pvector par test_syn.edif' test_top.v")

with open("test_syn.tcl", "w") as f:
    print("read_edif test_syn.edif", file=f)
    print("link_design", file=f)
    print("write_verilog -force test_syn.v", file=f)

os.system("set -x; vivado -nojournal -nolog -mode batch -source test_syn.tcl")

with open("test_tb.v", "w") as f:
    print("module tb;", file=f)
    print("  reg [31:0] A, B, C;", file=f)
    print("  wire [31:0] X, Y, Z;", file=f)
    print("", file=f)
    print("  top uut (", file=f)
    print("    .A(A),", file=f)
    print("    .B(B),", file=f)
    print("    .C(C),", file=f)
    print("    .X(X),", file=f)
    print("    .Y(Y),", file=f)
    print("    .Z(Z)", file=f)
    print("  );", file=f)
    print("", file=f)
    print("  initial begin", file=f)
    for i in range(100):
        print("    A = 32'h%08x;" % np.random.randint(2**32), file=f)
        print("    B = 32'h%08x;" % np.random.randint(2**32), file=f)
        print("    C = 32'h%08x;" % np.random.randint(2**32), file=f)
        print("    #10;", file=f)
        print("    $display(\"%x %x %x\", X, Y, Z);", file=f)
        print("    #10;", file=f)
    print("    $finish;", file=f)
    print("  end", file=f)
    print("endmodule", file=f)

os.system("set -x; iverilog -o test_gold test_tb.v test_top.v")
os.system("set -x; iverilog -o test_gate test_tb.v test_syn.v ../../techlibs/xilinx/cells_sim.v")

os.system("set -x; ./test_gold > test_gold.out")
os.system("set -x; ./test_gate > test_gate.out")

os.system("set -x; md5sum test_gold.out test_gate.out")

