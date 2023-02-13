import os
import re
import sys
import random
import argparse

parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
parser.add_argument('-S', '--seed', type=int, help='seed for PRNG')
parser.add_argument('-m', '--more', action='store_true', help='run more tests')
parser.add_argument('-c', '--count', type=int, default=32, help='number of random patterns to test')
parser.add_argument('-f', '--filter', default='', help='regular expression to filter tests to generate')
args = parser.parse_args()

if args.seed is None:
    args.seed = random.randrange(1 << 32)

print(f"xprop PRNG seed: {args.seed}")

makefile = open("run-test.mk", "w")

def add_test(name, src, seq=False):
    if not re.search(args.filter, name):
        return
    workdir = f"xprop_{name}"

    os.makedirs(workdir, exist_ok=True)
    with open(f"{workdir}/uut.v", "w") as uut:
        print(src, file=uut)
    print(f"all: {workdir}", file=makefile)
    print(f".PHONY: {workdir}", file=makefile)
    print(f"{workdir}:", file=makefile)
    seq_arg = " -s" if seq else ""
    print(
        f"\t@cd {workdir} && python3 -u ../test.py -S {args.seed} -c {args.count}{seq_arg} > test.log 2>&1 || echo {workdir}: failed > status\n"
        f"\t@cat {workdir}/status\n"
        f"\t@grep '^.*: ok' {workdir}/status\n"
        ,
        file=makefile,
    )

def cell_test(name, cell, inputs, outputs, params, initial={}, defclock=False, seq=False):
    ports = []
    port_conns = []
    for inport, width in inputs.items():
        ports.append(f"input [{width-1}:0] {inport}")
        if defclock and inport in ["C", "CLK"]:
            port_conns.append(f".{inport}({inport} !== 0)")
        else:
            port_conns.append(f".{inport}({inport})")
    for outport, width in outputs.items():
        reg = " reg" if outport in initial else ""
        ports.append(f"output{reg} [{width-1}:0] {outport}")
        port_conns.append(f".{outport}({outport})")
    param_defs = []
    for param, value in params.items():
        param_defs.append(f".{param}({value})")
    initials = []
    # for port, value in initial.items():
    #     initials.append(f"initial {port} = {value};\n")
    add_test(name,
        f"module uut({', '.join(ports)});\n"
        f"\\${cell} #({', '.join(param_defs)}) cell ({', '.join(port_conns)});\n"
        f"{''.join(initials)}"
        "endmodule",
        seq=seq,
    )

def unary_test(cell, width, signed, out_width):
    add_test(
        f"{cell}_{width}{'us'[signed]}_{out_width}",
        f"module uut(input [{width-1}:0] A, output [{out_width}-1:0] Y);\n"
        f"\\${cell} #(.A_WIDTH({width}), .A_SIGNED({int(signed)}), .Y_WIDTH({out_width}))"
        " cell (.A(A), .Y(Y));\n"
        "endmodule",
    )

def binary_test(cell, a_width, b_width, signed, out_width):
    add_test(
        f"{cell}_{a_width}{'us'[signed]}{b_width}_{out_width}",
        f"module uut(input [{a_width-1}:0] A, input [{b_width-1}:0] B, output [{out_width}-1:0] Y);\n"
        f"\\${cell} #(.A_WIDTH({a_width}), .A_SIGNED({int(signed)}), .B_WIDTH({b_width}), .B_SIGNED({int(signed)}), .Y_WIDTH({out_width}))"
        " cell (.A(A), .B(B), .Y(Y));\n"
        "endmodule",
    )

def shift_test(cell, a_width, b_width, a_signed, b_signed, out_width):
    add_test(
        f"{cell}_{a_width}{'us'[a_signed]}{b_width}{'us'[b_signed]}_{out_width}",
        f"module uut(input [{a_width-1}:0] A, input [{b_width-1}:0] B, output [{out_width}-1:0] Y);\n"
        f"\\${cell} #(.A_WIDTH({a_width}), .A_SIGNED({int(a_signed)}), .B_WIDTH({b_width}), .B_SIGNED({int(b_signed)}), .Y_WIDTH({out_width}))"
        " cell (.A(A), .B(B), .Y(Y));\n"
        "endmodule",
    )

def mux_test(width):
    cell_test(f"mux_{width}", 'mux', {"A": width, "B": width, "S": 1}, {"Y": width}, {"WIDTH": width})

def bmux_test(width, s_width):
    cell_test(f"bmux_{width}_{s_width}", 'bmux', {"A": width << s_width, "S": s_width}, {"Y": width}, {"WIDTH": width, "S_WIDTH": s_width})

def demux_test(width, s_width):
    cell_test(f"demux_{width}_{s_width}", 'demux', {"A": width, "S": s_width}, {"Y": width << s_width}, {"WIDTH": width, "S_WIDTH": s_width})

def pmux_test(width, s_width):
    cell_test(f"pmux_{width}_{s_width}", 'pmux', {"A": width, "B": width * s_width, "S": s_width}, {"Y": width}, {"WIDTH": width, "S_WIDTH": s_width})

def bwmux_test(width):
    cell_test(f"bwmux_{width}", 'bwmux', {"A": width, "B": width, "S": width}, {"Y": width}, {"WIDTH": width})

def bweqx_test(width):
    cell_test(f"bweqx_{width}", 'bweqx', {"A": width, "B": width}, {"Y": width}, {"WIDTH": width})

def ff_test(width):
    cell_test(f"ff_{width}", 'ff', {"D": width}, {"Q": width}, {"WIDTH": width}, seq=True)

def dff_test(width, pol, defclock):
    cell_test(f"dff_{width}{'np'[pol]}{'xd'[defclock]}", 'dff', {"CLK": 1, "D": width}, {"Q": width}, {"WIDTH": width, "CLK_POLARITY": int(pol)}, defclock=defclock, seq=True)

def dffe_test(width, pol, enpol, defclock):
    cell_test(f"dffe_{width}{'np'[pol]}{'np'[enpol]}{'xd'[defclock]}", 'dffe', {"CLK": 1, "EN": 1, "D": width}, {"Q": width}, {"WIDTH": width, "CLK_POLARITY": int(pol), "EN_POLARITY": int(enpol)}, defclock=defclock, seq=True)


print(".PHONY: all", file=makefile)
print("all:\n\t@echo done\n", file=makefile)

for cell in ["not", "pos", "neg"]:
    if args.more:
        unary_test(cell, 1, False, 1)
        unary_test(cell, 3, False, 3)
        unary_test(cell, 3, True, 3)
        unary_test(cell, 3, True, 1)
        unary_test(cell, 3, False, 5)
    unary_test(cell, 3, True, 5)

for cell in ["and", "or", "xor", "xnor"]:
    binary_test(cell, 1, 1, False, 1)
    binary_test(cell, 1, 1, True, 2)
    binary_test(cell, 2, 2, False, 2)
    if args.more:
        binary_test(cell, 2, 2, False, 1)
        binary_test(cell, 2, 1, False, 2)
        binary_test(cell, 2, 1, False, 1)

# [, "pow"] are not implemented yet
for cell in ["add", "sub", "mul", "div", "mod", "divfloor", "modfloor"]:
    if args.more:
        binary_test(cell, 1, 1, False, 1)
        binary_test(cell, 1, 1, False, 2)
        binary_test(cell, 3, 3, False, 1)
        binary_test(cell, 3, 3, False, 3)
        binary_test(cell, 3, 3, False, 6)
        binary_test(cell, 3, 3, True, 1)
        binary_test(cell, 3, 3, True, 3)
        binary_test(cell, 3, 3, True, 6)
    binary_test(cell, 5, 3, False, 3)
    binary_test(cell, 5, 3, True, 3)

for cell in ["lt", "le", "eq", "ne", "eqx", "nex", "ge", "gt"]:
    if args.more:
        binary_test(cell, 1, 1, False, 1)
        binary_test(cell, 1, 1, False, 2)
        binary_test(cell, 3, 3, False, 1)
        binary_test(cell, 3, 3, False, 2)
        binary_test(cell, 3, 3, True, 1)
        binary_test(cell, 3, 3, True, 2)
        binary_test(cell, 5, 3, False, 1)
        binary_test(cell, 5, 3, True, 1)
    binary_test(cell, 5, 3, False, 2)
    binary_test(cell, 5, 3, True, 2)

for cell in ["reduce_and", "reduce_or", "reduce_xor", "reduce_xnor"]:
    if args.more:
        unary_test(cell, 1, False, 1)
        unary_test(cell, 3, False, 1)
        unary_test(cell, 3, True, 1)
    unary_test(cell, 3, False, 3)
    unary_test(cell, 3, True, 3)

for cell in ["reduce_bool", "logic_not"]:
    unary_test(cell, 1, False, 1)
    unary_test(cell, 3, False, 3)
    unary_test(cell, 3, True, 3)
    unary_test(cell, 3, True, 1)

for cell in ["logic_and", "logic_or"]:
    binary_test(cell, 1, 1, False, 1)
    binary_test(cell, 3, 3, False, 3)
    binary_test(cell, 3, 3, True, 3)
    binary_test(cell, 3, 3, True, 1)

for cell in ["shl", "shr", "sshl", "sshr", "shift"]:
    if args.more:
        shift_test(cell, 2, 1, False, False, 2)
        shift_test(cell, 2, 1, True, False, 2)
        shift_test(cell, 2, 1, False, False, 4)
        shift_test(cell, 2, 1, True, False, 4)
        shift_test(cell, 4, 2, False, False, 4)
        shift_test(cell, 4, 2, True, False, 4)
        shift_test(cell, 4, 2, False, False, 8)
        shift_test(cell, 4, 2, True, False, 8)
    shift_test(cell, 4, 3, False, False, 3)
    shift_test(cell, 4, 3, True, False, 3)

for cell in ["shift"]:
    if args.more:
        shift_test(cell, 2, 1, False, True, 2)
        shift_test(cell, 2, 1, True, True, 2)
        shift_test(cell, 2, 1, False, True, 4)
        shift_test(cell, 2, 1, True, True, 4)
        shift_test(cell, 4, 2, False, True, 4)
        shift_test(cell, 4, 2, True, True, 4)
    shift_test(cell, 4, 2, False, True, 8)
    shift_test(cell, 4, 2, True, True, 8)
    shift_test(cell, 4, 3, False, True, 3)
    shift_test(cell, 4, 3, True, True, 3)

for cell in ["shiftx"]:
    if args.more:
        shift_test(cell, 2, 1, False, True, 2)
        shift_test(cell, 2, 1, False, True, 4)
        shift_test(cell, 4, 2, False, True, 4)
    shift_test(cell, 4, 2, False, True, 8)
    shift_test(cell, 4, 3, False, True, 3)

mux_test(1)
mux_test(3)

bmux_test(1, 2)
bmux_test(2, 2)
bmux_test(3, 1)

demux_test(1, 2)
demux_test(2, 2)
demux_test(3, 1)

pmux_test(1, 4)
pmux_test(2, 2)
pmux_test(3, 1)
pmux_test(4, 4)

bwmux_test(1)
bwmux_test(3)

bweqx_test(1)
bweqx_test(3)

ff_test(1)
ff_test(3)

dff_test(1, True, True)
dff_test(1, False, True)
dff_test(3, True, True)
dff_test(3, False, True)

# dff_test(1, True, False)  # TODO support x clocks
# dff_test(1, False, False)  # TODO support x clocks
# dff_test(3, True, False)  # TODO support x clocks
# dff_test(3, False, False)  # TODO support x clocks

dffe_test(1, True, False, True)
dffe_test(1, False, False, True)
dffe_test(3, True, False, True)
dffe_test(3, False, False, True)
dffe_test(1, True, True, True)
dffe_test(1, False, True, True)
dffe_test(3, True, True, True)
dffe_test(3, False, True, True)



# TODO "shift", "shiftx"

# TODO "fa", "lcu", "alu", "macc", "lut", "sop"

# TODO "slice", "concat"

# TODO "tribuf", "specify2", "specify3", "specrule"

# TODO "assert", "assume", "live", "fair", "cover", "initstate", "anyconst", "anyseq", "anyinit", "allconst", "allseq", "equiv",

# TODO "bweqx", "bwmux"

# TODO "sr", "ff", "dff", "dffe", "dffsr", "sffsre", "adff", "aldff", "sdff", "adffe", "aldffe", "sdffe", "sdffce", "dlatch", "adlatch", "dlatchsr"

# TODO "fsm"

# TODO "memrd", "memrd_v2", "memwr", "memwr_v2", "meminit", "meminit_v2", "mem", "mem_v2"
