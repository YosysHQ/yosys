import os
import re
import subprocess
import itertools
import random
import argparse
from pathlib import Path

parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
parser.add_argument('-S', '--seed', type=int, help='seed for PRNG')
parser.add_argument('-c', '--count', type=int, default=32, help='number of random patterns to test')
parser.add_argument('-s', '--seq', action='store_true', help='run a sequential test')
parser.add_argument('steps', nargs='*', help='steps to run')
args = parser.parse_args()

if args.seed is None:
    args.seed = random.randrange(1 << 32)

print(f"PRNG seed: {args.seed}")
random.seed(args.seed)

steps = args.steps

all_outputs = [
    "sim",
    "sim_xprop",
    "vsim_expr",
    "vsim_expr_xprop",
    "vsim_noexpr",
    "vsim_noexpr_xprop",
    "sat",
    "sat_xprop",
]

if not args.seq:
    all_outputs += ["opt_expr", "opt_expr_xprop"]

if not steps:
    steps = ["clean", "prepare", "verify", *all_outputs, "compare"]

if "clean" in steps:
    for output in all_outputs:
        try:
            os.unlink(f"{output}.out")
        except FileNotFoundError:
            pass


def yosys(command):
    subprocess.check_call(["../../../yosys", "-Qp", command])

def remove(file):
    try:
        os.unlink(file)
    except FileNotFoundError:
        pass


def vcdextract(signals, on_change, file, output, limit=None):
    scope = []
    ids = {}
    prefix = []

    for line in file:
        line = prefix + line.split()
        if line[-1] != "$end":
            prefix = line
            continue
        prefix = []

        if not line:
            continue
        if line[0] == "$scope":
            scope.append(line[2].lstrip("\\"))
        elif line[0] == "$upscope":
            scope.pop()
        elif line[0] == "$var":
            ids[".".join(scope + [line[4].lstrip("\\")])] = line[3]
        elif line[0] == "$enddefinitions":
            break
        elif line[0] in ["$version", "$date", "$comment"]:
            continue
        else:
            raise RuntimeError(f"unexpected input in vcd {line}")

    dump_pos = {}

    for i, sig in enumerate(signals + on_change):
        dump_pos[ids[sig]] = i

    values = [None] * len(signals + on_change)

    last_values = []

    counter = 0

    for line in file:
        if line.startswith("#"):
            if None in values:
                continue

            if values != last_values:
                last_values = list(values)
                if limit is None or counter < limit:
                    print(*values[:len(signals)], file=output)
                    counter += 1
            continue

        if line.startswith("b"):
            value, id = line[1:].split()
        else:
            value, id = line[:1], line[1:]

        pos = dump_pos.get(id)
        if pos is None:
            continue

        values[pos] = value

    if values != last_values:
        if limit is None or counter < limit:
            print(*values[:len(signals)], file=output)


share = Path(__file__).parent / ".." / ".." / "share"

simlibs = [str(share / "simlib.v"), str(share / "simcells.v")]

if "prepare" in steps:
    yosys(
        """
            read_verilog -icells uut.v
            hierarchy -top uut; proc -noopt
            write_rtlil uut.il
            dump -o ports.list uut/x:*
        """
    )

inputs = []
outputs = []

with open("ports.list") as ports_file:
    for line in ports_file:
        line = line.split()
        if not line or line[0] != "wire":
            continue
        line = line[1:]
        width = 1
        if line[0] == "width":
            width = int(line[1])
            line = line[2:]
        direction, seq, name = line
        assert name.startswith("\\")
        name = name[1:]
        seq = int(seq)

        if direction == "input":
            inputs.append((seq, name, width))
        else:
            outputs.append((seq, name, width))

inputs.sort()
outputs.sort()

input_width = sum(width for seq, name, width in inputs)
output_width = sum(width for seq, name, width in outputs)

if "prepare" in steps:
    if args.seq:
        patterns = [''.join(random.choices('01x', k=input_width)) for i in range(args.count)]
    else:
        if 3**input_width <= args.count * 2:
            patterns = ["".join(bits) for bits in itertools.product(*["01x"] * input_width)]
        else:
            patterns = set()

            for bit in '01x':
                patterns.add(bit * input_width)

            for bits in itertools.combinations('01x', 2):
                for bit1, bit2 in itertools.permutations(bits):
                    for i in range(input_width):
                        pattern = [bit1] * input_width
                        pattern[i] = bit2
                        patterns.add(''.join(pattern))

                    for i, j in itertools.combinations(range(input_width), 2):
                        pattern = [bit1] * input_width
                        pattern[i] = bit2
                        pattern[j] = bit2
                        patterns.add(''.join(pattern))

            for bit1, bit2, bit3 in itertools.permutations('01x'):
                for i, j in itertools.combinations(range(input_width), 2):
                    pattern = [bit1] * input_width
                    pattern[i] = bit2
                    pattern[j] = bit3
                    patterns.add(''.join(pattern))

            if len(patterns) > args.count // 2:
                patterns = sorted(patterns)
                random.shuffle(patterns)
                patterns = set(patterns[:args.count // 2])

            while len(patterns) < args.count:
                pattern = ''.join(random.choices('01x', k=input_width))
                patterns.add(pattern)

        patterns = sorted(patterns)
    with open("patterns.list", "w") as f:
        for pattern in patterns:
            print(pattern, file=f)
else:
    with open("patterns.list") as f:
        patterns = [pattern.strip() for pattern in f]


if "prepare" in steps:
    with open("wrapper.v", "w") as wrapper_file:
        print(
            "module wrapper("
            f"input [{input_width-1}:0] A, "
            f"output [{output_width-1}:0] Y);",
            file=wrapper_file,
        )

        connections = []
        pos = 0
        for seq, name, width in inputs:
            connections.append(f".{name}(A[{pos+width-1}:{pos}])")
            pos += width
        pos = 0
        for seq, name, width in outputs:
            connections.append(f".{name}(Y[{pos+width-1}:{pos}])")
            pos += width

        print(f"uut uut({', '.join(connections)});", file=wrapper_file)
        print("endmodule", file=wrapper_file)

    yosys(
        """
            read_rtlil uut.il
            read_verilog wrapper.v
            hierarchy -top wrapper; proc -noopt
            flatten; clean;
            rename wrapper uut
            write_rtlil wrapped.il
        """
    )

    try:
        yosys(
            """
                read_rtlil wrapped.il
                dffunmap
                xprop -required
                check -assert
                write_rtlil wrapped_xprop.il
            """
        )
    except subprocess.CalledProcessError:
        remove("wrapped_xprop.il")

    with open("verilog_sim_tb.v", "w") as tb_file:
        print("module top();", file=tb_file)
        print(f"reg gclk;", file=tb_file)
        print(f"reg [{input_width-1}:0] A;", file=tb_file)
        print(f"wire [{output_width-1}:0] Y;", file=tb_file)
        print(f"uut uut(.A(A), .Y(Y));", file=tb_file)
        print("initial begin", file=tb_file)

        for pattern in patterns:
            # A[0] might be the clock which requires special sequencing
            print(
                f'    #0; gclk = 1; #0; A[0] = 1\'b{pattern[-1]}; #0; A = {input_width}\'b{pattern}; #5; gclk = 0; $display("%b %b", A, Y); #5',
                file=tb_file,
            )

        print("    $finish(0);", file=tb_file)
        print("end", file=tb_file)
        print("endmodule", file=tb_file)

    with open("synth_tb.v", "w") as tb_file:
        print("module top(input clk);", file=tb_file)
        print(f"reg [{len(patterns).bit_length() - 1}:0] counter = 0;", file=tb_file)
        print(f"reg [{input_width-1}:0] A;", file=tb_file)
        print(f"(* gclk *) reg gclk;", file=tb_file)
        print(f"wire [{output_width-1}:0] Y;", file=tb_file)
        print(f"uut uut(.A(A), .Y(Y));", file=tb_file)
        print(f"always @(posedge gclk) counter <= counter + 1;", file=tb_file)
        print(f"always @* case (counter)", file=tb_file)
        for i, pattern in enumerate(patterns):
            print(f"    {i:7} : A = {input_width}'b{pattern};", file=tb_file)
        print(f"    default : A = {input_width}'b{'x' * input_width};", file=tb_file)
        print(f"endcase", file=tb_file)
        print("endmodule", file=tb_file)

    with open("const_tb.v", "w") as tb_file:
        print("module top();", file=tb_file)
        for i, pattern in enumerate(patterns):
            print(
                f"(* keep *) wire [{output_width-1}:0] Y_{i}; "
                f"uut uut_{i}(.A({input_width}'b{pattern}), .Y(Y_{i}));",
                file=tb_file,
            )
        print("endmodule", file=tb_file)

if "verify" in steps:
    try:
        seq_args = " -tempinduct -set-init-undef" if args.seq else ""
        yosys(
            f"""
                read_rtlil wrapped.il
                copy uut gold
                rename uut gate
                design -push-copy
                dffunmap
                xprop -formal -split-inputs -required -debug-asserts gate
                clk2fflogic
                sat{seq_args} -enable_undef -set-def-inputs -prove-asserts -verify -show-all gate
                design -pop

                dffunmap
                xprop -required -assume-encoding gate
                miter -equiv -make_assert -flatten gold gate miter
                clk2fflogic
                sat{seq_args} -enable_undef -set-assumes -prove-asserts -verify -show-all miter
            """
        )
        with open("verified", "w") as f:
            pass
    except subprocess.CalledProcessError:
        remove("verified")


for mode in ["", "_xprop"]:
    if not Path(f"wrapped{mode}.il").is_file():
        for expr in [f"expr{mode}", f"noexpr{mode}"]:
            remove(f"vsim_{expr}.out")
        continue

    if "prepare" in steps:
        yosys(
            f"""
                read_rtlil wrapped{mode}.il
                chformal -remove
                dffunmap
                write_verilog -noexpr vsim_noexpr{mode}.v
                write_verilog -noparallelcase vsim_expr{mode}.v
            """
        )

    for expr in [f"expr{mode}", f"noexpr{mode}"]:
        if f"vsim_{expr}" in steps:
            subprocess.check_call(
                [
                    "iverilog",
                    "-DSIMLIB_FF",
                    "-DSIMLIB_GLOBAL_CLOCK=top.gclk",
                    f"-DDUMPFILE=\"vsim_{expr}.vcd\"",
                    "-o",
                    f"vsim_{expr}",
                    "verilog_sim_tb.v",
                    f"vsim_{expr}.v",
                    *simlibs,
                ]
            )
            with open(f"vsim_{expr}.out", "w") as f:
                subprocess.check_call(["vvp", f"./vsim_{expr}"], stdout=f)

for mode in ["", "_xprop"]:
    if f"sim{mode}" not in steps:
        continue
    if not Path(f"wrapped{mode}.il").is_file():
        remove(f"sim{mode}.out")
        continue
    yosys(
        f"""
            read_verilog synth_tb.v
            read_rtlil wrapped{mode}.il
            hierarchy -top top; proc -noopt
            dffunmap
            sim -clock clk -n {len(patterns) // 2} -vcd sim{mode}.vcd top
        """
    )

    with open(f"sim{mode}.vcd") as fin, open(f"sim{mode}.out", "w") as fout:
        vcdextract(["top.A", "top.Y"], ["top.counter"], fin, fout, len(patterns))

for mode in ["", "_xprop"]:
    if f"sat{mode}" not in steps:
        continue
    if not Path(f"wrapped{mode}.il").is_file():
        remove(f"sat{mode}.out")
        continue
    chunk_size = len(patterns) if args.seq else 32
    last_progress = 0
    with open(f"sat{mode}.ys", "w") as ys:
        for chunk_start in range(0, len(patterns), chunk_size):
            chunk = patterns[chunk_start : chunk_start + chunk_size]
            progress = (10 * chunk_start) // len(patterns)
            if progress > last_progress:
                print(f"log sat {progress}0%", file=ys)
                last_progress = progress

            append = "-a" if chunk_start else "-o"
            print(
                end=f"tee -q {append} sat{mode}.log sat -set-init-undef -seq {len(chunk)}"
                " -show A -show Y -dump_vcd sat.vcd -enable_undef",
                file=ys,
            )
            for i, pattern in enumerate(chunk, 1):
                ad = pattern.replace("x", "0")
                ax = pattern.replace("1", "0").replace("x", "1")
                print(end=f" -set-at {i} A {input_width}'b{pattern}", file=ys)
            print(file=ys)
        print(f"log sat 100%", file=ys)

    try:
        yosys(
            f"""
                read_rtlil wrapped{mode}.il
                clk2fflogic
                script sat{mode}.ys
            """
        )
    except subprocess.CalledProcessError:
        remove(f"sat{mode}.out")
    else:
        sig_re = re.compile(
            r" *[0-9]+ +\\([AY]) +(?:--|[0-9]+) +(?:--|[0-9a-f]+) +([01x]+)"
        )
        current_input = None
        with open(f"sat{mode}.log") as logfile, open(f"sat{mode}.out", "w") as outfile:
            for line in logfile:
                match = sig_re.match(line)
                if match:
                    if match[1] == "A":
                        current_input = match[2]
                    else:
                        print(current_input, match[2], file=outfile)

for mode in ["", "_xprop"]:
    if f"opt_expr{mode}" not in steps:
        continue
    if not Path(f"wrapped{mode}.il").is_file():
        remove(f"opt_expr{mode}.out")
        continue
    yosys(
        f"""
            read_verilog const_tb.v
            read_rtlil wrapped{mode}.il
            hierarchy -top top; proc -noopt
            flatten
            opt_expr -keepdc; clean
            dump -o opt_expr{mode}.list */\Y_*
        """
    )

    values = []

    connect_re = re.compile(r" *connect +\\Y_([0-9]+) +[0-9]+'([01x]+)$")
    with open(f"opt_expr{mode}.list") as connections:
        for line in connections:
            match = connect_re.match(line)
            if match:
                seq = int(match[1])
                data = match[2]
                if len(data) < output_width:
                    data = data * output_width
                values.append((seq, data))

        values.sort()

        with open(f"opt_expr{mode}.out", "w") as outfile:
            for seq, data in values:
                print(patterns[seq], data, file=outfile)


if "compare" in steps:
    groups = {}
    missing = []

    for output in all_outputs:
        try:
            with open(f"{output}.out") as f:
                groups.setdefault(f.read(), []).append(output)
        except FileNotFoundError:
            missing.append(output)

    verified = Path(f"verified").is_file()

    with open("status", "w") as status:
        name = Path('.').absolute().name

        status_list = []

        if len(groups) > 1:
            status_list.append("mismatch")
        if not verified:
            status_list.append("failed-verify")
        if missing:
            status_list.append("missing")
        if not status_list:
            status_list.append("ok")
        print(f"{name}: {', '.join(status_list)}", file=status)

        if len(groups) > 1:
            print("output differences:", file=status)
            for group in groups.values():
                print("  -", *group, file=status)
        if missing:
            print("missing:", file=status)
            print("  -", *missing, file=status)

    with open("status") as status:
        print(end=status.read())
