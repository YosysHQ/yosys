#!/usr/bin/env python3
"""Generate a many-small-modules design.

Mirrors the shape of designs where a parameterized leaf is elaborated into
thousands of distinct modules: the per-module fixed cost of a pass dominates,
not the per-candidate cost. Roughly a third of the leaves carry no arithmetic
at all, which is where a type prefilter has to pay off.
"""
import argparse
import random

parser = argparse.ArgumentParser()
parser.add_argument("-n", "--modules", type=int, default=2000)
parser.add_argument("-w", "--width", type=int, default=16)
parser.add_argument("-d", "--depth", type=int, default=12)
parser.add_argument("-s", "--seed", type=int, default=1)
parser.add_argument("-o", "--out", default="manymod.v")
args = parser.parse_args()

rng = random.Random(args.seed)
W = args.width
D = args.depth

out = []
for i in range(args.modules):
    # 1/3 pure mux/logic (no arith), 1/3 arith, 1/3 compare
    kind = i % 3
    out.append(f"module leaf{i} (input clk, input [{W-1}:0] a, b, c, d,")
    out.append(f"    input [3:0] s, output reg [{W-1}:0] y);")
    out.append(f"  wire [{W-1}:0] m0 = s[0] ? a : b;")
    out.append(f"  wire [{W-1}:0] m1 = s[1] ? c : d;")
    out.append(f"  wire [{W-1}:0] m2 = s[2] ? m0 : m1;")
    out.append(f"  wire [{W-1}:0] st0 = m2;")
    for k in range(D):
        p = f"st{k}"
        n = f"st{k+1}"
        if kind == 0:
            out.append(f"  wire [{W-1}:0] {n} = s[3] ? ({p} ^ a) : (({p} & b) | c);")
        elif kind == 1:
            out.append(f"  wire [{W-1}:0] {n} = (s[3] ? {p} : c) + (a ^ {p});")
        else:
            out.append(f"  wire {n}_p = {p} > a;")
            out.append(f"  wire [{W-1}:0] {n} = {{{p}[{W-2}:0], {n}_p}} ^ (s[3] ? b : c);")
    out.append(f"  always @(posedge clk) y <= st{D} ^ m2;")
    out.append("endmodule")
    out.append("")

out.append(f"module top (input clk, input [{W-1}:0] a, b, c, d, input [3:0] s,")
out.append(f"    output [{W-1}:0] y);")
out.append(f"  wire [{W-1}:0] chain [0:{args.modules}];")
out.append("  assign chain[0] = a;")
for i in range(args.modules):
    out.append(f"  leaf{i} u{i} (clk, chain[{i}], b, c, d, s, chain[{i+1}]);")
out.append(f"  assign y = chain[{args.modules}];")
out.append("endmodule")

with open(args.out, "w") as f:
    f.write("\n".join(out) + "\n")

print(f"wrote {args.out}: {args.modules} leaf modules, width {W}")
