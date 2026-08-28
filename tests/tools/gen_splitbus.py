#!/usr/bin/env python3
"""Generate modules carrying per-lane split buses that are not allocators.

opt_first_fit_alloc draws its root candidates from wires named `foo[k]`, which
a vectorizing frontend emits for every unpacked array in the source. Most of
them are ordinary datapath, so the pass walks their cones and rejects them.
This models that: the split buses are real, the allocator is not there.
"""
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("-n", "--modules", type=int, default=500)
parser.add_argument("-l", "--lanes", type=int, default=8)
parser.add_argument("-e", "--elem", type=int, default=4)
parser.add_argument("-b", "--buses", type=int, default=3)
parser.add_argument("-d", "--depth", type=int, default=10)
parser.add_argument("-o", "--out", default="splitbus.v")
args = parser.parse_args()

N, E, B, D = args.lanes, args.elem, args.buses, args.depth

out = []
for m in range(args.modules):
    out.append(f"module leaf{m} (input clk, input [{N-1}:0] req,")
    out.append(f"    input [{E-1}:0] din, input [{N*E-1}:0] wide, output reg [{N*E-1}:0] y);")
    for b in range(B):
        for k in range(N):
            out.append(f"  wire [{E-1}:0] \\bus{b}[{k}] ;")
    # Lane logic: a rotate/compare mix, deliberately not a first-fit scan.
    for b in range(B):
        for k in range(N):
            src = f"wide[{(k+1)*E-1}:{k*E}]"
            prev = f"\\bus{b}[{(k-1) % N}] "
            out.append(f"  assign \\bus{b}[{k}] = req[{k}] ? ({src} ^ din) : "
                       f"({prev} + {b+1});")
    out.append(f"  wire [{N*E-1}:0] flat0 = {{" +
               ", ".join(f"\\bus0[{k}] " for k in reversed(range(N))) + "};")
    out.append(f"  wire [{N*E-1}:0] flat1 = {{" +
               ", ".join(f"\\bus1[{k}] " for k in reversed(range(N))) + "};")
    out.append(f"  wire [{N*E-1}:0] flat2 = {{" +
               ", ".join(f"\\bus2[{k}] " for k in reversed(range(N))) + "};")
    out.append(f"  wire [{N*E-1}:0] st0 = flat0 ^ flat1 ^ flat2;")
    for k in range(D):
        out.append(f"  wire [{N*E-1}:0] st{k+1} = "
                   f"(st{k} + wide) ^ (req[0] ? st{k} : wide);")
    out.append(f"  always @(posedge clk) y <= st{D};")
    out.append("endmodule")
    out.append("")

out.append(f"module top (input clk, input [{N-1}:0] req, input [{E-1}:0] din,")
out.append(f"    input [{N*E-1}:0] wide, output [{N*E-1}:0] y);")
out.append(f"  wire [{N*E-1}:0] chain [0:{args.modules}];")
out.append("  assign chain[0] = wide;")
for m in range(args.modules):
    out.append(f"  leaf{m} u{m} (clk, req, din, chain[{m}], chain[{m+1}]);")
out.append(f"  assign y = chain[{args.modules}];")
out.append("endmodule")

with open(args.out, "w") as f:
    f.write("\n".join(out) + "\n")

print(f"wrote {args.out}: {args.modules} modules, {B} split buses of {N}x{E}")
