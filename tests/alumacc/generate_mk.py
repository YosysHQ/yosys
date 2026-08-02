#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

import argparse
import random
from itertools import product

TEMPLATE=r"""read_rtlil << EOT
module \top
  wire width {a_width} input 1 signed \a
  wire width {b_width} input 2 signed \b
  wire output 3 \x
  wire width {y_width} output 4 \y
  cell ${c1} \c1
    parameter \A_SIGNED {c1_signed}
    parameter \B_SIGNED {c1_signed}
    parameter \A_WIDTH {a_width}
    parameter \B_WIDTH {b_width}
    parameter \Y_WIDTH 1
    connect \A \a
    connect \B \b
    connect \Y \x
  end
  cell ${c2} \c2
    parameter \A_SIGNED {c2_signed}
    parameter \B_SIGNED {c2_signed}
    parameter \A_WIDTH {a_width}
    parameter \B_WIDTH {b_width}
    parameter \Y_WIDTH {y_width}
    connect \A \a
    connect \B \b
    connect \Y \y
  end
end
EOT
equiv_opt -assert alumacc
design -load postopt
{postopt_assert}
"""

EQ = ["eq", "eqx", "ne", "nex"]
LGE = ["lt", "gt"]
CMP = EQ + LGE
ARITH = ["add", "sub"]
SIGNED = [0, 1]
WIDTH = list(range(1, 4))

parser = argparse.ArgumentParser(formatter_class = argparse.ArgumentDefaultsHelpFormatter)
parser.add_argument('-S', '--seed',  type = int, help = 'seed for PRNG')
args = parser.parse_args()

seed = args.seed
if seed is None:
    seed = random.randrange(sys.maxsize)
print("alumacc PRNG seed: %d" % seed)
random.seed(seed)

count = 0
for c1_signed, c2, c2_signed, a_width in product(
    SIGNED, [EQ, LGE, ARITH], SIGNED, WIDTH
):
    c1 = random.choice(LGE)
    if isinstance(c2, list):
        c2 = random.choice(c2)

    b_widths: list[int]
    if a_width == 2:
      b_widths = [1, 2, 3]
    else:
      b_widths = [a_width]
    y_widths: list[int]
    if c2 in CMP:
        y_widths = [1]
    else:
        y_widths = b_widths

    for b_width, y_width in product(b_widths, y_widths):
        out_cells = "t:$alu"
        for c in c1, c2:
            if c in EQ:
                # LGE cells will always remap to $alu, but EQ cells only will if merged
                out_cells += f" t:${c}"

        undersized = c2 in ARITH and y_width < max(a_width, b_width)
        mixed_sign = c1_signed != c2_signed and a_width != b_width
        if c2 != "add" and not undersized and not mixed_sign:
            # cells correctly merged
            postopt_assert = f"select -assert-count 1 {out_cells}"
        else:
            # currently these all produce 2, but assert-max allows for future improvement
            postopt_assert = f"select -assert-max 2 {out_cells}"

        with open(f"uut_{'s' if c1_signed else 'u'}{c1}_{'s' if c2_signed else 'u'}{c2}_{a_width}_{b_width}_{y_width}.ys", "w") as f:
            print(str.format_map(TEMPLATE, locals()), file=f)
            count = count + 1

# print(count)

gen_tests_makefile.generate(["--yosys-scripts"])
