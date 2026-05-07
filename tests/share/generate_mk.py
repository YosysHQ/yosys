#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

import argparse
import sys
import random
from pathlib import Path

def random_plus_x():
    return "%s x" % random.choice(['+', '+', '+', '-', '-', '|', '&', '^'])

def maybe_plus_x(expr):
    if random.randint(0, 4) == 0:
        return "(%s %s)" % (expr, random_plus_x())
    else:
        return expr

parser = argparse.ArgumentParser(formatter_class = argparse.ArgumentDefaultsHelpFormatter)
parser.add_argument('-S', '--seed',  type = int, help = 'seed for PRNG')
parser.add_argument('-c', '--count', type = int, default = 100, help = 'number of test cases to generate')
args = parser.parse_args()

seed = args.seed
if seed is None:
    seed = random.randrange(sys.maxsize)
print("share PRNG seed: %d" % seed)
random.seed(seed)

for path in Path(".").glob("uut_*.*"):
    if path.is_file():
        path.unlink()

for idx in range(args.count):
    with open('uut_%05d.v' % idx, 'w') as f:
        with gen_tests_makefile.redirect_stdout(f):
            if random.choice(['bin', 'uni']) == 'bin':
                print('module uut_%05d(a, b, c, d, x, s, y);' % (idx))
                op = random.choice([
                    random.choice(['+', '-', '*', '/', '%']),
                    random.choice(['<', '<=', '==', '!=', '===', '!==', '>=', '>' ]),
                    random.choice(['<<', '>>', '<<<', '>>>']),
                    random.choice(['|', '&', '^', '~^', '||', '&&']),
                ])
                print('  input%s [%d:0] a;' % (random.choice(['', ' signed']), random.randint(0, 8)))
                print('  input%s [%d:0] b;' % (random.choice(['', ' signed']), random.randint(0, 8)))
                print('  input%s [%d:0] c;' % (random.choice(['', ' signed']), random.randint(0, 8)))
                print('  input%s [%d:0] d;' % (random.choice(['', ' signed']), random.randint(0, 8)))
                print('  input%s [%d:0] x;' % (random.choice(['', ' signed']), random.randint(0, 8)))
                print('  input s;')
                print('  output [%d:0] y;' % random.randint(0, 8))
                print('  assign y = (s ? %s(%s %s %s) : %s(%s %s %s))%s;' %
                        (random.choice(['', '$signed', '$unsigned']), maybe_plus_x('a'), op, maybe_plus_x('b'),
                         random.choice(['', '$signed', '$unsigned']), maybe_plus_x('c'), op, maybe_plus_x('d'),
                         random_plus_x() if random.randint(0, 4) == 0 else ''))
                print('endmodule')
            else:
                print('module uut_%05d(a, b, x, s, y);' % (idx))
                op = random.choice(['~', '-', '!'])
                print('  input%s [%d:0] a;' % (random.choice(['', ' signed']), random.randint(0, 8)))
                print('  input%s [%d:0] b;' % (random.choice(['', ' signed']), random.randint(0, 8)))
                print('  input%s [%d:0] x;' % (random.choice(['', ' signed']), random.randint(0, 8)))
                print('  input s;')
                print('  output [%d:0] y;' % random.randint(0, 8))
                print('  assign y = (s ? %s(%s%s) : %s(%s%s))%s;' %
                        (random.choice(['', '$signed', '$unsigned']), op, maybe_plus_x('a'),
                         random.choice(['', '$signed', '$unsigned']), op, maybe_plus_x('b'),
                         random_plus_x() if random.randint(0, 4) == 0 else ''))
                print('endmodule')
    with open('uut_%05d.ys' % idx, 'w') as f:
        with gen_tests_makefile.redirect_stdout(f):
            print('read_verilog uut_%05d.v' % idx)
            print('proc -noopt;;')
            print('copy uut_%05d gold' % idx)
            print('rename uut_%05d gate' % idx)
            print('tee -o uut_%05d.txt wreduce' % idx)
            print('tee -a uut_%05d.txt share -aggressive gate' % idx)
            print('miter -equiv -flatten -ignore_gold_x -make_outputs -make_outcmp gold gate miter')
            print('sat -set-def-inputs -verify -prove trigger 0 -show-inputs -show-outputs miter')
            print('! grep -q \'^Removing [246] cells\' uut_%05d.txt' % idx)

gen_tests_makefile.generate(["--yosys-scripts"])
