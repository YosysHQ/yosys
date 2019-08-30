#!/usr/bin/env python3

import argparse
import sys
import random
from contextlib import contextmanager


@contextmanager
def redirect_stdout(new_target):
    old_target, sys.stdout = sys.stdout, new_target
    try:
        yield new_target
    finally:
        sys.stdout = old_target


def random_plus_x():
    return "%s x" % random.choice(['+', '+', '+', '-', '-', '|', '&', '^'])


def maybe_plus_x(expr):
    if random.randint(0, 4) == 0:
        return "(%s %s)" % (expr, random_plus_x())
    else:
        return expr


parser = argparse.ArgumentParser(
    formatter_class=argparse.ArgumentDefaultsHelpFormatter)
parser.add_argument('-S', '--seed', type=int, help='seed for PRNG')
parser.add_argument('-c',
                    '--count',
                    type=int,
                    default=100,
                    help='number of test cases to generate')
args = parser.parse_args()

if args.seed is not None:
    print("PRNG seed: %d" % args.seed)
    random.seed(args.seed)

for idx in range(args.count):
    with open('temp/uut_%05d.v' % idx, 'w') as f:
        with redirect_stdout(f):
            print('module uut_%05d(a, b, c, s, y);' % (idx))
            op = random.choice([
                random.choice(['+', '-', '*', '/', '%']),
                random.choice(['<', '<=', '==', '!=', '===', '!==', '>=',
                               '>']),
                random.choice(['<<', '>>', '<<<', '>>>']),
                random.choice(['|', '&', '^', '~^', '||', '&&']),
            ])
            print('  input%s [%d:0] a;' % (random.choice(['', ' signed']), 8))
            print('  input%s [%d:0] b;' % (random.choice(['', ' signed']), 8))
            print('  input%s [%d:0] c;' % (random.choice(['', ' signed']), 8))
            print('  input s;')
            print('  output [%d:0] y;' % 8)
            ops1 = ['a', 'b']
            ops2 = ['a', 'c']
            random.shuffle(ops1)
            random.shuffle(ops2)
            cast1 = random.choice(['', '$signed', '$unsigned'])
            cast2 = random.choice(['', '$signed', '$unsigned'])
            print('  assign y = (s ? %s(%s %s %s) : %s(%s %s %s));' %
                  (cast1, ops1[0], op, ops1[1],
                   cast2, ops2[0], op, ops2[1]))
            print('endmodule')

    with open('temp/uut_%05d.ys' % idx, 'w') as f:
        with redirect_stdout(f):
            print('read_verilog temp/uut_%05d.v' % idx)
            print('proc;;')
            print('copy uut_%05d gold' % idx)
            print('rename uut_%05d gate' % idx)
            print('tee -a temp/all_share_log.txt log')
            print('tee -a temp/all_share_log.txt log #job# uut_%05d' % idx)
            print('tee -a temp/all_share_log.txt opt gate')
            print('tee -a temp/all_share_log.txt opt_share gate')
            print('tee -a temp/all_share_log.txt opt_clean gate')
            print(
                'miter -equiv -flatten -ignore_gold_x -make_outputs -make_outcmp gold gate miter'
            )
            print(
                'sat -set-def-inputs -verify -prove trigger 0 -show-inputs -show-outputs miter'
            )
