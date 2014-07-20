#!/usr/bin/python

from __future__ import division
from __future__ import print_function

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

def maybe_plus_e(expr):
    if random.randint(0, 4) == 0:
        return "(%s + e)" % expr
    else:
        return expr

for idx in range(100):
    with file('temp/uut_%05d.v' % idx, 'w') as f, redirect_stdout(f):
        print('module uut_%05d(a, b, c, d, e, s, y);' % (idx))
        ac_signed = random.choice(['', ' signed'])
        bd_signed = random.choice(['', ' signed'])
        op = random.choice(['+', '-', '*', '/', '%', '<<', '>>', '<<<', '>>>'])
        print('  input%s [%d:0] a;' % (ac_signed, random.randint(0, 8)))
        print('  input%s [%d:0] b;' % (bd_signed, random.randint(0, 8)))
        print('  input%s [%d:0] c;' % (ac_signed, random.randint(0, 8)))
        print('  input%s [%d:0] d;' % (bd_signed, random.randint(0, 8)))
        print('  input signed [%d:0] e;' % random.randint(0, 8))
        print('  input s;')
        print('  output [%d:0] y;' % random.randint(0, 8))
        print('  assign y = (s ? %s(%s %s %s) : %s(%s %s %s))%s;' %
                (random.choice(['', '$signed', '$unsigned']), maybe_plus_e('a'), op, maybe_plus_e('b'),
                 random.choice(['', '$signed', '$unsigned']), maybe_plus_e('c'), op, maybe_plus_e('d'),
                 ' + e' if random.randint(0, 4) == 0 else ''))
        print('endmodule')
    with file('temp/uut_%05d.ys' % idx, 'w') as f, redirect_stdout(f):
        print('read_verilog temp/uut_%05d.v' % idx)
        print('proc;;')
        print('copy uut_%05d gold' % idx)
        print('rename uut_%05d gate' % idx)
        print('share -aggressive gate')
        print('miter -equiv -flatten -ignore_gold_x -make_outputs -make_outcmp gold gate miter')
        print('sat -set-def-inputs -verify -prove trigger 0 -show-inputs -show-outputs miter')
 
