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

for idx in range(100):
    with file('temp/uut_%05d.v' % idx, 'w') as f, redirect_stdout(f):
        print('module uut_%05d(a, b, c, d, s, y);' % (idx))
        ac_signed = random.choice(['', ' signed'])
        bd_signed = random.choice(['', ' signed'])
        op = random.choice(['+', '-', '*', '/', '%', '<<', '>>', '<<<', '>>>'])
        print('  input%s [%d:0] a;' % (ac_signed, random.randint(0, 8)))
        print('  input%s [%d:0] b;' % (bd_signed, random.randint(0, 8)))
        print('  input%s [%d:0] c;' % (ac_signed, random.randint(0, 8)))
        print('  input%s [%d:0] d;' % (bd_signed, random.randint(0, 8)))
        print('  input s;')
        print('  output [%d:0] y;' % random.randint(0, 8))
        print('  assign y = s ? %s(a %s b) : %s(c %s d);' % (random.choice(['', '$signed', '$unsigned']), op, random.choice(['', '$signed', '$unsigned']), op))
        print('endmodule')
    with file('temp/uut_%05d.ys' % idx, 'w') as f, redirect_stdout(f):
        print('read_verilog temp/uut_%05d.v' % idx)
        print('proc;;')
        print('copy uut_%05d gold' % idx)
        print('rename uut_%05d gate' % idx)
        print('share -aggressive gate')
        print('miter -equiv -ignore_gold_x -make_outputs -make_outcmp gold gate miter')
        print('flatten miter')
        print('sat -verify -prove trigger 0 -show-inputs -show-outputs miter')
 
