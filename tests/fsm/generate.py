#!/usr/bin/env python3

import argparse
import sys
import random
from contextlib import contextmanager

# set to 'True' to compare verific with yosys
test_verific = False

@contextmanager
def redirect_stdout(new_target):
    old_target, sys.stdout = sys.stdout, new_target
    try:
        yield new_target
    finally:
        sys.stdout = old_target

def random_expr(variables):
    c = random.choice(['bin', 'uni', 'var', 'const'])
    if c == 'bin':
        op = random.choice(['+', '-', '*', '<', '<=', '==', '!=', '>=', '>', '<<', '>>', '<<<', '>>>', '|', '&', '^', '~^', '||', '&&'])
        return "(%s %s %s)" % (random_expr(variables), op, random_expr(variables))
    if c == 'uni':
        op = random.choice(['+', '-', '~', '|', '&', '^', '~^', '!', '$signed', '$unsigned'])
        return "%s(%s)" % (op, random_expr(variables))
    if c == 'var':
        return random.choice(variables)
    if c == 'const':
        bits = random.randint(1, 32)
        return "%d'd%s" % (bits, random.randint(0, 2**bits-1))
    raise AssertionError

parser = argparse.ArgumentParser(formatter_class = argparse.ArgumentDefaultsHelpFormatter)
parser.add_argument('-S', '--seed',  type = int, help = 'seed for PRNG')
parser.add_argument('-c', '--count', type = int, default = 50, help = 'number of test cases to generate')
args = parser.parse_args()

if args.seed is not None:
    print("PRNG seed: %d" % args.seed)
    random.seed(args.seed)

for idx in range(args.count):
    with open('temp/uut_%05d.v' % idx, 'w') as f:
        with redirect_stdout(f):
            rst2 = random.choice([False, True])
            if rst2:
                print('module uut_%05d(clk, rst1, rst2, rst, a, b, c, x, y, z);' % (idx))
                print('  input clk, rst1, rst2;')
                print('  output rst;')
                print('  assign rst = rst1 || rst2;')
            else:
                print('module uut_%05d(clk, rst, a, b, c, x, y, z);' % (idx))
                print('  input clk, rst;')
            variables=['a', 'b', 'c', 'x', 'y', 'z']
            print('  input%s [%d:0] a;' % (random.choice(['', ' signed']), random.randint(0, 31)))
            print('  input%s [%d:0] b;' % (random.choice(['', ' signed']), random.randint(0, 31)))
            print('  input%s [%d:0] c;' % (random.choice(['', ' signed']), random.randint(0, 31)))
            print('  output reg%s [%d:0] x;' % (random.choice(['', ' signed']), random.randint(0, 31)))
            print('  output reg%s [%d:0] y;' % (random.choice(['', ' signed']), random.randint(0, 31)))
            print('  output reg%s [%d:0] z;' % (random.choice(['', ' signed']), random.randint(0, 31)))
            state_bits = random.randint(5, 16);
            print('  %sreg [%d:0] state;' % (random.choice(['', '(* fsm_encoding = "one-hot" *)',
                    '(* fsm_encoding = "binary" *)']), state_bits-1))
            states=[]
            for i in range(random.randint(2, 10)):
                n = random.randint(0, 2**state_bits-1)
                if n not in states:
                    states.append(n)
            print('  always @(posedge clk) begin')
            print('    if (%s) begin' % ('rst1' if rst2 else 'rst'))
            print('      x <= %d;' % random.randint(0, 2**31-1))
            print('      y <= %d;' % random.randint(0, 2**31-1))
            print('      z <= %d;' % random.randint(0, 2**31-1))
            print('      state <= %d;' % random.choice(states))
            print('    end else begin')
            print('      case (state)')
            for state in states:
                print('        %d: begin' % state)
                for var in ('x', 'y', 'z'):
                    print('            %s <= %s;' % (var, random_expr(variables)))
                next_states = states[:]
                for i in range(random.randint(0, len(states))):
                    next_state = random.choice(next_states)
                    next_states.remove(next_state)
                    print('            if ((%s) %s (%s)) state <= %s;' % (random_expr(variables),
                            random.choice(['<', '<=', '>=', '>']), random_expr(variables), next_state))
                print('          end')
            print('      endcase')
            if rst2:
                print('      if (rst2) begin')
                print('        x <= a;')
                print('        y <= b;')
                print('        z <= c;')
                print('        state <= %d;' % random.choice(states))
                print('      end')
            print('    end')
            print('  end')
            print('endmodule')
    with open('temp/uut_%05d.ys' % idx, 'w') as f:
        with redirect_stdout(f):
            if test_verific:
                print('read_verilog temp/uut_%05d.v' % idx)
                print('proc;; rename uut_%05d gold' % idx)
                print('verific -vlog2k temp/uut_%05d.v' % idx)
                print('verific -import uut_%05d' % idx)
                print('rename uut_%05d gate' % idx)
            else:
                print('read_verilog temp/uut_%05d.v' % idx)
                print('proc;;')
                print('copy uut_%05d gold' % idx)
                print('rename uut_%05d gate' % idx)
                print('cd gate')
                print('opt; wreduce; share%s; opt; fsm;;' % random.choice(['', ' -aggressive']))
                print('cd ..')
            print('miter -equiv -flatten -ignore_gold_x -make_outputs -make_outcmp gold gate miter')
            print('sat -verify-no-timeout -timeout 20 -seq 5 -set-at 1 %s_rst 1 -prove trigger 0 -prove-skip 1 -show-inputs -show-outputs miter' % ('gold' if rst2 else 'in'))

