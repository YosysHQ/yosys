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

def random_expression(depth = 3, maxparam = 0):
    def recursion():
        return random_expression(depth = depth-1, maxparam = maxparam)
    if depth == 0:
        if maxparam != 0 and random.randint(0, 1) != 0:
            return 'p%02d' % random.randint(0, maxparam-1)
        return random.choice([ '%e', '%f', '%g' ]) % random.uniform(-2, +2)
    if random.randint(0, 4) == 0:
        return recursion() + random.choice([ ' < ', ' <= ', ' == ', ' != ', ' >= ', ' > ' ]) + recursion() + ' ? ' + recursion() + ' : ' + recursion()
    op_prefix = [ '+(', '-(' ]
    op_infix = [ ' + ', ' - ', ' * ', ' / ' ]
    op_func1 = [ '$ln', '$log10', '$exp', '$sqrt', '$floor', '$ceil', '$sin', '$cos', '$tan', '$asin', '$acos', '$atan', '$sinh', '$cosh', '$tanh', '$asinh', '$acosh', '$atanh' ]
    op_func2 = [ '$pow', '$atan2', '$hypot' ]
    op = random.choice(op_prefix + op_infix + op_func1 + op_func2)
    if op in op_prefix:
        return op + recursion() + ')'
    if op in op_infix:
        return '(' + recursion() + op + recursion() + ')'
    if op in op_func1:
        return op + '(' + recursion() + ')'
    if op in op_func2:
        return op + '(' + recursion() + ', ' + recursion() + ')'
    raise

for i in range(3): 
    with file('uut_%05d.v' % i, 'w') as f, redirect_stdout(f):
        print('module uut_%05d(output [63:0] %s);\n' % (i, ', '.join(['y%02d' % i for i in range(100)])))
        for i in range(30):
            print('localparam p%02d = %s;' % (i, random_expression()))
        for i in range(30, 60):
            print('localparam p%02d = %s;' % (i, random_expression(maxparam = 30)))
        for i in range(100):
            print('assign y%02d = %s;' % (i, random_expression(maxparam = 60)))
        print('endmodule')
 
