#!/usr/bin/env python3

import argparse
import fileinput
import sys

parser = argparse.ArgumentParser(description='Convert vcd2txt output to tikz-timing line.')
parser.add_argument('filename', metavar='FILE', help='input txt file')
parser.add_argument('signame', metavar='SIG', help='Signal name')
parser.add_argument('-s', metavar='scale', default=1.0, type=float, help='Scale all time spans with this factor')
parser.add_argument('-l', action='store_true', help='Logic signal (high/low)')
parser.add_argument('-b', action='store_true', help='Display binary value')
parser.add_argument('-x', action='store_true', help='Display hex value')
parser.add_argument('-d', action='store_true', help='Display decimal value')
args = parser.parse_args()

start_time = None
stop_time = None
time_val = { }

def value_to_logic(value):
    found_x = False
    for char in value:
        if char == '1':
            return "H"
        if char == 'x':
            found_x = True
    return "U" if found_x else "L"

def value_to_binary(value):
    return "D{%s}" % value

def value_to_hex(value):
    hex_string = ""
    found_def = False
    while len(value) % 4 != 0:
        value = "0" + value
    while len(value) != 0:
        bin_digits = value[0:4]
        hex_digit = 0
        value = value[4:]
        for b in bin_digits:
            if b == '0':
                hex_digit = hex_digit * 2
            elif b == '1':
                hex_digit = hex_digit * 2 + 1
            else:
                hex_digit += 100
        if hex_digit > 15:
            hex_string += "x"
        else:
            found_def = True
            hex_string += "0123456789abcdef"[hex_digit]
    if not found_def:
        return "U";
    return "D{%s}" % hex_string

def value_to_decimal(value):
    val = 0
    found_def = False
    found_undef = False
    for digit in value:
        if digit == 'x':
            found_undef = True
        else:
            val = val*2 + int(digit)
            found_def = True
    if found_def:
        if found_undef:
            return "D{X}"
        else:
            return "D{%d}" % val
    return "U"

for line in fileinput.input(args.filename):
    (node, time, name, value) = line.strip().split('\t')
    time = int(time)
    if start_time is None or start_time > time:
        start_time = time
    if stop_time is None or stop_time < time:
        stop_time = time
    if name == args.signame:
        if args.l:
            time_val[+time] = value_to_logic(value)
        elif args.b:
            time_val[+time] = value_to_binary(value)
        elif args.x:
            time_val[+time] = value_to_hex(value)
        elif args.d:
            time_val[+time] = value_to_decimal(value)
        else:
            time_val[+time] = value

if start_time not in time_val:
    time_val[start_time] = "S"

last_time = None
last_value = None
for t in sorted(time_val.keys()):
    if last_time is not None:
        print("%f%s" % ((t - last_time)*args.s, last_value), end='')
    (last_time, last_value) = (t, time_val[t])
if last_time < stop_time:
    print("%f%s" % ((stop_time - last_time)*args.s, last_value), end='')
print('')

