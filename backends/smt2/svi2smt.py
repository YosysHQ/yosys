#
# yosys -- Yosys Open SYnthesis Suite
#
# Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#

from collections import namedtuple

Op = namedtuple("Op", ["op", "args", "tail"], defaults=[list, ""])

def pp(v, indent=""):
    if isinstance(v, Op):
        lit = True
        if isinstance(v.args, list):
            for a in v.args:
                if isinstance(a, str): continue
                if isinstance(a, int): continue
                lit = False
        if lit:
            print(indent + v.op + " " + str(v.args))
        else:
            print(indent + v.op + ":")
            pp(v.args, indent=indent+"  ")
    elif isinstance(v, list):
        for a in v:
            pp(a, indent=indent)
    elif isinstance(v, str):
        print(indent + '"' + v + '"')
    else:
        print(indent + "=" + str(v))

class SviParserError(Exception):
    def __init__(self, text, expected):
        self.text = text
        self.expected = expected

def parse_str(text, s):
    text = text.lstrip()
    if not text.startswith(s):
        raise SviParserError(text, s)
    return Op("str", [s], text[len(s):])

def parse_binop(text, ops, arg_parser, assoc="L"):
    text = text.lstrip()
    args = [arg_parser(text)]
    opers = []

    while True:
        for op, cmd in ops:
            try:
                q = parse_str(args[-1].tail, op)
                q = arg2_parser(q.tail)
                args.append(q)
                opers.append(cmd)
            except SviParserError:
                pass
        else:
            break

    if len(opers) == 1:
        args, opers = [Op(opers[0], args, args[-1].tail)], []
    elif assoc == "L":
        while len(opers) > 1:
            args = [Op(opers[0], args[0:2], args[1].tail), *args[2:]]
            opers = opers[1:]
    elif assoc == "R":
        while len(opers) > 1:
            args = [Op(opers[-1], args[-2:], args[-1].tail), *args[0:-2]]
            opers = opers[:-1]
    else:
        assert False

    return args[0]

def parse_int(text, label, base, digits):
    text = text.lstrip()
    tail = text.lstrip(digits)

    if len(text) == len(tail) or text.startswith("_"):
        raise SviParserError(text, label)

    text = text[:-len(tail)].replace("_", "")
    return Op("int", int(text, base), tail)

def parse_dec(text):
    return parse_int(text, "dec", 10, "0123456789_")

def parse_hex(text):
    return parse_int(text, "hex", 16, "0123456789abcdefABCDEF_")

def parse_bin(text):
    return parse_int(text, "bin", 2, "01_")

def parse_name(text):
    text = text.lstrip()

    tail = text
    if len(tail) and tail[0].isalpha():
        tail = tail[1:]
        while len(tail) and tail[0].isalnum():
            tail = tail[1:]

    if len(text) == len(tail):
        raise SviParserError(text, "name")

    return Op("name", text[:-len(tail)], tail)

# const: dec
# const: dec 'h hex
# const: dec 'b bin
def parse_const(text):
    p = parse_dec(text)

    try:
        q = parse_str(p.tail, "'h")
        q = parse_hex(q.tail)
        return Op("const", [p.args, q.args], q.tail)
    except SviParserError:
        pass

    try:
        q = parse_str(p.tail, "'b")
        q = parse_bin(q.tail)
        return Op("const", [p.args, q.args], q.tail)
    except SviParserError:
        pass

    return Op("const", [32, p.args], p.tail)

# signal: name
# signal: name [ idx ]
# signal: name [ msb : lsb ]
# signal: name [ lsb +: width ]
def parse_signal(text):
    p = parse_name(text)

    try:
        q = parse_str(p.tail, "[")
        q = parse_dec(q.tail)

        try:
            r = parse_str(q.tail, ":")
            r = parse_dec(r.tail)
            s = parse_str(r.tail, "]")
            return Op("signal", [p.args, r.args, q.args-r.args+1], s.tail)
        except SviParserError:
            pass

        try:
            r = parse_str(q.tail, "+:")
            r = parse_dec(r.tail)
            s = parse_str(r.tail, "]")
            return Op("signal", [p.args, q.args, r.args], s.tail)
        except SviParserError:
            pass

        r = parse_str(q.tail, "]")
        return Op("signal", [p.args, q.args], r.tail)
    except SviParserError:
        pass

    return Op("signal", [p.args], p.tail)

# lvl0:
#   "!" lvl0
#   "~" lvl0
#   const
#   signal
#   "(" expr ")"
def parse_lvl0(text):
    try:
        p = parse_str(text, "!")
        p = parse_atom(p.tail)
        return Op("not", [p], p.tail)
    except SviParserError:
        pass

    try:
        return parse_const(text)
    except SviParserError:
        pass

    try:
        return parse_signal(text)
    except SviParserError:
        pass

    p = parse_str(text, "(")
    p = parse_expr(p.tail)
    q = parse_str(p.tail, ")")
    return p._replace(tail=q.tail)

# lvl1:
#   lvl0
#   lvl1 + lvl0
#   lvl1 - lvl0
def parse_lvl1(text):
    return parse_binop(text, [("+", "add"), ("-", "sub")], parse_lvl0)

# lvl2:
#   lvl2 "<<" lvl1
#   lvl2 ">>" lvl1
def parse_lvl2(text):
    return parse_binop(text, [("<<", "shl"), (">>", "shr")], parse_lvl1)

# lvl3:
#   lvl3 ("<"|">"|"<="|">="|"=="|"!=") lvl2
def parse_lvl3(text):
    return parse_binop(text, [
        ("<", "lt"),
        (">", "gt"),
        ("<=", "le"),
        (">=", "ge"),
        ("==", "eq"),
        ("!=", "ne")
    ], parse_lvl2)

# lvl4:
#   lvl3 op lvl3
def parse_lvl4(text):
    return parse_binop(text, [("&", "or")], parse_lvl3)

# lvl5:
#   lvl4 op lvl4
def parse_lvl4(text):
    return parse_binop(text, [("&", "or")], parse_lvl3)

# lvlN:
#   lvlN op lvlK
def parse_lvlN(text):
    return parse_binop(text, [("|", "or")], parse_lvlK)

# term: sum
# term: sum ^ term
def parse_term(text):
    return parse_binop(text, [("^", "xor")], parse_sum, parse_term)

# expr: term
# expr: term < term
# expr: term > term
# expr: term <= term
# expr: term >= term
# expr: term == term
# expr: term != term
def parse_expr(text):
    return parse_binop(text, [
        ("<", "lt"),
        (">", "gt"),
        ("<=", "le"),
        (">=", "ge"),
        ("==", "eq"),
        ("!=", "ne")
    ], parse_term)

# conj: expr
# conj: expr "and" conj
def parse_conj(text):
    return parse_binop(text, [("and", "conj")], parse_expr, parse_conj)

# prop:
#   expr "|->" conj ";"
#   expr ";"
def parse_prop(text):
    p = parse_binop(text, [("|->", "impl")], parse_expr, parse_conj)
    q = parse_str(p.tail, ";")
    return p._replace(tail=q.tail)

if __name__ == '__main__':
    if False:
        import fileinput
        with fileinput.input() as f:
            svi_text = "".join(f).rstrip()
    else:
        svi_text = """
1 & S[1] |-> S[3:2] and 8'h a_B | S[2+:2] | 1 ^ 3 'b 101 == S;

a
  |-> b
  and (c & d) == e;

x |-> c > d;
        """.strip()

    print("--- Input ---")
    print(svi_text)
    print("-------------")

    props = []
    try:
        while len(svi_text):
            props.append(parse_prop(svi_text))
            svi_text = props[-1].tail
    except SviParserError as e:
        print(e)

    if len(props) == 1:
        props = props[0]
    else:
        props = Op("conj", props, svi_text)

    print()
    print("--- Property ---")
    pp(props)
    print("----------------")
