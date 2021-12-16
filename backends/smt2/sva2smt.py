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

class SvaParserError(Exception):
    def __init__(self, text, expected):
        self.text = text
        self.expected = expected

def parse_str(text, s):
    t1 = text.lstrip()
    if not t1.startswith(s):
        raise SvaParserError(t1, s)
    return ("str", s), t1[len(s):]

def parse_binop(text, ops, arg1_parser, arg2_parser=None):
    if arg2_parser is None:
        arg2_parser = arg1_parser

    t1 = text.lstrip()
    s1, t1 = arg1_parser(t1)

    for op, label, chain in ops:
        try:
            _, t2 = parse_str(t1, op)
            s2, t2 = arg2_parser(t2)
            if chain and s2[0] == label:
                return (label, s1) + s2[1:], t2
            return (label, s1, s2), t2
        except SvaParserError:
            pass

    return s1, t1

def parse_dec(text):
    t1 = text.lstrip()
    t2 = t1.lstrip("0123456789_")

    if len(t1) == len(t2) or t1.startswith("_"):
        raise SvaParserError(t1, "dec")

    n = t1[:-len(t2)].replace("_", "")
    return int(n, 10), t2

def parse_hex(text):
    t1 = text.lstrip()
    t2 = t1.lstrip("0123456789abcdefABCDEF_")

    if len(t1) == len(t2) or t1.startswith("_"):
        raise SvaParserError(t1, "hex")

    n = t1[:-len(t2)].replace("_", "")
    return int(n, 16), t2

def parse_bin(text):
    t1 = text.lstrip()
    t2 = t1.lstrip("01_")

    if len(t1) == len(t2) or t1.startswith("_"):
        raise SvaParserError(t1, "bin")

    n = t1[:-len(t2)].replace("_", "")
    return int(n, 2), t2

def parse_name(text):
    t1 = text.lstrip()

    t2 = t1
    if len(t2) and t2[0].isalpha():
        t2 = t2[1:]
        while len(t2) and t2[0].isalnum():
            t2 = t2[1:]

    if len(t1) == len(t2):
        raise SvaParserError(t1, "name")

    return t1[:-len(t2)], t2

# const: dec
# const: dec 'h hex
# const: dec 'b bin
def parse_const(text):
    s1, t1 = parse_dec(text)

    try:
        _, t2 = parse_str(t1, "'h")
        s2, t2 = parse_hex(t2)
        return ("const", s1, s2), t2
    except SvaParserError:
        pass

    try:
        _, t2 = parse_str(t1, "'b")
        s2, t2 = parse_bin(t2)
        return ("const", s1, s2), t2
    except SvaParserError:
        pass

    return ("const", 32, s1), t1

# signal: name
# signal: name [ idx ]
# signal: name [ msb : lsb ]
# signal: name [ lsb +: width ]
def parse_signal(text):
    s1, t1 = parse_name(text)

    try:
        _, t2 = parse_str(t1, "[")
        s2, t2 = parse_dec(t2)

        try:
            _, t3 = parse_str(t2, ":")
            s3, t3 = parse_dec(t3)
            _, t3 = parse_str(t3, "]")
            return ("signal", s1, s3, s2-s3+1), t3
        except SvaParserError:
            pass

        try:
            _, t3 = parse_str(t2, "+:")
            s3, t3 = parse_dec(t3)
            _, t3 = parse_str(t3, "]")
            return ("signal", s1, s2, s3), t3
        except SvaParserError:
            pass

        _, t2 = parse_str(t2, "]")
        return ("signal", s1, s2), t2
    except SvaParserError:
        pass

    return ("signal", s1), t1

# atom: ! atom
# atom: const
# atom: signal
# atom: ( expr )
def parse_atom(text):
    try:
        _, t = parse_str(text, "!")
        s, t = parse_atom(t)
        return ("not", s), t
    except SvaParserError:
        pass

    try:
        return parse_const(text)
    except SvaParserError:
        pass

    try:
        return parse_signal(text)
    except SvaParserError:
        pass

    _, t = parse_str(text, "(")
    s, t = parse_expr(t)
    _, t = parse_str(t, ")")
    return s, t

# prod: atom
# prod: atom & prod
def parse_prod(text):
    return parse_binop(text, [("&", "and", True)], parse_atom, parse_prod)

# sum: prod
# sum: prod | sum
def parse_sum(text):
    return parse_binop(text, [("|", "or", True)], parse_prod, parse_sum)

# term: sum
# term: sum ^ term
def parse_term(text):
    return parse_binop(text, [("^", "xor", True)], parse_sum, parse_term)

# expr: term
# expr: term < term
# expr: term > term
# expr: term <= term
# expr: term >= term
# expr: term == term
# expr: term != term
def parse_expr(text):
    return parse_binop(text, [
        ("<", "lt", False),
        (">", "gt", False),
        ("<=", "le", False),
        (">=", "ge", False),
        ("==", "eq", False),
        ("!=", "ne", False)
    ], parse_term)

# conj: expr
# conj: expr "and" conj
def parse_conj(text):
    return parse_binop(text, [("and", "conj", True)], parse_expr, parse_conj)

# prop:
#   expr "|->" conj ";"
#   expr ";"
def parse_prop(text):
    s, t = parse_binop(text, [("|->", "impl", False)], parse_expr, parse_conj)
    _, t = parse_str(t, ";")
    return s, t

if __name__ == '__main__':
    import fileinput, pprint
    pp = pprint.PrettyPrinter(indent=4)

    if False:
        with fileinput.input() as f:
            sva_text = "".join(f).rstrip()
    else:
        sva_text = """
1 & S[1] |-> S[3:2] and 8'h a_B | S[2+:2] ^ 3 'b 101 == S;

a
  |-> b
  and (c & d) == e;

x |-> c > d;
        """.strip()

    print("--- Input ---")
    print(sva_text)
    print("-------------")

    props = []
    while len(sva_text):
        s, sva_text = parse_prop(sva_text)
        props.append(s)

    print()
    print("--- S-Expr ---")
    for s in props:
        pp.pprint(s)
        print("--------------")
    print()
