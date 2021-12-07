#!/usr/bin/env python3

class FNode:
    def __init__(self, fun, *args):
        self.fun = fun
        self.args = args

        if len(self.args) == 0:
            assert fun not in ("BUF", "NOT", "AND", "OR", "XOR", "MUX")

        if len(self.args) == 1:
            assert fun in ("BUF", "NOT")

        if len(self.args) == 2:
            assert fun in ("AND", "OR", "XOR")

        if len(self.args) == 3:
            assert fun in ("MUX")

    def __str__(self):
        if len(self.args) == 0:
            return self.fun
        if self.fun == "NOT" and len(self.args[0].args) == 0:
            return "!" + self.args[0].fun
        return self.fun + "(" + ",".join([str(a) for a in self.args]) + ")"

    def as_genlib_term(self):
        if len(self.args) == 0:
            return self.fun
        if self.fun == "NOT":
            assert len(self.args[0].args) == 0
            return "!" + self.args[0].fun
        if self.fun == "AND":
            return "(" + self.args[0].as_genlib_term() + "*" + self.args[1].as_genlib_term() + ")"
        if self.fun == "OR":
            return "(" + self.args[0].as_genlib_term() + "+" + self.args[1].as_genlib_term() + ")"
        assert False

    def mapMux(self):
        if self.fun == "MUX":
            A, B, C = self.args
            return OR(AND(A, NOT(C)), AND(B, C)).mapMux()
        return FNode(self.fun, *[a.mapMux() for a in self.args])

    def mapXor(self):
        if self.fun == "XOR":
            A, B = self.args
            return OR(AND(A, NOT(B)), AND(NOT(A), B)).mapXor()
        return FNode(self.fun, *[a.mapXor() for a in self.args])

    def mapNot(self):
        if self.fun == "BUF":
            return self.arg1.mapNot()
        if self.fun == "NOT":
            if self.args[0].fun == "AND":
                return OR(NOT(self.args[0].args[0]),NOT(self.args[0].args[1])).mapNot()
            if self.args[0].fun == "OR":
                return AND(NOT(self.args[0].args[0]),NOT(self.args[0].args[1])).mapNot()
            if self.args[0].fun == "NOT":
                return self.args[0].args[0].mapNot()
        return FNode(self.fun, *[a.mapNot() for a in self.args])

    def map(self):
        n = self
        n = n.mapMux()
        n = n.mapXor()
        n = n.mapNot()
        return n

    def isInv(self):
        if len(self.args) == 0:
            return False
        if self.fun == "XOR":
            return False
        if self.fun == "NOT":
            return self.args[0].isNonInv()
        for a in self.args:
            if not a.isInv():
                return False
        return True

    def isNonInv(self):
        if len(self.args) == 0:
            return True
        if self.fun == "XOR":
            return False
        if self.fun == "NOT":
            return self.args[0].isInv()
        for a in self.args:
            if not a.isNonInv():
                return False
        return True

A = FNode("A")
B = FNode("B")
C = FNode("C")
D = FNode("D")
E = FNode("E")

def BUF(arg): return FNode("BUF", arg)
def NOT(arg): return FNode("NOT", arg)
def AND(arg1, arg2): return FNode("AND", arg1, arg2)
def  OR(arg1, arg2): return FNode( "OR", arg1, arg2)
def XOR(arg1, arg2): return FNode("XOR", arg1, arg2)
def MUX(arg1, arg2, arg3): return FNode("MUX", arg1, arg2, arg3)

# Genlib Format:
#
# GATE <cell-name> <cell-area> <cell-logic-function>
#
# PIN <pin-name> <phase> <input-load> <max-load>
#     <rise-block-delay> <rise-fanout-delay>
#     <fall-block-delay> <fall-fanout-delay>
#
# phase:
#     INV, NONINV, or UNKNOWN
#
# cell-logic-function:
#     <output> = <term with *(AND), +(OR), !(NOT)>


cells = [
    ["$__CC_BUF", 5, A],
    ["$__CC_NOT", 0, NOT(A)],
    ["$__CC_MUX", 5, MUX(A, B, C)],
]

base_cells = [
    ["$__CC2_A", AND(A, B)],
    ["$__CC2_O",  OR(A, B)],
    ["$__CC2_X", XOR(A, B)],

    ["$__CC3_AA", AND(AND(A, B), C)],
    ["$__CC3_OO",  OR( OR(A, B), C)],
    ["$__CC3_XX", XOR(XOR(A, B), C)],
    ["$__CC3_AO",  OR(AND(A, B), C)],
    ["$__CC3_OA", AND( OR(A, B), C)],
    ["$__CC3_AX", XOR(AND(A, B), C)],
    ["$__CC3_XA", AND(XOR(A, B), C)],

#   ["$__CC3_AAA", AND(AND(A,B),AND(A,C))],
#   ["$__CC3_AXA", XOR(AND(A,B),AND(A,C))],
#   ["$__CC3_XAX", AND(XOR(A,B),XOR(A,C))],
#   ["$__CC3_AAX", AND(AND(A,B),XOR(A,C))],
#   ["$__CC3_AXX", XOR(AND(A,B),XOR(A,C))],
#   ["$__CC3_XXX", XOR(XOR(A,B),XOR(A,C))],
#   ["$__CC3_AAO", AND(AND(A,B), OR(A,C))],
#   ["$__CC3_AOA",  OR(AND(A,B),AND(A,C))],
#   ["$__CC3_AOX",  OR(AND(A,B),XOR(A,C))],

#   ["$__CC3_AAA_N", AND(AND(A,B),AND(NOT(A),C))],
#   ["$__CC3_AXA_N", XOR(AND(A,B),AND(NOT(A),C))],
#   ["$__CC3_XAX_N", AND(XOR(A,B),XOR(NOT(A),C))],
#   ["$__CC3_AAX_N", AND(AND(A,B),XOR(NOT(A),C))],
#   ["$__CC3_AXX_N", XOR(AND(A,B),XOR(NOT(A),C))],
#   ["$__CC3_XXX_N", XOR(XOR(A,B),XOR(NOT(A),C))],
#   ["$__CC3_AAO_N", AND(AND(A,B), OR(NOT(A),C))],
#   ["$__CC3_AOA_N",  OR(AND(A,B),AND(NOT(A),C))],
#   ["$__CC3_AOX_N",  OR(AND(A,B),XOR(NOT(A),C))],

    ["$__CC4_AAA", AND(AND(A,B),AND(C,D))],
    ["$__CC4_AXA", XOR(AND(A,B),AND(C,D))],
    ["$__CC4_XAX", AND(XOR(A,B),XOR(C,D))],
    ["$__CC4_AAX", AND(AND(A,B),XOR(C,D))],
    ["$__CC4_AXX", XOR(AND(A,B),XOR(C,D))],
    ["$__CC4_XXX", XOR(XOR(A,B),XOR(C,D))],
    ["$__CC4_AAO", AND(AND(A,B), OR(C,D))],
    ["$__CC4_AOA",  OR(AND(A,B),AND(C,D))],
    ["$__CC4_AOX",  OR(AND(A,B),XOR(C,D))],
]

for name, expr in base_cells:
    cells.append([name, 10, expr])

    name = (name
        .replace("$__CC4_", "$__CC5_")
        .replace("$__CC3_", "$__CC4_")
        .replace("$__CC2_", "$__CC3_"))

    # Cells such as $__CC4_AA_A are redundant, as $__CC4_AAA is equivalent
    if name not in ("$__CC4_AA", "$__CC3_A"):
        cells.append([name + "_A", 12, AND(E, expr)])
    if name not in ("$__CC4_OO", "$__CC3_O"):
        cells.append([name + "_O", 12,  OR(E, expr)])
    if name not in ("$__CC4_XX", "$__CC3_X"):
        cells.append([name + "_X", 12, XOR(E, expr)])

with open("techlibs/gatemate/lut_tree_cells.genlib", "w") as glf:
    def mkGate(name, cost, expr, max_load=9999, block_delay = 10, fanout_delay = 5):
        name = name.replace(" ", "")
        expr = expr.map()

        phase = "UNKNOWN"
        if expr.isInv(): phase = "INV"
        if expr.isNonInv(): phase = "NONINV"

        print("", file=glf)
        print("GATE %s %d Y=%s;" % (name, cost, expr.as_genlib_term()), file=glf)
        print("PIN * %s 1 %d %d %d %d %d" % (phase, max_load, block_delay, fanout_delay, block_delay, fanout_delay), file=glf)
    print("GATE $__ZERO 0 Y=CONST0;", file=glf)
    print("GATE $__ONE 0 Y=CONST1;", file=glf)
    for name, cost, expr in cells:
        mkGate(name, cost, expr)

class LUTTreeNode:
    def __init__(self, name, width, inputs=None):
        self.name = name
        self.width = width
        self.inputs = inputs
    def is_input(self):
        return self.width == 0
    def map(self, expr, params, ports):
        if self.is_input():
            # Input to LUT tree
            if expr is None:
                ports[self.name] = "" # disconnected input
            else:
                assert(len(expr.args) == 0)
                ports[self.name] = expr.fun
            return
        if expr is None:
            # Unused part of tree
            params[self.name] = "4'b0000"
            for i in self.inputs:
                i.map(None, params, ports)
            return
        elif len(expr.args) == 0:
            # Input to the expression; but not LUT tree
            # Insert a route through
            params[self.name] = "4'b1010"
            self.inputs[0].map(expr, params, ports)
            for i in self.inputs[1:]:
                i.map(None, params, ports)
            return
        # Map uphill LUTs; uninverting arguments and keeping track of that if needed
        arg_inv = []
        for (i, arg) in zip(self.inputs, expr.args):
            if arg.fun == "NOT":
                i.map(arg.args[0], params, ports)
                arg_inv.append(True)
            else:
                i.map(arg, params, ports)
                arg_inv.append(False)
        # Determine base init value
        assert self.width == 2
        if expr.fun == "AND":
            init = 0b1000
        elif expr.fun == "OR":
            init = 0b1110
        elif expr.fun == "XOR":
            init = 0b0110
        else:
            assert False, expr.fun
        # Swap bits if init inverted
        swapped_init = 0b0000
        for b in range(4):
            if ((init >> b) & 0x1) == 0: continue
            for i in range(2):
                if arg_inv[i]:
                    b ^= (1 << i)
            swapped_init |= (1 << b)
        # Set init param
        params[self.name] = "4'b{:04b}".format(swapped_init)

def LUT2(name, i0, i1): return LUTTreeNode(name, 2, [i0, i1])
def I(name): return LUTTreeNode(name, 0)

lut_prims = {
    "CC_LUT2": LUT2("INIT", I("I0"), I("I1")),
    "CC_L2T4": LUT2(
        "INIT_L10",
        LUT2("INIT_L00", I("I0"), I("I1")),
        LUT2("INIT_L01", I("I2"), I("I3")),
    ),
    "CC_L2T5": LUT2(
        "INIT_L20", I("I4"), LUT2("INIT_L11",
            LUT2("INIT_L02", I("I0"), I("I1")),
            LUT2("INIT_L03", I("I2"), I("I3")),
        )
    )
}

with open("techlibs/gatemate/lut_tree_map.v", "w") as vf:
    # Non-automatic rules
    print("""
module \\$__ZERO (output Y); assign Y = 1'b0; endmodule
module \\$__ONE (output Y); assign Y = 1'b1; endmodule

module \\$__CC_BUF (input A, output Y); assign Y = A; endmodule

module \\$__CC_MUX (input A, B, C, output Y);
    CC_MX2 _TECHMAP_REPLACE_ (
        .D0(A), .D1(B), .S0(C),
        .Y(Y)
    );
endmodule
""", file=vf)
    for name, cost, expr in cells:
        expr = expr.mapMux().mapNot() # Don't map XOR
        if name in ("$__CC_BUF", "$__CC_NOT", "$__CC_MUX"):
            # Special cases
            continue
        if name.startswith("$__CC2_"):
            prim = "CC_LUT2"
        elif name.startswith("$__CC5_") or (name.startswith("$__CC4_") and cost == 12):
            prim = "CC_L2T5"
        else:
            prim = "CC_L2T4"
        ports = {}
        params = {}
        lut_prims[prim].map(expr, params, ports)
        print("", file=vf)
        print("module \\%s (input %s, output Y);" % (name,
            ", ".join(sorted(set(x for x in ports.values() if x)))), file=vf)
        print("    %s #(" % prim, file=vf)
        for k, v in sorted(params.items(), key=lambda x: x[0]):
            print("        .%s(%s)," % (k, v), file=vf)
        print("    ) _TECHMAP_REPLACE_ (", file=vf)
        print("         %s," % ", ".join(".%s(%s)" % (k, v) for k, v in sorted(ports.items(), key=lambda x:x[0])),
            file=vf)
        print("         .O(Y)", file=vf)
        print("    );", file=vf)
        print("endmodule", file=vf)
