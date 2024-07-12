from itertools import chain
import random

widths = [
    (16, 32, 48, True),
    (16, 32, 48, False),
    (32, 16, 48, True),
    (32, 16, 48, False),
    (32, 32, 16, True),
    (32, 32, 16, False)
]

shift_widths = [
    (32, 6, 32, True, False),
    (32, 6, 32, False, False),
    (32, 6, 64, True, False),
    (32, 6, 64, False, False),
    (32, 32, 16, True, False),
    (32, 32, 16, False, False),
    (32, 6, 32, True, True),
    (32, 6, 32, False, True),
    (32, 6, 64, True, True),
    (32, 6, 64, False, True),
    (32, 32, 16, True, True),
    (32, 32, 16, False, True),
]

def write_rtlil_cell(f, cell_type, inputs, outputs, parameters):
    f.write('autoidx 1\n')
    f.write('module \\gold\n')
    idx = 1
    for name, width in inputs.items():
        f.write(f'\twire width {width} input {idx} \\{name}\n')
        idx += 1
    for name, width in outputs.items():
        f.write(f'\twire width {width} output {idx} \\{name}\n')
        idx += 1
    f.write(f'\tcell ${cell_type} \\UUT\n')
    for (name, value) in parameters.items():
        f.write(f'\t\tparameter \\{name} {value}\n')
    for name in chain(inputs.keys(), outputs.keys()):
        f.write(f'\t\tconnect \\{name} \\{name}\n')
    f.write(f'\tend\nend\n')

class BaseCell:
    def __init__(self, name):
        self.name = name

class UnaryCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for (a_width, _, y_width, signed) in widths:
            yield (f'{a_width}-{y_width}-{'S' if signed else 'U'}',
                   {'A_WIDTH' : a_width,
                    'A_SIGNED' : int(signed),
                    'Y_WIDTH' : y_width})
    def write_rtlil_file(self, f, parameters):
        write_rtlil_cell(f, self.name, {'A': parameters['A_WIDTH']}, {'Y': parameters['Y_WIDTH']}, parameters)

class BinaryCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for (a_width, b_width, y_width, signed) in widths:
            yield (f'{a_width}-{b_width}-{y_width}-{'S' if signed else 'U'}',
                   {'A_WIDTH' : a_width,
                    'A_SIGNED' : int(signed),
                    'B_WIDTH' : b_width,
                    'B_SIGNED' : int(signed),
                    'Y_WIDTH' : y_width})
    def write_rtlil_file(self, f, parameters):
        write_rtlil_cell(f, self.name, {'A': parameters['A_WIDTH'], 'B': parameters['B_WIDTH']}, {'Y': parameters['Y_WIDTH']}, parameters)

class ShiftCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for (a_width, b_width, y_width, a_signed, b_signed) in shift_widths:
            if not self.name in ('shift', 'shiftx') and b_signed: continue
            if self.name == 'shiftx' and a_signed: continue
            yield (f'{a_width}-{b_width}-{y_width}-{'S' if a_signed else 'U'}{'S' if b_signed else 'U'}',
                   {'A_WIDTH' : a_width,
                    'A_SIGNED' : int(a_signed),
                    'B_WIDTH' : b_width,
                    'B_SIGNED' : int(b_signed),
                    'Y_WIDTH' : y_width})
    def write_rtlil_file(self, f, parameters):
        write_rtlil_cell(f, self.name, {'A': parameters['A_WIDTH'], 'B': parameters['B_WIDTH']}, {'Y': parameters['Y_WIDTH']}, parameters)

class MuxCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for width in [10, 20, 40]:
            yield (f'{width}', {'WIDTH' : width})
    def write_rtlil_file(self, f, parameters):
        write_rtlil_cell(f, self.name, {'A': parameters['WIDTH'], 'B': parameters['WIDTH'], 'S': 1}, {'Y': parameters['WIDTH']}, parameters)

class BWCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for width in [10, 20, 40]:
            yield (f'{width}', {'WIDTH' : width})
    def write_rtlil_file(self, f, parameters):
        inputs = {'A': parameters['WIDTH'], 'B': parameters['WIDTH']}
        if self.name == "bwmux": inputs['S'] = parameters['WIDTH']
        write_rtlil_cell(f, self.name, inputs, {'Y': parameters['WIDTH']}, parameters)

class PMuxCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for (width, s_width) in [(10, 1), (10, 4), (20, 4)]:
            yield (f'{width}-{s_width}',
                   {'WIDTH' : width,
                    'S_WIDTH' : s_width})
    def write_rtlil_file(self, f, parameters):
        s_width = parameters['S_WIDTH']
        b_width = parameters['WIDTH'] * s_width
        write_rtlil_cell(f, self.name, {'A': parameters['WIDTH'], 'B': b_width, 'S': s_width}, {'Y': parameters['WIDTH']}, parameters)

class BMuxCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for (width, s_width) in [(10, 1), (10, 2), (10, 4)]:
            yield (f'{width}-{s_width}', {'WIDTH' : width, 'S_WIDTH' : s_width})
    def write_rtlil_file(self, f, parameters):
        write_rtlil_cell(f, self.name, {'A': parameters['WIDTH'] << parameters['S_WIDTH'], 'S': parameters['S_WIDTH']}, {'Y': parameters['WIDTH']}, parameters)

class DemuxCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for (width, s_width) in [(10, 1), (32, 2), (16, 4)]:
            yield (f'{width}-{s_width}', {'WIDTH' : width, 'S_WIDTH' : s_width})
    def write_rtlil_file(self, f, parameters):
        write_rtlil_cell(f, self.name, {'A': parameters['WIDTH'], 'S': parameters['S_WIDTH']}, {'Y': parameters['WIDTH'] << parameters['S_WIDTH']}, parameters)

def seeded_randint(seed, a, b):
    r = random.getstate()
    random.seed(seed)
    n = random.randint(a, b)
    random.setstate(r)
    return n

class LUTCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for width in [4, 6, 8]:
            lut = seeded_randint(width, 0, 2**width - 1)
            yield (f'{width}', {'WIDTH' : width, 'LUT' : lut})
    def write_rtlil_file(self, f, parameters):
        write_rtlil_cell(f, self.name, {'A': parameters['WIDTH']}, {'Y': 1}, parameters)

class ConcatCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for (a_width, b_width) in [(16, 16), (8, 14), (20, 10)]:
            yield (f'{a_width}-{b_width}', {'A_WIDTH' : a_width, 'B_WIDTH' : b_width})
    def write_rtlil_file(self, f, parameters):
        write_rtlil_cell(f, self.name, {'A': parameters['A_WIDTH'], 'B' : parameters['B_WIDTH']}, {'Y': parameters['A_WIDTH'] + parameters['B_WIDTH']}, parameters)

class SliceCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        for (a_width, offset, y_width) in [(32, 10, 15), (8, 0, 4), (10, 0, 10)]:
            yield (f'{a_width}-{offset}-{y_width}', {'A_WIDTH' : a_width, 'OFFSET' : offset, 'Y_WIDTH': y_width})
    def write_rtlil_file(self, f, parameters):
        write_rtlil_cell(f, self.name, {'A': parameters['A_WIDTH']}, {'Y': parameters['Y_WIDTH']}, parameters)

class FailCell(BaseCell):
    def __init__(self, name):
        super().__init__(name)
    def generate_tests(self):
        yield ('', {})
    def write_rtlil_file(self, f, parameters):
        raise Exception(f'\'{self.name}\' cell unimplemented in test generator')

rtlil_cells = [
    UnaryCell("not"),
    UnaryCell("pos"),
    UnaryCell("neg"),
    BinaryCell("and"),
    BinaryCell("or"),
    BinaryCell("xor"),
    BinaryCell("xnor"),
    UnaryCell("reduce_and"),
    UnaryCell("reduce_or"),
    UnaryCell("reduce_xor"),
    UnaryCell("reduce_xnor"),
    UnaryCell("reduce_bool"),
    ShiftCell("shl"),
    ShiftCell("shr"),
    ShiftCell("sshl"),
    ShiftCell("sshr"),
    ShiftCell("shift"),
    ShiftCell("shiftx"),
#    ("fa", ["A", "B", "C", "X", "Y"]),
#    ("lcu", ["P", "G", "CI", "CO"]),
#    ("alu", ["A", "B", "CI", "BI", "X", "Y", "CO"]),
    BinaryCell("lt"),
    BinaryCell("le"),
    BinaryCell("eq"),
    BinaryCell("ne"),
    BinaryCell("eqx"),
    BinaryCell("nex"),
    BinaryCell("ge"),
    BinaryCell("gt"),
    BinaryCell("add"),
    BinaryCell("sub"),
    BinaryCell("mul"),
#    BinaryCell("macc"),
    BinaryCell("div"),
    BinaryCell("mod"),
    BinaryCell("divfloor"),
    BinaryCell("modfloor"),
    BinaryCell("pow"),
    UnaryCell("logic_not"),
    BinaryCell("logic_and"),
    BinaryCell("logic_or"),
    SliceCell("slice"),
    ConcatCell("concat"),
    MuxCell("mux"),
    BMuxCell("bmux"),
    PMuxCell("pmux"),
    DemuxCell("demux"),
    LUTCell("lut"),
#    ("sop", ["A", "Y"]),
#    ("tribuf", ["A", "EN", "Y"]),
#    ("specify2", ["EN", "SRC", "DST"]),
#    ("specify3", ["EN", "SRC", "DST", "DAT"]),
#    ("specrule", ["EN_SRC", "EN_DST", "SRC", "DST"]),
    BWCell("bweqx"),
    BWCell("bwmux"),
#    ("assert", ["A", "EN"]),
#    ("assume", ["A", "EN"]),
#    ("live", ["A", "EN"]),
#    ("fair", ["A", "EN"]),
#    ("cover", ["A", "EN"]),
#    ("initstate", ["Y"]),
#    ("anyconst", ["Y"]),
#    ("anyseq", ["Y"]),
#    ("anyinit", ["D", "Q"]),
#    ("allconst", ["Y"]),
#    ("allseq", ["Y"]),
#    ("equiv", ["A", "B", "Y"]),
#    ("print", ["EN", "TRG", "ARGS"]),
#    ("check", ["A", "EN", "TRG", "ARGS"]),
#    ("set_tag", ["A", "SET", "CLR", "Y"]),
#    ("get_tag", ["A", "Y"]),
#    ("overwrite_tag", ["A", "SET", "CLR"]),
#    ("original_tag", ["A", "Y"]),
#    ("future_ff", ["A", "Y"]),
#    ("scopeinfo", []),
]

def generate_test_cases(per_cell):
    tests = []
    names = []
    for cell in rtlil_cells:
        seen_names = set()
        for (name, parameters) in cell.generate_tests():
            if not name in seen_names:
                seen_names.add(name)
                tests.append((cell, parameters))
                names.append(f'{cell.name}-{name}' if name != '' else cell.name)
                if per_cell is not None and len(seen_names) >= per_cell:
                    break
    return (names, tests)