from itertools import chain
import random

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
        if value >= 2**32:
            f.write(f'\t\tparameter \\{name} {value.bit_length()}\'{value:b}\n')
        else:
            f.write(f'\t\tparameter \\{name} {value}\n')
    for name in chain(inputs.keys(), outputs.keys()):
        f.write(f'\t\tconnect \\{name} \\{name}\n')
    f.write(f'\tend\nend\n')

class BaseCell:
    def __init__(self, name, parameters, inputs, outputs, test_values):
        self.name = name
        self.parameters = parameters
        self.inputs = inputs
        self.outputs = outputs
        self.test_values = test_values
    def get_port_width(self, port, parameters):
        def parse_specifier(spec):
            if isinstance(spec, int):
                return spec
            if isinstance(spec, str):
                return parameters[spec]
            if callable(spec):
                return spec(parameters)
            assert False, "expected int, str or lambda"
        if port in self.inputs:
            return parse_specifier(self.inputs[port])
        elif port in self.outputs:
            return parse_specifier(self.outputs[port])
        else:
            assert False, "expected input or output"
    def generate_tests(self, rnd):
        def print_parameter(v):
            if isinstance(v, bool):
                return "S" if v else "U"
            else:
                return str(v)
        for values in self.test_values:
            if isinstance(values, int):
                values = [values]
            name = '-'.join([print_parameter(v) for v in values])
            parameters = {parameter: int(values[i]) for i, parameter in enumerate(self.parameters)}
            if self.is_test_valid(values):
                yield (name, parameters)
    def write_rtlil_file(self, path, parameters):
        inputs = {port: self.get_port_width(port, parameters) for port in self.inputs}
        outputs = {port: self.get_port_width(port, parameters) for port in self.outputs}
        with open(path, 'w') as f:
            write_rtlil_cell(f, self.name, inputs, outputs, parameters)
    def is_test_valid(self, values):
        return True

class UnaryCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['A_WIDTH', 'Y_WIDTH', 'A_SIGNED'], {'A': 'A_WIDTH'}, {'Y': 'Y_WIDTH'}, values)

class BinaryCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['A_WIDTH', 'B_WIDTH', 'Y_WIDTH', 'A_SIGNED', 'B_SIGNED'], {'A': 'A_WIDTH', 'B': 'B_WIDTH'}, {'Y': 'Y_WIDTH'}, values)

class ShiftCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name,  ['A_WIDTH', 'B_WIDTH', 'Y_WIDTH', 'A_SIGNED', 'B_SIGNED'], {'A': 'A_WIDTH', 'B': 'B_WIDTH'}, {'Y': 'Y_WIDTH'}, values)
    def is_test_valid(self, values):
        (a_width, b_width, y_width, a_signed, b_signed) = values
        if not self.name in ('shift', 'shiftx') and b_signed: return False
        if self.name == 'shiftx' and a_signed: return False
        return True

class MuxCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['WIDTH'], {'A': 'WIDTH', 'B': 'WIDTH', 'S': 1}, {'Y': 'WIDTH'}, values)

class BWCell(BaseCell):
    def __init__(self, name, values):
        inputs = {'A': 'WIDTH', 'B': 'WIDTH'}
        if name == "bwmux": inputs['S'] = 'WIDTH'
        super().__init__(name, ['WIDTH'], inputs, {'Y': 'WIDTH'}, values)

class PMuxCell(BaseCell):
    def __init__(self, name, values):
        b_width = lambda par: par['WIDTH'] * par['S_WIDTH']
        super().__init__(name, ['WIDTH', 'S_WIDTH'], {'A': 'WIDTH', 'B': b_width, 'S': 'S_WIDTH'}, {'Y': 'WIDTH'}, values)

class BMuxCell(BaseCell):
    def __init__(self, name, values):
        a_width = lambda par: par['WIDTH'] << par['S_WIDTH']
        super().__init__(name, ['WIDTH', 'S_WIDTH'], {'A': a_width, 'S': 'S_WIDTH'}, {'Y': 'WIDTH'}, values)

class DemuxCell(BaseCell):
    def __init__(self, name, values):
        y_width = lambda par: par['WIDTH'] << par['S_WIDTH']
        super().__init__(name, ['WIDTH', 'S_WIDTH'], {'A': 'WIDTH', 'S': 'S_WIDTH'}, {'Y': y_width}, values)

class LUTCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['WIDTH', 'LUT'], {'A': 'WIDTH'}, {'Y': 1}, values)
    def generate_tests(self, rnd):
        for width in self.test_values:
            lut = rnd(f'lut-{width}').getrandbits(2**width)
            yield (f'{width}', {'WIDTH' : width, 'LUT' : lut})

class ConcatCell(BaseCell):
    def __init__(self, name, values):
        y_width = lambda par: par['A_WIDTH'] + par['B_WIDTH']
        super().__init__(name, ['A_WIDTH', 'B_WIDTH'], {'A': 'A_WIDTH', 'B': 'B_WIDTH'}, {'Y': y_width}, values)

class SliceCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['A_WIDTH', 'OFFSET', 'Y_WIDTH'], {'A': 'A_WIDTH'}, {'Y': 'Y_WIDTH'}, values)

class FACell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['WIDTH'], {'A': 'WIDTH', 'B': 'WIDTH', 'C': 'WIDTH'}, {'X': 'WIDTH', 'Y': 'WIDTH'}, values)
        self.sim_preprocessing = "techmap" # because FA is not implemented in yosys sim

class LCUCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['WIDTH'], {'P': 'WIDTH', 'G': 'WIDTH', 'CI': 1}, {'CO': 'WIDTH'}, values)
        self.sim_preprocessing = "techmap" # because LCU is not implemented in yosys sim

class ALUCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['A_WIDTH', 'B_WIDTH', 'Y_WIDTH', 'A_SIGNED', 'B_SIGNED'], {'A': 'A_WIDTH', 'B': 'B_WIDTH', 'CI': 1, 'BI': 1}, {'X': 'Y_WIDTH', 'Y': 'Y_WIDTH', 'CO': 'Y_WIDTH'}, values)
        self.sim_preprocessing = "techmap" # because ALU is not implemented in yosys sim

class FailCell(BaseCell):
    def __init__(self, name):
        super().__init__(name, [], {}, {})
    def generate_tests(self, rnd):
        yield ('', {})
    def write_rtlil_file(self, path, parameters):
        raise Exception(f'\'{self.name}\' cell unimplemented in test generator')

class FFCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['WIDTH'], ['D'], ['Q'], values)
    def write_rtlil_file(self, path, parameters):
        from test_functional import yosys_synth
        verilog_file = path.parent / 'verilog.v'
        with open(verilog_file, 'w') as f:
            width = parameters['WIDTH']
            f.write(f"""
module gold(
    input wire clk,
    input wire [{width-1}:0] D,
    output reg [{width-1}:0] Q
);
    initial Q = {width}'b{("101" * width)[:width]};
    always @(posedge clk)
        Q <= D;
endmodule""")
        yosys_synth(verilog_file, path)

class MemCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['DATA_WIDTH', 'ADDR_WIDTH'], {'WA': 'ADDR_WIDTH', 'RA': 'ADDR_WIDTH', 'WD': 'DATA_WIDTH'}, {'RD': 'DATA_WIDTH'}, values)
    def write_rtlil_file(self, path, parameters):
        from test_functional import yosys_synth
        verilog_file = path.parent / 'verilog.v'
        with open(verilog_file, 'w') as f:
            f.write("""
module gold(
    input wire clk,
    input wire [{1}:0] WA,
    input wire [{0}:0] WD,
    input wire [{1}:0] RA,
    output reg [{0}:0] RD
);
    reg [{0}:0] mem[0:{2}];
    integer i;
    initial
        for(i = 0; i <= {2}; i = i + 1)
            mem[i] = 9192 * (i + 1);
    always @(*)
        RD = mem[RA];
    always @(posedge clk)
        mem[WA] <= WD;
endmodule""".format(parameters['DATA_WIDTH'] - 1, parameters['ADDR_WIDTH'] - 1, 2**parameters['ADDR_WIDTH'] - 1))
        yosys_synth(verilog_file, path)

class MemDualCell(BaseCell):
    def __init__(self, name, values):
        super().__init__(name, ['DATA_WIDTH', 'ADDR_WIDTH'],
                         {'WA1': 'ADDR_WIDTH', 'WA2': 'ADDR_WIDTH',
                          'RA1': 'ADDR_WIDTH', 'RA2': 'ADDR_WIDTH',
                          'WD1': 'DATA_WIDTH', 'WD2': 'DATA_WIDTH'},
                         {'RD1': 'DATA_WIDTH', 'RD2': 'DATA_WIDTH'}, values)
        self.sim_preprocessing = "memory_map" # issue #4496 in yosys -sim prevents this example from working without memory_map
    def write_rtlil_file(self, path, parameters):
        from test_functional import yosys_synth
        verilog_file = path.parent / 'verilog.v'
        with open(verilog_file, 'w') as f:
            f.write("""
module gold(
    input wire clk,
    input wire [{1}:0] WA1,
    input wire [{0}:0] WD1,
    input wire [{1}:0] WA2,
    input wire [{0}:0] WD2,
    input wire [{1}:0] RA1,
    input wire [{1}:0] RA2,
    output reg [{0}:0] RD1,
    output reg [{0}:0] RD2
);
    reg [{0}:0] mem[0:{2}];
    integer i;
    initial
        for(i = 0; i <= {2}; i = i + 1)
            mem[i] = 9192 * (i + 1);
    always @(*)
        RD1 = mem[RA1];
    always @(*)
        RD2 = mem[RA2];
    always @(posedge clk) begin
        mem[WA1] <= WD1;
        mem[WA2] <= WD2;
    end
endmodule""".format(parameters['DATA_WIDTH'] - 1, parameters['ADDR_WIDTH'] - 1, 2**parameters['ADDR_WIDTH'] - 1))
        yosys_synth(verilog_file, path)

class PicorvCell(BaseCell):
    def __init__(self):
        super().__init__("picorv", [], {}, {}, [()])
        self.smt_max_steps = 50 # z3 is too slow for more steps
    def write_rtlil_file(self, path, parameters):
        from test_functional import yosys, base_path, quote
        tb_file = base_path / 'tests/functional/picorv32_tb.v'
        cpu_file = base_path / 'tests/functional/picorv32.v'
        yosys(f"read_verilog {quote(tb_file)} {quote(cpu_file)}; prep -top gold; flatten; write_rtlil {quote(path)}")

binary_widths = [
    # try to cover extending A operand, extending B operand, extending/truncating result
    (16, 32, 48, True, True),
    (16, 32, 48, False, False),
    (32, 16, 48, True, True),
    (32, 16, 48, False, False),
    (32, 32, 16, True, True),
    (32, 32, 16, False, False),
    # have at least one test that checks small inputs, which will exercise the cornercases more
    (4, 4, 8, True, True),
    (4, 4, 8, False, False)
]

unary_widths = [
    (6, 12, True),
    (6, 12, False),
    (32, 16, True),
    (32, 16, False)
]

# note that meaningless combinations of signednesses are eliminated,
# like e.g. most shift operations don't take signed shift amounts
shift_widths = [
    # one set of tests that definitely checks all possible shift amounts
    # with a bigger result width to make sure it's not truncated
    (32, 6, 64, True, False),
    (32, 6, 64, False, False),
    (32, 6, 64, True, True),
    (32, 6, 64, False, True),
    # one set that checks very oversized shifts
    (32, 32, 64, True, False),
    (32, 32, 64, False, False),
    (32, 32, 64, True, True),
    (32, 32, 64, False, True),
    # at least one test where the result is going to be truncated
    (32, 6, 16, False, False),
    # since 1-bit shifts are special cased
    (1, 4, 1, False, False),
    (1, 4, 1, True, False),
]

rtlil_cells = [
    UnaryCell("not", unary_widths),
    UnaryCell("pos", unary_widths),
    UnaryCell("neg", unary_widths),
    BinaryCell("and", binary_widths),
    BinaryCell("or", binary_widths),
    BinaryCell("xor", binary_widths),
    BinaryCell("xnor", binary_widths),
    UnaryCell("reduce_and", unary_widths),
    UnaryCell("reduce_or", unary_widths),
    UnaryCell("reduce_xor", unary_widths),
    UnaryCell("reduce_xnor", unary_widths),
    UnaryCell("reduce_bool", unary_widths),
    ShiftCell("shl", shift_widths),
    ShiftCell("shr", shift_widths),
    ShiftCell("sshl", shift_widths),
    ShiftCell("sshr", shift_widths),
    ShiftCell("shift", shift_widths),
    ShiftCell("shiftx", shift_widths),
    FACell("fa", [8, 20]),
    LCUCell("lcu", [1, 10]),
    ALUCell("alu", binary_widths),
    BinaryCell("lt", binary_widths),
    BinaryCell("le", binary_widths),
    BinaryCell("eq", binary_widths),
    BinaryCell("ne", binary_widths),
    BinaryCell("eqx", binary_widths),
    BinaryCell("nex", binary_widths),
    BinaryCell("ge", binary_widths),
    BinaryCell("gt", binary_widths),
    BinaryCell("add", binary_widths),
    BinaryCell("sub", binary_widths),
    BinaryCell("mul", binary_widths),
#    BinaryCell("macc"),
    BinaryCell("div", binary_widths),
    BinaryCell("mod", binary_widths),
    BinaryCell("divfloor", binary_widths),
    BinaryCell("modfloor", binary_widths),
    BinaryCell("pow", binary_widths),
    UnaryCell("logic_not", unary_widths),
    BinaryCell("logic_and", binary_widths),
    BinaryCell("logic_or", binary_widths),
    SliceCell("slice", [(32, 10, 15), (8, 0, 4), (10, 0, 10)]),
    ConcatCell("concat", [(16, 16), (8, 14), (20, 10)]),
    MuxCell("mux", [10, 16, 40]),
    BMuxCell("bmux", [(10, 1), (10, 2), (10, 4)]),
    PMuxCell("pmux", [(10, 1), (10, 4), (20, 4)]),
    DemuxCell("demux", [(10, 1), (32, 2), (16, 4)]),
    LUTCell("lut", [4, 6, 8]),
#    ("sop", ["A", "Y"]),
#    ("tribuf", ["A", "EN", "Y"]),
#    ("specify2", ["EN", "SRC", "DST"]),
#    ("specify3", ["EN", "SRC", "DST", "DAT"]),
#    ("specrule", ["EN_SRC", "EN_DST", "SRC", "DST"]),
    BWCell("bweqx", [10, 16, 40]),
    BWCell("bwmux", [10, 16, 40]),
    FFCell("ff", [10, 20, 40]),
    MemCell("mem", [(16, 4)]),
    MemDualCell("mem-dual", [(16, 4)]),
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
    PicorvCell()
]

def generate_test_cases(per_cell, rnd):
    tests = []
    names = []
    for cell in rtlil_cells:
        seen_names = set()
        for (name, parameters) in cell.generate_tests(rnd):
            if not name in seen_names:
                seen_names.add(name)
                tests.append((cell, parameters))
                names.append(f'{cell.name}-{name}' if name != '' else cell.name)
                if per_cell is not None and len(seen_names) >= per_cell:
                    break
    return (names, tests)