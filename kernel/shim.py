from pathlib import Path

with open("kernel/constids.inc") as f:
    X = set([line[2:-2] for line in f.readlines() if len(line) > 2])

# f.write(X)
# ValidConstID = NewType('ValidConstID', str)


class ValidConstID(str):
    # https://stackoverflow.com/questions/69844072/why-isnt-python-newtype-compatible-with-isinstance-and-type
    def __new__(cls, *args, **kwargs):
        return str.__new__(cls, *args, **kwargs)


def id(str):
    assert str in X
    return ValidConstID(str)


class CellType():
    name: str
    inputs: list[ValidConstID, ValidConstID | int]
    outputs = list[ValidConstID, ValidConstID | int]
    other_params = list[ValidConstID, type]

    def __init__(self, name, inputs, outputs, other_params, add_wire_width_expr):
        self.name = name
        self.inputs = inputs
        self.outputs = outputs
        self.other_params = other_params
        self.add_wire_width_expr = add_wire_width_expr
        self.inputs.sort()
        self.outputs.sort()
        self.other_params.sort()

    def arg_inputs(self, call=False):
        s = ""
        if call:
            s += "".join(map(
                lambda inp: f"sig_{inp[0].lower()}, ", self.inputs))
        else:
            s += "".join(map(
                lambda inp: f"const RTLIL::SigSpec &sig_{inp[0].lower()}, ", self.inputs))
        return s

    def arg_outputs(self, call=False):
        s = ""
        if call:
            s += "".join(map(
                lambda outp: f"sig_{outp[0].lower()}, ", self.outputs))
        else:
            s += "".join(map(
                lambda outp: f"const RTLIL::SigSpec &sig_{outp[0].lower()}, ", self.outputs))
        return s

    def emit_add_h(self, filename):

        def _argumentize_param(param):
            is_only_one_param_signed = len(
                list(filter(lambda x: "_SIGNED" in x[0], self.other_params))) == 1
            if "_SIGNED" in param and is_only_one_param_signed:
                return "is_signed = false"
            else:
                return param.lower()

        with open(filename, 'a') as f:
            f.write(
                f"RTLIL::Cell* add{self.name.title()}(RTLIL::IdString name, ")
            f.write(self.arg_inputs() + self.arg_outputs())
            f.write("".join(
                map(lambda par: f"{par[1].__name__} {_argumentize_param(par[0])}, ", self.other_params)))
            f.write("const std::string &src = \"\");\n")

    def emit_add_cc(self, filename):

        def _argumentize_param(param):
            is_only_one_param_signed = len(
                list(filter(lambda x: "_SIGNED" in x[0], self.other_params))) == 1
            if "_SIGNED" in param and is_only_one_param_signed:
                return "is_signed"
            else:
                return param.lower()

        with open(filename, 'a') as f:
            f.write(
                f"RTLIL::Cell* RTLIL::Module::add{self.name.title()}(RTLIL::IdString name, ")
            f.write(self.arg_inputs() + self.arg_outputs())
            f.write("".join(
                map(lambda par: f"{par[1].__name__} {_argumentize_param(par[0])}, ", self.other_params)))
            f.write("const std::string &src)\n")

            f.write("{\n")
            f.write(
                f"\tRTLIL::Cell *cell = addCell(name, ID(${self.name}));\n")

            for param in self.other_params:
                f.write(
                    f"\tcell->parameters[ID::{param[0]}] = {_argumentize_param(param[0])};\n")

            for input, width in self.inputs:
                if isinstance(width, ValidConstID):
                    f.write(
                        f"\tcell->parameters[ID::{width}] = sig_{input.lower()}.size();\n")

            for output, width in self.outputs:
                if isinstance(width, ValidConstID):
                    f.write(
                        f"\tcell->parameters[ID::{width}] = sig_{output.lower()}.size();\n")

            for input, _ in self.inputs:
                f.write(
                    f"\tcell->setPort(ID::{input}, sig_{input.lower()});\n")
            for output, _ in self.outputs:
                f.write(
                    f"\tcell->setPort(ID::{output}, sig_{output.lower()});\n")
            f.write("\tcell->set_src_attribute(src);\n")
            f.write("\treturn cell;\n")
            f.write("}\n\n")

            if self.add_wire_width_expr:
                f.write(
                    f"RTLIL::SigSpec RTLIL::Module::{self.name.title()}(RTLIL::IdString name, {self.arg_inputs()}")
                f.write("".join(
                    map(lambda par: f"{par[1].__name__} {_argumentize_param(par[0])}, ", self.other_params)))
                f.write("const std::string &src) {\n")
                f.write(
                    f"\tRTLIL::SigSpec sig_y = addWire(NEW_ID, {self.add_wire_width_expr});\n")
                f.write(
                    f"\tadd{self.name.title()}(name, {self.arg_inputs(call=True)}{self.arg_outputs(call=True)}")
                f.write("".join(
                    map(lambda par: f"{_argumentize_param(par[0])}", self.other_params)))
                f.write(f", src);\n")
                f.write("\treturn sig_y;\n")
                f.write("}\n\n")
            # _func(const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed, const std::string &src) { \
            #     RTLIL::SigSpec sig_y = addWire(NEW_ID, _y_size);         \
            #     add ## _func(name, sig_a, sig_b, sig_y, is_signed, src); \
            #     return sig_y;                                            \
            # }


def unary(name):
    inputs = [(id("A"), id("A_WIDTH"))]
    outputs = [(id("Y"), id("Y_WIDTH"))]
    other_params = [(id("A_SIGNED"), bool)]
    add_wire_width_expr = "sig_a.size()"
    return CellType(name, inputs, outputs, other_params, add_wire_width_expr)


celltypes = []
celltypes += [unary("pos")]
celltypes += [unary("neg")]
celltypes += [unary("not")]

shim_headers = Path("kernel/adds.shim.h")
shim_headers.unlink(missing_ok=True)
shim_src = Path("kernel/adds.shim.cc")
shim_src.unlink(missing_ok=True)


def emit_boilerplate():
    warning = "/* Generated by shim.py, do not modify */\n"
    with open(shim_headers, 'a') as f:
        f.write(warning)
        f.write('#ifndef SHIM_H\n')
        f.write('#define SHIM_H\n')
        f.write('#include "kernel/yosys.h"\n')
        f.write('#endif /* SHIM_H */\n')

    with open(shim_src, 'a') as f:
        f.write(warning)
        f.write('#include "kernel/yosys.h"\n')
        f.write("USING_YOSYS_NAMESPACE\n")


emit_boilerplate()

for celltype in celltypes:
    celltype.emit_add_h(shim_headers)

for celltype in celltypes:
    celltype.emit_add_cc(shim_src)
