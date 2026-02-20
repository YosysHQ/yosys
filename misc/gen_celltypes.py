#!/usr/bin/env python3
"""
Generate pre-computed static cell type tables. Outputs:
    kernel/gen_celltypes_data.h
    kernel/gen_celltypes_data.cc
"""

import os
import re
import sys
from dataclasses import dataclass

MAX_CELLS = 1024
MAX_PORTS = 20

# Build the IdString index map
def parse_constids(filepath):
    index_map = {}
    index = 1  # 0 is reserved for empty IdString
    with open(filepath, "r") as f:
        for line in f:
            line = line.strip()
            m = re.match(r"^X\((\S+)\)$", line)
            if m:
                name = m.group(1)
                index_map[name] = index
                index += 1
    return index_map


def resolve_id(index_map, name):
    """Resolve a name (e.g. '$and', 'A', '$_BUF_') to its constids index."""
    if name not in index_map:
        raise KeyError(f"ID '{name}' not found in constids.inc")
    return index_map[name]


# Cell type table builder
@dataclass
class Features:
    is_evaluable: bool = False
    is_combinatorial: bool = False
    is_synthesizable: bool = False
    is_stdcell: bool = False
    is_ff: bool = False
    is_mem_noff: bool = False
    is_anyinit: bool = False
    is_tristate: bool = False


@dataclass
class CellInfo:
    type_name: str
    inputs: MAX_CELLS
    outputs: list
    features: Features


def build_cell_table():
    cells = []

    def setup_type(type_name, inputs, outputs, features):
        cells.append(CellInfo(type_name, list(inputs), list(outputs),
                              Features(**vars(features))))

    # setup_internals_other
    f = Features(is_tristate=True)
    setup_type("$tribuf", ["A", "EN"], ["Y"], f)

    f = Features()
    setup_type("$assert", ["A", "EN"], [], f)
    setup_type("$assume", ["A", "EN"], [], f)
    setup_type("$live", ["A", "EN"], [], f)
    setup_type("$fair", ["A", "EN"], [], f)
    setup_type("$cover", ["A", "EN"], [], f)
    setup_type("$initstate", [], ["Y"], f)
    setup_type("$anyconst", [], ["Y"], f)
    setup_type("$anyseq", [], ["Y"], f)
    setup_type("$allconst", [], ["Y"], f)
    setup_type("$allseq", [], ["Y"], f)
    setup_type("$equiv", ["A", "B"], ["Y"], f)
    setup_type("$specify2", ["EN", "SRC", "DST"], [], f)
    setup_type("$specify3", ["EN", "SRC", "DST", "DAT"], [], f)
    setup_type("$specrule", ["EN_SRC", "EN_DST", "SRC", "DST"], [], f)
    setup_type("$print", ["EN", "ARGS", "TRG"], [], f)
    setup_type("$check", ["A", "EN", "ARGS", "TRG"], [], f)
    setup_type("$set_tag", ["A", "SET", "CLR"], ["Y"], f)
    setup_type("$get_tag", ["A"], ["Y"], f)
    setup_type("$overwrite_tag", ["A", "SET", "CLR"], [], f)
    setup_type("$original_tag", ["A"], ["Y"], f)
    setup_type("$future_ff", ["A"], ["Y"], f)
    setup_type("$scopeinfo", [], [], f)
    setup_type("$input_port", [], ["Y"], f)
    setup_type("$connect", ["A", "B"], [], f)

    # setup_internals_eval
    f = Features(is_evaluable=True)

    unary_ops = [
        "$not", "$pos", "$buf", "$neg",
        "$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor",
        "$reduce_bool",
        "$logic_not", "$slice", "$lut", "$sop",
    ]
    binary_ops = [
        "$and", "$or", "$xor", "$xnor",
        "$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx",
        "$lt", "$le", "$eq", "$ne", "$eqx", "$nex", "$ge", "$gt",
        "$add", "$sub", "$mul", "$div", "$mod", "$divfloor", "$modfloor",
        "$pow",
        "$logic_and", "$logic_or", "$concat", "$macc",
        "$bweqx",
    ]

    for t in unary_ops:
        setup_type(t, ["A"], ["Y"], f)
    for t in binary_ops:
        setup_type(t, ["A", "B"], ["Y"], f)

    for t in ["$mux", "$pmux", "$bwmux"]:
        setup_type(t, ["A", "B", "S"], ["Y"], f)
    for t in ["$bmux", "$demux"]:
        setup_type(t, ["A", "S"], ["Y"], f)

    setup_type("$lcu", ["P", "G", "CI"], ["CO"], f)
    setup_type("$alu", ["A", "B", "CI", "BI"], ["X", "Y", "CO"], f)
    setup_type("$macc_v2", ["A", "B", "C"], ["Y"], f)
    setup_type("$fa", ["A", "B", "C"], ["X", "Y"], f)

    # setup_internals_ff
    f = Features(is_ff=True)
    setup_type("$sr", ["SET", "CLR"], ["Q"], f)
    setup_type("$ff", ["D"], ["Q"], f)
    setup_type("$dff", ["CLK", "D"], ["Q"], f)
    setup_type("$dffe", ["CLK", "EN", "D"], ["Q"], f)
    setup_type("$dffsr", ["CLK", "SET", "CLR", "D"], ["Q"], f)
    setup_type("$dffsre", ["CLK", "SET", "CLR", "D", "EN"], ["Q"], f)
    setup_type("$adff", ["CLK", "ARST", "D"], ["Q"], f)
    setup_type("$adffe", ["CLK", "ARST", "D", "EN"], ["Q"], f)
    setup_type("$aldff", ["CLK", "ALOAD", "AD", "D"], ["Q"], f)
    setup_type("$aldffe", ["CLK", "ALOAD", "AD", "D", "EN"], ["Q"], f)
    setup_type("$sdff", ["CLK", "SRST", "D"], ["Q"], f)
    setup_type("$sdffe", ["CLK", "SRST", "D", "EN"], ["Q"], f)
    setup_type("$sdffce", ["CLK", "SRST", "D", "EN"], ["Q"], f)
    setup_type("$dlatch", ["EN", "D"], ["Q"], f)
    setup_type("$adlatch", ["EN", "D", "ARST"], ["Q"], f)
    setup_type("$dlatchsr", ["EN", "SET", "CLR", "D"], ["Q"], f)

    # setup_internals_anyinit
    f = Features(is_anyinit=True)
    setup_type("$anyinit", ["D"], ["Q"], f)

    # setup_internals_mem_noff
    f = Features(is_mem_noff=True)
    setup_type("$memrd", ["CLK", "EN", "ADDR"], ["DATA"], f)
    setup_type("$memrd_v2", ["CLK", "EN", "ARST", "SRST", "ADDR"],
               ["DATA"], f)
    setup_type("$memwr", ["CLK", "EN", "ADDR", "DATA"], [], f)
    setup_type("$memwr_v2", ["CLK", "EN", "ADDR", "DATA"], [], f)
    setup_type("$meminit", ["ADDR", "DATA"], [], f)
    setup_type("$meminit_v2", ["ADDR", "DATA", "EN"], [], f)
    setup_type("$mem",
               ["RD_CLK", "RD_EN", "RD_ADDR",
                "WR_CLK", "WR_EN", "WR_ADDR", "WR_DATA"],
               ["RD_DATA"], f)
    setup_type("$mem_v2",
               ["RD_CLK", "RD_EN", "RD_ARST", "RD_SRST", "RD_ADDR",
                "WR_CLK", "WR_EN", "WR_ADDR", "WR_DATA"],
               ["RD_DATA"], f)
    setup_type("$fsm", ["CLK", "ARST", "CTRL_IN"], ["CTRL_OUT"], f)

    # setup_stdcells_tristate
    f = Features(is_stdcell=True, is_tristate=True)
    setup_type("$_TBUF_", ["A", "E"], ["Y"], f)

    # setup_stdcells_eval
    f = Features(is_stdcell=True, is_evaluable=True)
    setup_type("$_BUF_", ["A"], ["Y"], f)
    setup_type("$_NOT_", ["A"], ["Y"], f)
    setup_type("$_AND_", ["A", "B"], ["Y"], f)
    setup_type("$_NAND_", ["A", "B"], ["Y"], f)
    setup_type("$_OR_", ["A", "B"], ["Y"], f)
    setup_type("$_NOR_", ["A", "B"], ["Y"], f)
    setup_type("$_XOR_", ["A", "B"], ["Y"], f)
    setup_type("$_XNOR_", ["A", "B"], ["Y"], f)
    setup_type("$_ANDNOT_", ["A", "B"], ["Y"], f)
    setup_type("$_ORNOT_", ["A", "B"], ["Y"], f)
    setup_type("$_MUX_", ["A", "B", "S"], ["Y"], f)
    setup_type("$_NMUX_", ["A", "B", "S"], ["Y"], f)
    setup_type("$_MUX4_", ["A", "B", "C", "D", "S", "T"], ["Y"], f)
    setup_type("$_MUX8_",
               ["A", "B", "C", "D", "E", "F", "G", "H", "S", "T", "U"],
               ["Y"], f)
    setup_type("$_MUX16_",
               ["A", "B", "C", "D", "E", "F", "G", "H",
                "I", "J", "K", "L", "M", "N", "O", "P",
                "S", "T", "U", "V"],
               ["Y"], f)
    setup_type("$_AOI3_", ["A", "B", "C"], ["Y"], f)
    setup_type("$_OAI3_", ["A", "B", "C"], ["Y"], f)
    setup_type("$_AOI4_", ["A", "B", "C", "D"], ["Y"], f)
    setup_type("$_OAI4_", ["A", "B", "C", "D"], ["Y"], f)

    # setup_stdcells_ff
    f = Features(is_stdcell=True, is_ff=True)
    NP = ["N", "P"]
    ZO = ["0", "1"]

    for c1 in NP:
        for c2 in NP:
            setup_type(f"$_SR_{c1}{c2}_", ["S", "R"], ["Q"], f)

    setup_type("$_FF_", ["D"], ["Q"], f)

    for c1 in NP:
        setup_type(f"$_DFF_{c1}_", ["C", "D"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            setup_type(f"$_DFFE_{c1}{c2}_", ["C", "D", "E"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in ZO:
                setup_type(f"$_DFF_{c1}{c2}{c3}_",
                           ["C", "R", "D"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in ZO:
                for c4 in NP:
                    setup_type(f"$_DFFE_{c1}{c2}{c3}{c4}_",
                               ["C", "R", "D", "E"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            setup_type(f"$_ALDFF_{c1}{c2}_",
                       ["C", "L", "AD", "D"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in NP:
                setup_type(f"$_ALDFFE_{c1}{c2}{c3}_",
                           ["C", "L", "AD", "D", "E"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in NP:
                setup_type(f"$_DFFSR_{c1}{c2}{c3}_",
                           ["C", "S", "R", "D"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in NP:
                for c4 in NP:
                    setup_type(f"$_DFFSRE_{c1}{c2}{c3}{c4}_",
                               ["C", "S", "R", "D", "E"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in ZO:
                setup_type(f"$_SDFF_{c1}{c2}{c3}_",
                           ["C", "R", "D"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in ZO:
                for c4 in NP:
                    setup_type(f"$_SDFFE_{c1}{c2}{c3}{c4}_",
                               ["C", "R", "D", "E"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in ZO:
                for c4 in NP:
                    setup_type(f"$_SDFFCE_{c1}{c2}{c3}{c4}_",
                               ["C", "R", "D", "E"], ["Q"], f)

    for c1 in NP:
        setup_type(f"$_DLATCH_{c1}_", ["E", "D"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in ZO:
                setup_type(f"$_DLATCH_{c1}{c2}{c3}_",
                           ["E", "R", "D"], ["Q"], f)

    for c1 in NP:
        for c2 in NP:
            for c3 in NP:
                setup_type(f"$_DLATCHSR_{c1}{c2}{c3}_",
                           ["E", "S", "R", "D"], ["Q"], f)

    return cells


def build_arrays(cells, index_map):
    cats = {
        "is_known": [0] * MAX_CELLS,
        "is_evaluable": [0] * MAX_CELLS,
        "is_combinatorial": [0] * MAX_CELLS,
        "is_synthesizable": [0] * MAX_CELLS,
        "is_stdcell": [0] * MAX_CELLS,
        "is_ff": [0] * MAX_CELLS,
        "is_mem_noff": [0] * MAX_CELLS,
        "is_anyinit": [0] * MAX_CELLS,
        "is_tristate": [0] * MAX_CELLS,
    }

    input_counts = [0] * MAX_CELLS
    input_ports = [[0] * MAX_PORTS for _ in range(MAX_CELLS)]
    output_counts = [0] * MAX_CELLS
    output_ports = [[0] * MAX_PORTS for _ in range(MAX_CELLS)]

    for cell in cells:
        idx = resolve_id(index_map, cell.type_name)
        if idx >= MAX_CELLS:
            print(f"WARNING: '{cell.type_name}' index {idx} >= MAX_CELLS "
                  f"({MAX_CELLS}), increase MAX_CELLS", file=sys.stderr)
            continue

        cats["is_known"][idx] = 1
        for feat in ["is_evaluable", "is_combinatorial", "is_synthesizable",
                      "is_stdcell", "is_ff", "is_mem_noff", "is_anyinit",
                      "is_tristate"]:
            if getattr(cell.features, feat):
                cats[feat][idx] = 1

        input_counts[idx] = len(cell.inputs)
        for j, port in enumerate(cell.inputs):
            input_ports[idx][j] = resolve_id(index_map, port)

        output_counts[idx] = len(cell.outputs)
        for j, port in enumerate(cell.outputs):
            output_ports[idx][j] = resolve_id(index_map, port)

    # Compat derived categories
    def bor(a, b):
        return [int(a[i] or b[i]) for i in range(MAX_CELLS)]
    def band(a, b):
        return [int(a[i] and b[i]) for i in range(MAX_CELLS)]
    def bnot(a):
        return [int(not a[i]) for i in range(MAX_CELLS)]

    mem_ff = bor(cats["is_ff"], cats["is_mem_noff"])
    internals_all = band(cats["is_known"], bnot(cats["is_stdcell"]))
    nomem_noff = band(cats["is_known"], bnot(mem_ff))

    compat = {
        "compat_internals_all": internals_all,
        "compat_mem_ff": mem_ff,
        "compat_nomem_noff": nomem_noff,
        "compat_internals_mem_ff": band(internals_all, mem_ff),
        "compat_internals_nomem_noff": band(internals_all, nomem_noff),
        "compat_stdcells_nomem_noff": band(cats["is_stdcell"], nomem_noff),
        "compat_stdcells_mem": band(cats["is_stdcell"], cats["is_mem_noff"]),
    }

    return (cats, compat,
            input_counts, input_ports, output_counts, output_ports)


def fmt_u8(name, data):
    lines = [f"const uint8_t {name}[{MAX_CELLS}] = {{"]
    for i in range(0, MAX_CELLS, 25):
        chunk = data[i:i + 25]
        lines.append("    " + ",".join(str(v) for v in chunk) + ",")
    lines.append("};")
    return "\n".join(lines)


def fmt_u16(name, data):
    lines = [f"const uint16_t {name}[{MAX_CELLS}] = {{"]
    for i in range(0, MAX_CELLS, 25):
        chunk = data[i:i + 25]
        lines.append("    " + ",".join(str(v) for v in chunk) + ",")
    lines.append("};")
    return "\n".join(lines)


def fmt_u32_2d(name, data):
    lines = [f"const uint32_t {name}[{MAX_CELLS}][{MAX_PORTS}] = {{"]
    for i in range(MAX_CELLS):
        lines.append("    {" + ",".join(str(v) for v in data[i]) + "},")
    lines.append("};")
    return "\n".join(lines)


def generate_cc(cats, compat, in_c, in_p, out_c, out_p):
    parts = [
        "// AUTO-GENERATED FILE - DO NOT EDIT",
        "// Generated by misc/gen_celltypes.py from kernel/constids.inc",
        "// Source of truth for cell definitions: misc/gen_celltypes.py",
        "//",
        "// Regenerate with: make kernel/gen_celltypes_data.cc",
        "",
        '#include "kernel/gen_celltypes_data.h"',
        "",
        "YOSYS_NAMESPACE_BEGIN",
        "namespace StaticCellTypes {",
        "namespace GeneratedData {",
        "",
    ]

    for name, data in cats.items():
        parts.append(fmt_u8(name, data))
        parts.append("")

    for name, data in compat.items():
        parts.append(fmt_u8(name, data))
        parts.append("")

    parts.append(fmt_u16("port_inputs_counts", in_c))
    parts.append("")
    parts.append(fmt_u32_2d("port_inputs_ports", in_p))
    parts.append("")
    parts.append(fmt_u16("port_outputs_counts", out_c))
    parts.append("")
    parts.append(fmt_u32_2d("port_outputs_ports", out_p))
    parts.append("")

    parts.extend([
        "} // namespace GeneratedData",
        "} // namespace StaticCellTypes",
        "YOSYS_NAMESPACE_END",
        "",
    ])
    return "\n".join(parts)


def generate_header():
    return f"""\
// AUTO-GENERATED FILE - DO NOT EDIT
// Generated by misc/gen_celltypes.py from kernel/constids.inc
// Regenerate with: make kernel/gen_celltypes_data.cc

#ifndef GEN_CELLTYPES_DATA_H
#define GEN_CELLTYPES_DATA_H

#include "kernel/yosys.h"
#include <cstdint>

YOSYS_NAMESPACE_BEGIN
namespace StaticCellTypes {{

constexpr int GEN_MAX_CELLS = {MAX_CELLS};
constexpr int GEN_MAX_PORTS = {MAX_PORTS};

namespace GeneratedData {{

extern const uint8_t is_known[GEN_MAX_CELLS];
extern const uint8_t is_evaluable[GEN_MAX_CELLS];
extern const uint8_t is_combinatorial[GEN_MAX_CELLS];
extern const uint8_t is_synthesizable[GEN_MAX_CELLS];
extern const uint8_t is_stdcell[GEN_MAX_CELLS];
extern const uint8_t is_ff[GEN_MAX_CELLS];
extern const uint8_t is_mem_noff[GEN_MAX_CELLS];
extern const uint8_t is_anyinit[GEN_MAX_CELLS];
extern const uint8_t is_tristate[GEN_MAX_CELLS];

extern const uint8_t compat_internals_all[GEN_MAX_CELLS];
extern const uint8_t compat_mem_ff[GEN_MAX_CELLS];
extern const uint8_t compat_nomem_noff[GEN_MAX_CELLS];
extern const uint8_t compat_internals_mem_ff[GEN_MAX_CELLS];
extern const uint8_t compat_internals_nomem_noff[GEN_MAX_CELLS];
extern const uint8_t compat_stdcells_nomem_noff[GEN_MAX_CELLS];
extern const uint8_t compat_stdcells_mem[GEN_MAX_CELLS];

extern const uint16_t port_inputs_counts[GEN_MAX_CELLS];
extern const uint32_t port_inputs_ports[GEN_MAX_CELLS][GEN_MAX_PORTS];
extern const uint16_t port_outputs_counts[GEN_MAX_CELLS];
extern const uint32_t port_outputs_ports[GEN_MAX_CELLS][GEN_MAX_PORTS];

}} // namespace GeneratedData

struct GenCategory {{
	const uint8_t* data;
	bool operator()(RTLIL::IdString type) const {{
		size_t idx = type.index_;
		return idx < GEN_MAX_CELLS && data[idx];
	}}
}};

struct GenPortLookup {{
	const uint16_t* counts;
	const uint32_t (*ports)[GEN_MAX_PORTS];

	bool contains(RTLIL::IdString type, RTLIL::IdString port) const {{
		size_t idx = type.index_;
		if (idx >= GEN_MAX_CELLS)
			return false;
		uint16_t count = counts[idx];
		for (uint16_t i = 0; i < count; i++) {{
			if (ports[idx][i] == (uint32_t)port.index_)
				return true;
		}}
		return false;
	}}
}};

inline GenCategory gen_is_known()         {{ return {{GeneratedData::is_known}}; }}
inline GenCategory gen_is_evaluable()     {{ return {{GeneratedData::is_evaluable}}; }}
inline GenCategory gen_is_combinatorial() {{ return {{GeneratedData::is_combinatorial}}; }}
inline GenCategory gen_is_synthesizable() {{ return {{GeneratedData::is_synthesizable}}; }}
inline GenCategory gen_is_stdcell()       {{ return {{GeneratedData::is_stdcell}}; }}
inline GenCategory gen_is_ff()            {{ return {{GeneratedData::is_ff}}; }}
inline GenCategory gen_is_mem_noff()      {{ return {{GeneratedData::is_mem_noff}}; }}
inline GenCategory gen_is_anyinit()       {{ return {{GeneratedData::is_anyinit}}; }}
inline GenCategory gen_is_tristate()      {{ return {{GeneratedData::is_tristate}}; }}

inline GenCategory gen_compat_internals_all()        {{ return {{GeneratedData::compat_internals_all}}; }}
inline GenCategory gen_compat_mem_ff()               {{ return {{GeneratedData::compat_mem_ff}}; }}
inline GenCategory gen_compat_nomem_noff()           {{ return {{GeneratedData::compat_nomem_noff}}; }}
inline GenCategory gen_compat_internals_mem_ff()     {{ return {{GeneratedData::compat_internals_mem_ff}}; }}
inline GenCategory gen_compat_internals_nomem_noff() {{ return {{GeneratedData::compat_internals_nomem_noff}}; }}
inline GenCategory gen_compat_stdcells_nomem_noff()  {{ return {{GeneratedData::compat_stdcells_nomem_noff}}; }}
inline GenCategory gen_compat_stdcells_mem()         {{ return {{GeneratedData::compat_stdcells_mem}}; }}

inline GenPortLookup gen_port_inputs() {{
	return {{GeneratedData::port_inputs_counts, GeneratedData::port_inputs_ports}};
}}

inline GenPortLookup gen_port_outputs() {{
	return {{GeneratedData::port_outputs_counts, GeneratedData::port_outputs_ports}};
}}

}} // namespace StaticCellTypes
YOSYS_NAMESPACE_END

#endif // GEN_CELLTYPES_DATA_H
"""


def main():
    if len(sys.argv) > 1:
        yosys_src = sys.argv[1]
    else:
        yosys_src = os.environ.get("YOSYS_SRC", ".")

    constids_path = os.path.join(yosys_src, "kernel", "constids.inc")
    header_out = os.path.join(yosys_src, "kernel", "gen_celltypes_data.h")
    data_out = os.path.join(yosys_src, "kernel", "gen_celltypes_data.cc")

    if not os.path.exists(constids_path):
        print(f"Error: {constids_path} not found.", file=sys.stderr)
        sys.exit(1)

    # Parse
    print(f"Parsing {constids_path}...", file=sys.stderr)
    index_map = parse_constids(constids_path)
    print(f"  {len(index_map)} IdString constants", file=sys.stderr)

    # Build tables
    cells = build_cell_table()
    print(f"  {len(cells)} cell types defined", file=sys.stderr)

    try:
        result = build_arrays(cells, index_map)
    except KeyError as e:
        print(f"Error: {e}", file=sys.stderr)
        print(f"  kernel/constids.inc may be missing entries.",
              file=sys.stderr)
        sys.exit(1)

    cats, compat, in_c, in_p, out_c, out_p = result

    # Write header
    with open(header_out, "w") as f:
        f.write(generate_header())
    print(f"Wrote {header_out}", file=sys.stderr)

    # Write data
    with open(data_out, "w") as f:
        f.write(generate_cc(cats, compat, in_c, in_p, out_c, out_p))
    print(f"Wrote {data_out}", file=sys.stderr)


if __name__ == "__main__":
    main()
