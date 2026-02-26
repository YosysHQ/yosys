#!/usr/bin/env python3
"""Validate the sideband invariant: cell names in Yosys JSON match cell names
in the corresponding Verilog netlist, and \\src attributes are present.

This validates the key property needed for the cell-name sideband join approach:
after synthesis, write_json and write_verilog produce outputs where cell instance
names are identical, so the JSON (with \\src attributes) can be used as a sideband
to annotate post-PnR netlists that preserve those cell names.

Usage:
    python3 validate_src_sideband.py <json_file> <verilog_file> [--expect-source PREFIX]

Checks:
1. JSON contains cells with \\src attributes
2. Cell names in JSON match cell names in Verilog
3. \\src values have valid file:line.col format
4. If --expect-source given, at least one \\src references that prefix
"""

import json
import re
import sys


# Match src patterns like "counter.v:3.5-8.8" or "counter.v:3.5"
SRC_PATTERN = re.compile(r'^[\w./\\-]+:\d+\.\d+(-\d+\.\d+)?$')

# Verilog keywords to skip when parsing instantiations
VERILOG_KEYWORDS = frozenset({
    'module', 'input', 'output', 'wire', 'reg', 'assign', 'endmodule',
    'inout', 'parameter', 'localparam', 'always', 'initial', 'function',
    'task', 'generate', 'genvar', 'supply0', 'supply1', 'if', 'else',
    'begin', 'end', 'case', 'casex', 'casez', 'default', 'endcase',
    'for', 'while', 'defparam', 'specify', 'endspecify', 'or', 'and',
    'not', 'buf', 'pullup', 'pulldown',
})

# Match Verilog cell instantiations after #(...) removal:
#   <cell_type> <instance_name> (
# Handles escaped names like \$abc$123 and simple names like _123_
VERILOG_CELL_RE = re.compile(
    r'^\s*(\S+)\s+'           # cell type
    r'(\\[^\s]+|\w+)\s*\(',   # instance name (escaped or simple)
    re.MULTILINE
)


def _strip_param_blocks(content):
    """Remove Verilog #(...) parameter blocks, handling nested parentheses."""
    result = []
    i = 0
    while i < len(content):
        if content[i] == '#' and i + 1 < len(content) and content[i + 1] == '(':
            # Skip #(...) including nested parens
            depth = 0
            i += 1  # skip '#'
            while i < len(content):
                if content[i] == '(':
                    depth += 1
                elif content[i] == ')':
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
        else:
            result.append(content[i])
            i += 1
    return ''.join(result)


def extract_json_cells(json_path):
    """Extract cell names and their attributes from Yosys JSON output.

    Skips $specify cells which are ABC9 internal timing specification cells
    that don't appear in the Verilog netlist output.
    """
    with open(json_path) as f:
        data = json.load(f)

    cells = {}
    for mod_name, mod in data.get('modules', {}).items():
        for cell_name, cell in mod.get('cells', {}).items():
            cell_type = cell.get('type', '')
            if cell_type.startswith('$specify') or cell_type == '$specrule':
                continue
            cells[cell_name] = {
                'type': cell_type,
                'src': cell.get('attributes', {}).get('src'),
            }
    return cells


def extract_verilog_cells(verilog_path):
    """Extract cell instance names from Verilog netlist.

    Parses module instantiations of the form:
        cell_type [#(params)] instance_name (
    Handles escaped identifiers (\\name) and #(...) parameter blocks.
    """
    with open(verilog_path) as f:
        content = f.read()

    # Remove comments
    content = re.sub(r'//.*$', '', content, flags=re.MULTILINE)
    content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)

    # Remove #(...) parameter blocks so regex sees: cell_type instance_name (
    content = _strip_param_blocks(content)

    cell_names = set()
    for match in VERILOG_CELL_RE.finditer(content):
        cell_type = match.group(1)
        instance_name = match.group(2)

        # Strip leading backslash from escaped identifiers for comparison
        clean_type = cell_type.lstrip('\\')

        # Skip Verilog keywords that look like instantiations
        if clean_type in VERILOG_KEYWORDS:
            continue

        # Strip leading backslash from escaped identifiers
        if instance_name.startswith('\\'):
            instance_name = instance_name[1:]

        cell_names.add(instance_name)

    return cell_names


def validate(json_path, verilog_path, expect_source=None):
    """Validate the sideband invariant between JSON and Verilog outputs."""
    json_cells = extract_json_cells(json_path)
    verilog_cells = extract_verilog_cells(verilog_path)

    print(f"JSON cells: {len(json_cells)}")
    print(f"Verilog cells: {len(verilog_cells)}")

    ok = True

    # Check 1: We have cells
    if not json_cells:
        print("FAIL: No cells found in JSON output")
        return False
    if not verilog_cells:
        print("FAIL: No cells found in Verilog output")
        return False

    # Check 2: Cell name match (the sideband invariant)
    json_names = set(json_cells.keys())
    only_in_json = json_names - verilog_cells
    only_in_verilog = verilog_cells - json_names

    if only_in_json:
        print(f"WARNING: {len(only_in_json)} cells only in JSON: "
              f"{sorted(only_in_json)[:5]}")
    if only_in_verilog:
        print(f"WARNING: {len(only_in_verilog)} cells only in Verilog: "
              f"{sorted(only_in_verilog)[:5]}")

    common = json_names & verilog_cells
    if not common:
        print("FAIL: No common cell names between JSON and Verilog")
        return False

    match_pct = 100.0 * len(common) / max(len(json_names), len(verilog_cells))
    print(f"Cell name match: {len(common)}/{max(len(json_names), len(verilog_cells))} "
          f"({match_pct:.0f}%)")

    if match_pct < 90:
        print("FAIL: Cell name match below 90% - sideband invariant violated")
        ok = False

    # Check 3: src attributes present
    cells_with_src = sum(1 for c in json_cells.values() if c['src'])
    valid_src = 0
    matching_src = 0
    src_examples = []

    for cell in json_cells.values():
        if cell['src']:
            for part in cell['src'].split('|'):
                part = part.strip()
                if part and SRC_PATTERN.match(part):
                    valid_src += 1
                    src_examples.append(part)
                    if expect_source and part.startswith(expect_source):
                        matching_src += 1

    print(f"Cells with \\src: {cells_with_src}/{len(json_cells)}")
    print(f"Valid \\src values: {valid_src}")

    if cells_with_src == 0:
        print("FAIL: No cells have \\src attributes")
        print("This indicates node retention is not working properly.")
        return False

    if valid_src == 0:
        print("FAIL: No valid \\src location strings found")
        ok = False

    if expect_source:
        print(f"\\src values matching '{expect_source}': {matching_src}")
        if matching_src == 0:
            print(f"FAIL: No \\src values reference expected source '{expect_source}'")
            ok = False

    if ok:
        pct = 100.0 * cells_with_src / len(json_cells)
        print(f"PASS: Sideband invariant holds - {pct:.0f}% of cells have \\src, "
              f"cell names match between JSON and Verilog")
        for sv in src_examples[:5]:
            print(f"  Example: {sv}")

    return ok


if __name__ == '__main__':
    expect_source = None
    positional = []
    argv = sys.argv[1:]
    i = 0
    while i < len(argv):
        if argv[i] == '--expect-source' and i + 1 < len(argv):
            expect_source = argv[i + 1]
            i += 2
        elif not argv[i].startswith('--'):
            positional.append(argv[i])
            i += 1
        else:
            i += 1

    if len(positional) < 2:
        print(f"Usage: {sys.argv[0]} <json_file> <verilog_file> "
              f"[--expect-source PREFIX]")
        sys.exit(1)

    if not validate(positional[0], positional[1], expect_source):
        sys.exit(1)
