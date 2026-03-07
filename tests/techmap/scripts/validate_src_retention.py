#!/usr/bin/env python3
"""Validate that \\src attributes are preserved on cells after ABC9 synthesis.

Usage: python3 validate_src_retention.py <yosys_json_output> [options]

Options:
    --expect-source PREFIX  At least one \\src must reference this file prefix
    --cell-type TYPE        Only check cells of this type (e.g. $lut)

Checks:
1. The JSON file is valid and contains modules
2. At least one matching cell exists in the design
3. At least one matching cell has a \\src attribute
4. The \\src attribute values look like valid source locations (file:line.col)
5. If --expect-source is given, at least one \\src value must reference that prefix
"""

import json
import re
import sys

SRC_PATTERN = re.compile(r'^[\w./\\-]+:\d+\.\d+(-\d+\.\d+)?$')


def validate(json_path, expect_source=None, cell_type=None):
    with open(json_path) as f:
        data = json.load(f)

    modules = data.get('modules', {})
    if not modules:
        print("FAIL: No modules found in JSON output")
        return False

    total_cells = 0
    cells_with_src = 0
    valid_src_values = 0
    matching_src_values = 0
    src_values = []
    type_label = f" (type={cell_type})" if cell_type else ""

    for mod_name, mod in modules.items():
        for cell_name, cell in mod.get('cells', {}).items():
            if cell_type and cell.get('type') != cell_type:
                continue
            total_cells += 1
            attrs = cell.get('attributes', {})
            if 'src' in attrs:
                cells_with_src += 1
                src_val = attrs['src']
                src_values.append(src_val)
                # src can be pipe-separated for multiple source locations
                for part in src_val.split('|'):
                    part = part.strip()
                    if part and SRC_PATTERN.match(part):
                        valid_src_values += 1
                        if expect_source and part.startswith(expect_source):
                            matching_src_values += 1

    print(f"Total cells{type_label}: {total_cells}")
    print(f"Cells with \\src: {cells_with_src}")
    print(f"Valid \\src values: {valid_src_values}")
    if expect_source:
        print(f"\\src values matching '{expect_source}': {matching_src_values}")

    if total_cells == 0:
        print(f"FAIL: No cells{type_label} found in design")
        return False

    if cells_with_src == 0:
        print(f"FAIL: No cells{type_label} have \\src attributes")
        return False

    if valid_src_values == 0:
        print("FAIL: No valid \\src location strings found")
        print(f"Found src values: {src_values}")
        return False

    if expect_source and matching_src_values == 0:
        print(f"FAIL: No \\src values reference expected source '{expect_source}'")
        print(f"Found src values: {src_values[:10]}")
        return False

    pct = 100.0 * cells_with_src / total_cells
    print(f"PASS: {pct:.0f}% of cells ({cells_with_src}/{total_cells}) have \\src attributes")
    for sv in src_values[:5]:
        print(f"  Example: {sv}")
    return True


if __name__ == '__main__':
    expect_source = None
    cell_type = None
    positional = []
    argv = sys.argv[1:]
    i = 0
    while i < len(argv):
        if argv[i] == '--expect-source' and i + 1 < len(argv):
            expect_source = argv[i + 1]
            i += 2
        elif argv[i] == '--cell-type' and i + 1 < len(argv):
            cell_type = argv[i + 1]
            i += 2
        elif not argv[i].startswith('--'):
            positional.append(argv[i])
            i += 1
        else:
            i += 1

    if not positional:
        print(f"Usage: {sys.argv[0]} <json_file> [--expect-source PREFIX] [--cell-type TYPE]")
        sys.exit(1)
    if not validate(positional[0], expect_source, cell_type):
        sys.exit(1)
