#!/usr/bin/env python3
"""Validate that \\src attributes are preserved on cells after ABC synthesis.

Usage: python3 validate_src_retention.py <yosys_json_output> [--expect-source PREFIX]

Checks:
1. The JSON file is valid and contains modules
2. At least one cell exists in the design
3. At least one cell has a \\src attribute
4. The \\src attribute values look like valid source locations (file:line.col)
5. If --expect-source is given, at least one \\src value must reference that file prefix
"""

import json
import re
import sys

SRC_PATTERN = re.compile(r'^[\w./\\-]+:\d+\.\d+(-\d+\.\d+)?$')


def validate(json_path, expect_source=None):
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

    for mod_name, mod in modules.items():
        for cell_name, cell in mod.get('cells', {}).items():
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

    print(f"Total cells: {total_cells}")
    print(f"Cells with \\src: {cells_with_src}")
    print(f"Valid \\src values: {valid_src_values}")
    if expect_source:
        print(f"\\src values matching '{expect_source}': {matching_src_values}")

    if total_cells == 0:
        print("FAIL: No cells found in design")
        return False

    if cells_with_src == 0:
        print("FAIL: No cells have \\src attributes")
        print("This indicates node retention is not working properly.")
        return False

    if valid_src_values == 0:
        print("FAIL: No valid \\src location strings found")
        print(f"Found src values: {src_values}")
        return False

    if expect_source and matching_src_values == 0:
        print(f"FAIL: No \\src values reference expected source '{expect_source}'")
        print("This indicates node retention is not tracing back to the original source.")
        print(f"Found src values: {src_values[:10]}")
        return False

    pct = 100.0 * cells_with_src / total_cells
    print(f"PASS: {pct:.0f}% of cells ({cells_with_src}/{total_cells}) have \\src attributes")
    for sv in src_values[:5]:
        print(f"  Example: {sv}")
    return True


if __name__ == '__main__':
    expect_source = None
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    for i, a in enumerate(sys.argv[1:], 1):
        if a == '--expect-source' and i + 1 < len(sys.argv):
            expect_source = sys.argv[i + 1]

    if not args:
        print(f"Usage: {sys.argv[0]} <json_file> [--expect-source PREFIX]")
        sys.exit(1)
    if not validate(args[0], expect_source):
        sys.exit(1)
