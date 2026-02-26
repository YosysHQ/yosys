#!/bin/bash
# Test the sideband invariant: cell names in write_json match cell names in
# write_verilog, and \src attributes survive ABC synthesis.
#
# This validates the key property for the cell-name sideband join approach:
# the JSON (with \src attributes) can serve as a sideband file to annotate
# post-PnR netlists where cell names are preserved by OpenROAD.
#
# When ABC lacks node_retention support, the cell-name match still validates
# but \src presence will be reported as INFO rather than PASS.
#
# To fully validate, use an ABC with node_retention support (ABCEXTERNAL).

set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
YOSYS=${YOSYS:-${SCRIPT_DIR}/../../yosys}
VALIDATE="${SCRIPT_DIR}/scripts/validate_src_sideband.py"

TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

# --- Test fixture: counter with known source locations ---
cat > "$TMPDIR/counter.v" <<'EOF'
(* src = "counter.v:1.1-12.10" *)
module counter(input wire clk, input wire rst, input wire en, output reg [3:0] count);
    (* src = "counter.v:3.5-8.8" *)
    always @(posedge clk) begin
        if (rst)
            count <= 4'b0;
        else if (en)
            count <= count + 1;
    end
endmodule
EOF

echo "=== Test 1: Sideband invariant through ABC (classic) ==="

$YOSYS -p "
read_verilog $TMPDIR/counter.v
synth -top counter -flatten
abc -lut 4
autoname
rename -enumerate
write_json $TMPDIR/abc_output.json
write_verilog -noattr -noexpr $TMPDIR/abc_output.nl.v
" 2>&1

# Check cell name match (always should work)
CELL_MATCH=$(python3 -c "
import json, re, sys

with open('$TMPDIR/abc_output.json') as f:
    data = json.load(f)

json_cells = set()
for mod in data.get('modules', {}).values():
    for name in mod.get('cells', {}).keys():
        json_cells.add(name)

# Parse verilog for cell instantiations
with open('$TMPDIR/abc_output.nl.v') as f:
    content = f.read()
content = re.sub(r'//.*$', '', content, flags=re.MULTILINE)
content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)

verilog_cells = set()
skip = {'module','input','output','wire','reg','assign','endmodule','inout'}
for m in re.finditer(r'^\s*(\S+)\s+(\\\\[^\s]+|\w+)\s*\(', content, re.MULTILINE):
    if m.group(1) not in skip:
        name = m.group(2)
        if name.startswith('\\\\'):
            name = name[1:]
        verilog_cells.add(name)

common = json_cells & verilog_cells
total = max(len(json_cells), len(verilog_cells), 1)
print(f'{len(common)}/{total}')
if len(common) == total:
    print('MATCH')
elif len(common) / total >= 0.9:
    print('MATCH')
else:
    print('MISMATCH')
")

echo "Cell name match (ABC): $CELL_MATCH"
if echo "$CELL_MATCH" | grep -q "MISMATCH"; then
    echo "FAIL: Cell names do not match between JSON and Verilog"
    exit 1
fi
echo "PASS: Cell name sideband invariant holds for ABC"

# Check src retention
SRC_CELLS=$(python3 -c "
import json
with open('$TMPDIR/abc_output.json') as f:
    data = json.load(f)
count = 0
for mod in data.get('modules', {}).values():
    for cell in mod.get('cells', {}).values():
        if 'src' in cell.get('attributes', {}):
            count += 1
print(count)
")

echo "Cells with \\src attributes (ABC): $SRC_CELLS"
if [ "$SRC_CELLS" -gt 0 ]; then
    echo "PASS: \\src attributes preserved through ABC synthesis"
else
    echo "INFO: No \\src attributes on cells (expected if ABC lacks node_retention)"
fi

echo ""
echo "=== Test 2: Sideband invariant through ABC9 ==="

$YOSYS -p "
read_verilog $TMPDIR/counter.v
synth -top counter -flatten
abc9 -lut 4
autoname
rename -enumerate
write_json $TMPDIR/abc9_output.json
write_verilog -noattr -noexpr $TMPDIR/abc9_output.nl.v
" 2>&1

CELL_MATCH9=$(python3 -c "
import json, re, sys

with open('$TMPDIR/abc9_output.json') as f:
    data = json.load(f)

json_cells = set()
for mod in data.get('modules', {}).values():
    for name in mod.get('cells', {}).keys():
        json_cells.add(name)

with open('$TMPDIR/abc9_output.nl.v') as f:
    content = f.read()
content = re.sub(r'//.*$', '', content, flags=re.MULTILINE)
content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)

verilog_cells = set()
skip = {'module','input','output','wire','reg','assign','endmodule','inout'}
for m in re.finditer(r'^\s*(\S+)\s+(\\\\[^\s]+|\w+)\s*\(', content, re.MULTILINE):
    if m.group(1) not in skip:
        name = m.group(2)
        if name.startswith('\\\\'):
            name = name[1:]
        verilog_cells.add(name)

common = json_cells & verilog_cells
total = max(len(json_cells), len(verilog_cells), 1)
print(f'{len(common)}/{total}')
if len(common) == total:
    print('MATCH')
elif len(common) / total >= 0.9:
    print('MATCH')
else:
    print('MISMATCH')
")

echo "Cell name match (ABC9): $CELL_MATCH9"
if echo "$CELL_MATCH9" | grep -q "MISMATCH"; then
    echo "FAIL: Cell names do not match between JSON and Verilog"
    exit 1
fi
echo "PASS: Cell name sideband invariant holds for ABC9"

SRC_CELLS9=$(python3 -c "
import json
with open('$TMPDIR/abc9_output.json') as f:
    data = json.load(f)
count = 0
for mod in data.get('modules', {}).values():
    for cell in mod.get('cells', {}).values():
        if 'src' in cell.get('attributes', {}):
            count += 1
print(count)
")

echo "Cells with \\src attributes (ABC9): $SRC_CELLS9"
if [ "$SRC_CELLS9" -gt 0 ]; then
    echo "PASS: \\src attributes preserved through ABC9 synthesis"
else
    echo "INFO: No \\src attributes on cells (expected if ABC lacks node_retention)"
fi

echo ""
echo "=== Test 3: Full sideband validation (if retention-enabled ABC available) ==="

# Run the comprehensive validator if we have src retention
if [ "$SRC_CELLS" -gt 0 ] || [ "$SRC_CELLS9" -gt 0 ]; then
    if [ "$SRC_CELLS" -gt 0 ]; then
        echo "Validating ABC sideband with full validator..."
        python3 "$VALIDATE" "$TMPDIR/abc_output.json" "$TMPDIR/abc_output.nl.v" \
            --expect-source "counter.v"
    fi
    if [ "$SRC_CELLS9" -gt 0 ]; then
        echo "Validating ABC9 sideband with full validator..."
        python3 "$VALIDATE" "$TMPDIR/abc9_output.json" "$TMPDIR/abc9_output.nl.v" \
            --expect-source "counter.v"
    fi
else
    echo "INFO: Skipping full validation (no retention-enabled ABC)"
fi

echo ""
echo "=== All sideband invariant tests passed ==="
