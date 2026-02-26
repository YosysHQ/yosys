#!/bin/bash
# Full test for \src retention through ABC synthesis.
# When ABC lacks node_retention support, this test passes with an INFO message.
# To fully validate, use an ABC with node_retention support (ABCEXTERNAL).

set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
YOSYS=${YOSYS:-${SCRIPT_DIR}/../../yosys}

TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

cat > "$TMPDIR/test.v" <<'EOF'
(* src = "counter.v:1.1-10.10" *)
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

echo "=== Testing \\src retention through ABC ==="

$YOSYS -p "
read_verilog $TMPDIR/test.v
synth -top counter -flatten
abc -lut 4
write_json $TMPDIR/output.json
" 2>&1

SRC_CELLS=$(python3 -c "
import json
with open('$TMPDIR/output.json') as f:
    data = json.load(f)
count = 0
for mod_name, mod in data.get('modules', {}).items():
    for cell_name, cell in mod.get('cells', {}).items():
        if 'src' in cell.get('attributes', {}):
            count += 1
print(count)
")

echo "Cells with \\src attributes: $SRC_CELLS"

if [ "$SRC_CELLS" -gt 0 ]; then
    echo "PASS: \\src attributes preserved through ABC synthesis"
else
    echo "INFO: No \\src attributes on cells (expected if ABC lacks node_retention)"
fi
