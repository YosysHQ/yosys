#!/usr/bin/env bash
# Simulation regression for issue #4402.
# Confirms pre- and post-synthesis outputs match for a module with a signed input port.
# Requires iverilog/vvp in PATH. Skips if not found.
set -e

if ! command -v iverilog > /dev/null 2>&1; then
    echo "SKIP: iverilog not found"
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
YOSYS="${YOSYS:-$SCRIPT_DIR/../../yosys}"
TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

cat > "$TMPDIR/top.v" << 'EOF'
module top (y, clk, wire0);
  output wire y;
  input wire clk;
  input wire signed wire0;
  reg reg1;
  reg var2 = 0;
  reg var3 = 0;
  assign y = reg1;
  always @(posedge clk) begin
    reg1 = ($signed(wire0 <= 0) ? $unsigned(-var3) : (^~$signed(var2)));
  end
endmodule
EOF

# Synthesize
"$YOSYS" -q -p "
read_verilog $TMPDIR/top.v
hierarchy -top top
proc
write_verilog $TMPDIR/top_syn.v
"

# Simulate original
iverilog -o "$TMPDIR/sim_orig" "$SCRIPT_DIR/issue4402_tb.v" "$TMPDIR/top.v" 2>/dev/null
# Simulate synthesized
iverilog -o "$TMPDIR/sim_syn"  "$SCRIPT_DIR/issue4402_tb.v" "$TMPDIR/top_syn.v" 2>/dev/null

ORIG=$(vvp "$TMPDIR/sim_orig" 2>/dev/null | grep "y =")
SYN=$(vvp  "$TMPDIR/sim_syn"  2>/dev/null | grep "y =")

echo "Original:    $ORIG"
echo "Synthesized: $SYN"

if [ "$ORIG" != "$SYN" ]; then
    echo "FAIL: pre/post-synthesis outputs differ"
    exit 1
fi
echo "PASS"
