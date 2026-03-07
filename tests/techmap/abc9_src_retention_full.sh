#!/bin/bash
# Full validation test for \src retention through ABC9 synthesis
# via the XAIGER "y" extension equivalence mapping.
#
# Tests both a simple design and an Amaranth-style design, validating
# that \src attributes are present on LUT cells, have valid format,
# and trace back to the original source files.
#
# Note: \src preservation via "y" extension only works for combinational
# designs (&verify -y is CEC-only, not sequential).

set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
YOSYS=${YOSYS:-${SCRIPT_DIR}/../../yosys}

TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

run_test() {
    local name="$1"
    local verilog_file="$2"
    local expect_source="${3:-}"

    echo "=== Testing \\src retention: $name ==="

    $YOSYS -ql "$TMPDIR/${name}.log" -p "
read_verilog $verilog_file
simplemap
scratchpad -set abc9.verify true
abc9 -lut 4
write_json $TMPDIR/${name}.json
"

    python3 "$SCRIPT_DIR/scripts/validate_src_retention.py" \
        "$TMPDIR/${name}.json" \
        --cell-type '$lut' \
        ${expect_source:+--expect-source "$expect_source"}

    echo ""
}

# Test 1: Simple combinational design
cat > "$TMPDIR/simple.v" <<'EOF'
module test(input wire a, input wire b, input wire c, output wire o);
    wire w;
    assign w = a & b;
    assign o = w | c;
endmodule
EOF

run_test "simple" "$TMPDIR/simple.v"

# Test 2: Amaranth-style design with Python source references
cat > "$TMPDIR/amaranth.v" <<'EOF'
(* \generator = "Amaranth" *)
(* src = "led_blinker.py:8.1-42.0" *)
module top(
    (* src = "led_blinker.py:10.5-10.30" *)
    input wire [3:0] i_data,
    (* src = "led_blinker.py:11.5-11.30" *)
    input wire [3:0] i_mask,
    (* src = "led_blinker.py:12.5-12.30" *)
    input wire i_mode,
    (* src = "led_blinker.py:13.5-13.30" *)
    output wire [3:0] o_result,
    (* src = "led_blinker.py:14.5-14.30" *)
    output wire o_any
);
    (* src = "led_blinker.py:18.5-18.40" *)
    wire [3:0] masked;
    (* src = "led_blinker.py:19.5-19.40" *)
    wire [3:0] inverted;
    (* src = "led_blinker.py:20.5-20.40" *)
    wire [3:0] selected;

    assign masked = i_data & i_mask;
    assign inverted = i_data ^ i_mask;
    assign selected = i_mode ? inverted : masked;
    assign o_result = selected;
    assign o_any = |selected;
endmodule
EOF

# Note: \src on cells comes from the Verilog source location of the assign
# statements, not from (* src *) attributes on wires. So we check for the
# temp .v file, not the Python source. The wire-level (* src *) attributes
# from Amaranth are preserved separately on wires, not cells.
run_test "amaranth" "$TMPDIR/amaranth.v"

# Test 3: Larger design (8-bit adder with mux)
cat > "$TMPDIR/large.v" <<'EOF'
module adder_mux(
    input wire [7:0] a,
    input wire [7:0] b,
    input wire [7:0] c,
    input wire sel,
    output wire [8:0] sum,
    output wire zero
);
    wire [8:0] ab_sum;
    wire [8:0] ac_sum;
    assign ab_sum = a + b;
    assign ac_sum = a + c;
    assign sum = sel ? ac_sum : ab_sum;
    assign zero = (sum == 9'd0);
endmodule
EOF

run_test "large" "$TMPDIR/large.v"

echo "=== All tests passed ==="
