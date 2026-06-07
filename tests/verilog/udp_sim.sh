#!/usr/bin/env bash
# Check that Yosys's lowering of Verilog user-defined primitives (UDPs)
# simulates identically to Icarus Verilog's native UDP support, under
# multi-valued (0/1/x/z) logic.  Uses the UDP examples from IEEE 1364-2005
# clause 8.
set -e

if ! command -v iverilog >/dev/null 2>&1; then
    echo "skipping udp_sim.sh: iverilog not found"
    exit 0
fi

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# 8.2 combinational multiplexer
cat > "$WORK/mux.v" <<'EOF'
primitive multiplexer (mux, control, dataA, dataB);
output mux; input control, dataA, dataB;
table
//  c  a  b : mux
    0  1  ? : 1 ;
    0  0  ? : 0 ;
    1  ?  1 : 1 ;
    1  ?  0 : 0 ;
    x  0  0 : 0 ;
    x  1  1 : 1 ;
endtable
endprimitive
EOF

# 8.3 level-sensitive latch
cat > "$WORK/latch.v" <<'EOF'
primitive latch (q, clock, data);
output q; reg q; input clock, data;
table
//  clk data : q : q+
    0   1    : ? : 1 ;
    0   0    : ? : 0 ;
    1   ?    : ? : - ;
endtable
endprimitive
EOF

# 8.4 rising-edge D flip-flop
cat > "$WORK/dff.v" <<'EOF'
primitive d_edge_ff (q, clock, data);
output q; reg q; input clock, data;
table
//  clk  data : q : q+
    (01) 0 : ? : 0 ;
    (01) 1 : ? : 1 ;
    (0?) 1 : 1 : 1 ;
    (0?) 0 : 0 : 0 ;
    (?0) ? : ? : - ;
     ?  (??): ? : - ;
endtable
endprimitive
EOF

# 8.5 D flip-flop with an initial value
cat > "$WORK/dff1.v" <<'EOF'
primitive dff1 (q, clk, d);
input clk, d; output q; reg q;
initial q = 1'b1;
table
    r 0 : ? : 0 ;
    r 1 : ? : 1 ;
    f ? : ? : - ;
    ? * : ? : - ;
endtable
endprimitive
EOF

# 8.5 set/reset flip-flop with an initial value
cat > "$WORK/srff.v" <<'EOF'
primitive srff (q, s, r);
output q; reg q; input s, r;
initial q = 1'b1;
table
    1 0 : ? : 1 ;
    f 0 : 1 : - ;
    0 r : ? : 0 ;
    0 f : 0 : - ;
    1 1 : ? : 0 ;
endtable
endprimitive
EOF

# 8.7 edge-triggered JK flip-flop with level-sensitive preset/clear
cat > "$WORK/jk.v" <<'EOF'
primitive jk_edge_ff (q, clock, j, k, preset, clear);
output q; reg q; input clock, j, k, preset, clear;
table
    ? ?? 01 : ? : 1 ;
    ? ?? *1 : 1 : 1 ;
    ? ?? 10 : ? : 0 ;
    ? ?? 1* : 0 : 0 ;
    r 00 00 : 0 : 1 ;
    r 00 11 : ? : - ;
    r 01 11 : ? : 0 ;
    r 10 11 : ? : 1 ;
    r 11 11 : 0 : 1 ;
    r 11 11 : 1 : 0 ;
    f ?? ?? : ? : - ;
    b *? ?? : ? : - ;
    b ?* ?? : ? : - ;
endtable
endprimitive
EOF

cat > "$WORK/dff_complex.v" <<'EOF'
primitive dff_complex (q, v, clk, d, xcr);
output q; reg q; input v, clk, d, xcr;
table
    *  ?   ? ? : ? : x;
    ? (x1) 0 0 : ? : 0;
    ? (x1) 1 0 : ? : 1;
    ? (x1) 0 1 : 0 : 0;
    ? (x1) 1 1 : 1 : 1;
    ? (x1) ? x : ? : -;
    ? (bx) 0 ? : 0 : -;
    ? (bx) 1 ? : 1 : -;
    ? (x0) b ? : ? : -;
    ? (x0) ? x : ? : -;
    ? (01) 0 ? : ? : 0;
    ? (01) 1 ? : ? : 1;
    ? (10) ? ? : ? : -;
    ?  b   * ? : ? : -;
    ?  ?   ? * : ? : -;
endtable
endprimitive
EOF

for u in mux latch dff dff1 srff jk dff_complex; do
    python3 "$(dirname "$0")/udp_cosim.py" "$WORK/$u.v" 20 60
done
