set -euo pipefail

mkdir -p temp

# Synthesize a tiny design through paths that previously round-tripped
# src through get_src_attribute() → set_src_attribute() and broke the
# flat-leaf invariant: opt_merge -share_all produces a Concat src on the
# surviving cell, then opt_dff / FfData emit re-emits the cell. Before
# the adopt_src_from refactor every pipe-joined flatten was re-interned
# as a single pipe-containing Leaf — now those paths transfer the id
# verbatim and no Leaf ever contains '|'.
cat > temp/pipe.v <<'EOF'
module top(input clk, input [7:0] a, b, c, d, output reg [7:0] x, y);
  always @(posedge clk) begin
    x <= a + b;
    y <= c + d;
  end
endmodule
EOF

${YOSYS} -p "read_verilog temp/pipe.v; hierarchy -top top; proc; opt; opt_merge -share_all; alumacc; opt_dff; dump_twines" \
    > temp/pipe-dump.txt 2>&1

if grep -E '^\s*@[0-9]+ leaf rc=[0-9]+ ' temp/pipe-dump.txt | grep -q '|'; then
    echo "FAIL: dump_twines produced a leaf containing '|':" >&2
    grep -E '^\s*@[0-9]+ leaf rc=[0-9]+ ' temp/pipe-dump.txt | grep '|' >&2
    exit 1
fi

# A second pattern that exercises the memory-mapping code path
# (Mem::extract_rdff stash + FfData::emit).
cat > temp/mem.v <<'EOF'
module mem(input clk, input we, input [3:0] addr, input [7:0] din, output reg [7:0] dout);
  reg [7:0] m [0:15];
  always @(posedge clk) begin
    if (we) m[addr] <= din;
    dout <= m[addr];
  end
endmodule
EOF

${YOSYS} -p "read_verilog temp/mem.v; hierarchy -top mem; proc; opt; memory_map; opt_dff; dump_twines" \
    > temp/mem-dump.txt 2>&1

if grep -E '^\s*@[0-9]+ leaf rc=[0-9]+ ' temp/mem-dump.txt | grep -q '|'; then
    echo "FAIL: dump_twines (memory_map path) produced a leaf containing '|':" >&2
    grep -E '^\s*@[0-9]+ leaf rc=[0-9]+ ' temp/mem-dump.txt | grep '|' >&2
    exit 1
fi
