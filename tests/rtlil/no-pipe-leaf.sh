set -euo pipefail

mkdir -p temp

check_no_pipe_leaf() {
    if grep -E '^[[:space:]]*leaf [0-9]+ ' "$1" | grep -q '|'; then
        echo "FAIL: $1 has a leaf containing '|':" >&2
        grep -E '^[[:space:]]*leaf [0-9]+ ' "$1" | grep '|' >&2
        exit 1
    fi
}

cat > temp/pipe.v <<'EOF'
module top(input clk, input [7:0] a, b, c, d, output reg [7:0] x, y);
  always @(posedge clk) begin
    x <= a + b;
    y <= c + d;
  end
endmodule
EOF

${YOSYS} -p "read_verilog temp/pipe.v; hierarchy -top top; proc; opt; opt_merge -share_all; alumacc; opt_dff; write_rtlil temp/pipe-dump.il"
check_no_pipe_leaf temp/pipe-dump.il

cat > temp/mem.v <<'EOF'
module mem(input clk, input we, input [3:0] addr, input [7:0] din, output reg [7:0] dout);
  reg [7:0] m [0:15];
  always @(posedge clk) begin
    if (we) m[addr] <= din;
    dout <= m[addr];
  end
endmodule
EOF

${YOSYS} -p "read_verilog temp/mem.v; hierarchy -top mem; proc; opt; memory_map; opt_dff; write_rtlil temp/mem-dump.il"
check_no_pipe_leaf temp/mem-dump.il
