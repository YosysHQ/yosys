trap 'echo "ERROR in const_cmdline_nested.sh" >&2; exit 1' ERR

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cat > "$tmp/design.v" <<'EOT'
module top(output [7:0] o);
assign o = 8'hAA;
endmodule
EOT

printf "setattr -set foo 2'd7 t:*\n" > "$tmp/inner.ys"
cat > "$tmp/outer.ys" <<EOT
read_verilog $tmp/design.v
prep -top top
script $tmp/inner.ys
setattr -set bar 3'd15 t:*
EOT

# nesting + revert
out=$(${YOSYS} -q "$tmp/outer.ys" 2>&1)
echo "$out" | grep -E "inner\.ys:1: Warning: While parsing constant \`2'd7'" > /dev/null
echo "$out" | grep -E "outer\.ys:[0-9]+: Warning: While parsing constant \`3'd15'" > /dev/null

# cmd fallback - no source location prefix
out=$(${YOSYS} -q -p "read_verilog $tmp/design.v; prep -top top; setattr -set foo 2'd7 t:*" 2>&1)
echo "$out" | grep -E "^Warning: While parsing constant \`2'd7'" > /dev/null
