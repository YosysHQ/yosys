set -euo pipefail

mkdir -p temp

# Read a hand-crafted RTLIL file with Suffix twine nodes, write it back,
# and verify byte-for-byte roundtrip — exercises the Suffix parser path,
# the Suffix backend emitter, and Design::clone_into across design -push
# (which must preserve Suffix tree topology verbatim).
${YOSYS} -p "read_rtlil suffix-twines.il; write_rtlil temp/suffix-twines-write.il"
tail -n +2 temp/suffix-twines-write.il > temp/suffix-twines-write-nogen.il
diff suffix-twines.il temp/suffix-twines-write-nogen.il

${YOSYS} -p "read_rtlil suffix-twines.il; design -push; design -pop; write_rtlil temp/suffix-twines-push.il"
tail -n +2 temp/suffix-twines-push.il > temp/suffix-twines-push-nogen.il
diff suffix-twines.il temp/suffix-twines-push-nogen.il

# Multi-level Suffix chain — verifies that Suffix-with-Suffix-parent
# survives read/write and a design -push/-pop verbatim cycle.
${YOSYS} -p "read_rtlil suffix-chain.il; design -push; design -pop; write_rtlil temp/suffix-chain-push.il"
tail -n +2 temp/suffix-chain-push.il > temp/suffix-chain-push-nogen.il
diff suffix-chain.il temp/suffix-chain-push-nogen.il

# Verify that gc preserves the Suffix tree (number of nodes and the
# materialized leaf strings on each cell src), even if the rebuilt pool
# is renumbered by hash-set iteration order.
${YOSYS} -p "read_rtlil suffix-chain.il; gc_twines; write_rtlil -resolve-src temp/suffix-chain-gc-resolved.il"
grep '\\src' temp/suffix-chain-gc-resolved.il | sort > temp/suffix-chain-gc-resolved.srcs
cat > temp/suffix-chain-expected.srcs <<EOF
  attribute \\src "/home/emil/repo/foo/bar.v:10.1-10.5"
  attribute \\src "/home/emil/repo/foo/bar.v:11.1-11.5"
EOF
diff temp/suffix-chain-expected.srcs temp/suffix-chain-gc-resolved.srcs
