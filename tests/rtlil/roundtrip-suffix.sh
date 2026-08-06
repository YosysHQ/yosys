set -euo pipefail

mkdir -p temp

${YOSYS} -p "read_rtlil suffix-twines.il; write_rtlil temp/suffix-twines-write.il"
tail -n +2 temp/suffix-twines-write.il > temp/suffix-twines-write-nogen.il
diff suffix-twines.il temp/suffix-twines-write-nogen.il

${YOSYS} -p "read_rtlil suffix-twines.il; design -push; design -pop; write_rtlil temp/suffix-twines-push.il"
tail -n +2 temp/suffix-twines-push.il > temp/suffix-twines-push-nogen.il
diff suffix-twines.il temp/suffix-twines-push-nogen.il

${YOSYS} -p "read_rtlil suffix-chain.il; design -push; design -pop; write_rtlil temp/suffix-chain-push.il"
tail -n +2 temp/suffix-chain-push.il > temp/suffix-chain-push-nogen.il
diff suffix-chain.il temp/suffix-chain-push-nogen.il

${YOSYS} -p "read_rtlil suffix-chain.il; opt_clean; write_rtlil -readable temp/suffix-chain-gc-resolved.il"
grep 'wire' temp/suffix-chain-gc-resolved.il | sort > temp/suffix-chain-gc-resolved.names
cat > temp/suffix-chain-expected.names <<EOF
  wire input 1 \\home.repo.chain.in
  wire output 2 \\home.repo.chain.out
EOF
diff temp/suffix-chain-expected.names temp/suffix-chain-gc-resolved.names
