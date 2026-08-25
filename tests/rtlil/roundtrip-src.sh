set -euo pipefail

mkdir -p temp

${YOSYS} -p "read_rtlil src-twines.il; write_rtlil temp/src-twines-write.il"
tail -n +2 temp/src-twines-write.il > temp/src-twines-write-nogen.il
diff src-twines.il temp/src-twines-write-nogen.il

${YOSYS} -p "read_rtlil src-twines.il; design -push; design -pop; write_rtlil temp/src-twines-push.il"
tail -n +2 temp/src-twines-push.il > temp/src-twines-push-nogen.il
diff src-twines.il temp/src-twines-push-nogen.il

${YOSYS} -p "read_rtlil src-twines.il; write_rtlil -readable temp/src-twines-resolved.il"
grep '\\src' temp/src-twines-resolved.il | LC_ALL=C sort > temp/src-twines-resolved.srcs
cat > temp/src-twines-expected.srcs <<EOT
  attribute \\src "everything.v:1.1-1.10"
  attribute \\src "everything.v:2.5-2.8"
attribute \\src "everything.v:1.1-1.10|everything.v:2.5-2.8"
EOT
diff temp/src-twines-expected.srcs temp/src-twines-resolved.srcs
