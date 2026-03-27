set -euo pipefail

mkdir -p temp

$YOSYS -p "read_verilog -sv everything.v; write_rtlil temp/roundtrip-design-push.il; design -push; design -pop; write_rtlil temp/roundtrip-design-pop.il"
diff temp/roundtrip-design-push.il temp/roundtrip-design-pop.il

$YOSYS -p "read_verilog -sv everything.v; write_rtlil temp/roundtrip-design-save.il; design -save foo; design -load foo; write_rtlil temp/roundtrip-design-load.il"
diff temp/roundtrip-design-save.il temp/roundtrip-design-load.il
