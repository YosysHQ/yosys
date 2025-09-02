set -euo pipefail
YS=../../yosys

$YS -p "read_verilog -sv everything.v; write_rtlil roundtrip-design-push.tmp.il; design -push; design -pop; write_rtlil roundtrip-design-pop.tmp.il"
diff roundtrip-design-push.tmp.il roundtrip-design-pop.tmp.il

$YS -p "read_verilog -sv everything.v; write_rtlil roundtrip-design-save.tmp.il; design -save foo; design -load foo; write_rtlil roundtrip-design-load.tmp.il"
diff roundtrip-design-save.tmp.il roundtrip-design-load.tmp.il
