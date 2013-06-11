
include generate.lst

test: $(TARGETS)

check/%.log: rtl/%.v xst/%.v
	bash run-check.sh $(notdir $(basename $<))

xst/%.v: rtl/%.v
	bash run-xst.sh $(notdir $(basename $<))

generate.lst: generate.cc
	clang -Wall -o generate generate.cc -lstdc++
	./generate
	{ echo -n "TARGETS := "; ls rtl/ | sed 's,\.v$$,.log,; s,^,check/,;' | tr '\n' ' '; } > generate.lst

check_xl_cells:
	../../yosys xl_cells_tb.ys

clean:
	rm -rf generate generate.lst check_temp xst_temp

mrproper: clean
	rm -rf rtl xst check

.PHONY: test check_xl_cells clean mrproper
.PRECIOUS: check/%.log xst/%.v rtl/%.v generate.lst

