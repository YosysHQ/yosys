
include generate.lst

test: $(TARGETS)

vivado: $(addprefix check_vivado/,$(notdir $(TARGETS)))

check/%.log: rtl/%.v xst/%.v
	bash run-check.sh $(notdir $(basename $<))

check_vivado/%.log: rtl/%.v vivado/%.v
	bash run-check.sh -vivado $(notdir $(basename $<))

xst/%.v: rtl/%.v
	bash run-xst.sh $(notdir $(basename $<))

vivado/%.v: rtl/%.v
	bash run-vivado.sh $(notdir $(basename $<))

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

backup:
	mkdir -p ~/.yosys/xhammer
	tar cvzf ~/.yosys/xhammer/xst_files.tar.gz xst
	tar cvzf ~/.yosys/xhammer/vivado_files.tar.gz vivado

restore:
	tar xvzf ~/.yosys/xhammer/xst_files.tar.gz
	tar xvzf ~/.yosys/xhammer/vivado_files.tar.gz

.PHONY: test vivado check_xl_cells clean mrproper backup restore
.PRECIOUS: check/%.log xst/%.v vivado/%.v rtl/%.v generate.lst

