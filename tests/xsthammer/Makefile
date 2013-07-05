
include generate.lst

test: $(TARGETS)

vivado: $(addprefix check_vivado/,$(notdir $(TARGETS)))

quartus: $(addprefix check_quartus/,$(notdir $(TARGETS)))

report:
	ls check check_quartus/ check_vivado | grep '\.err$$' | sort -u | cut -f1 -d. | gawk '{ print "report/" $$0 ".html"; }' | xargs -r $(MAKE)

report/%.html:
	bash report.sh $(notdir $(basename $@))

check/%.log: rtl/%.v xst/%.v
	bash run-check.sh $(notdir $(basename $<))

check_vivado/%.log: rtl/%.v vivado/%.v
	bash run-check.sh -vivado $(notdir $(basename $<))

check_quartus/%.log: rtl/%.v quartus/%.v
	bash run-check.sh -quartus $(notdir $(basename $<))

xst/%.v: rtl/%.v
	bash run-xst.sh $(notdir $(basename $<))

vivado/%.v: rtl/%.v
	bash run-vivado.sh $(notdir $(basename $<))

quartus/%.v: rtl/%.v
	bash run-quartus.sh $(notdir $(basename $<))

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
	tar cvzf ~/.yosys/xhammer/quartus_files.tar.gz quartus

restore:
	tar xvzf ~/.yosys/xhammer/xst_files.tar.gz
	tar xvzf ~/.yosys/xhammer/vivado_files.tar.gz
	tar xvzf ~/.yosys/xhammer/quartus_files.tar.gz

.PHONY: test vivado quartus report check_xl_cells clean mrproper backup restore
.PRECIOUS: check/%.log xst/%.v vivado/%.v quartus/%.v rtl/%.v generate.lst

