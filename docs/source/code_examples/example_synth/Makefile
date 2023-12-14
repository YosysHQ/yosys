PROGRAM_PREFIX :=

YOSYS ?= ../../../../$(PROGRAM_PREFIX)yosys

DOTS = control_hier.dot control_proc.dot
DOTS += example_hier.dot

dots: $(DOTS) example.out

$(DOTS) example.out: example.v example.ys
	$(YOSYS) example.ys -l example.out -Q

.PHONY: clean
clean:
	rm -f *.dot
