#!/bin/bash

set -ex

rm -rf temp
mkdir -p temp

../../yosys -p 'test_cell -muxdiv -w temp/test all'
rm -f temp/test_{alu,fa,lcu,lut,macc,shiftx}_*

cat > temp/makefile << "EOT"
all: $(addsuffix .ok,$(basename $(wildcard temp/test_*.il)))
%.ok: %.il
	bash run-single.sh $(basename $<)
	touch $@
EOT

${MAKE:-make} -f temp/makefile

