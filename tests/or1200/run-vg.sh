#!/bin/bash
time valgrind --leak-check=full --show-reachable=yes --log-file=valgrind.log \
		../../yosys -o synth.v -tl synth.log -p "hierarchy -check -top or1200_top" \
		-p opt_const -p proc -p memory -p opt -p techmap -p opt -p abc -p opt rtl/or1200_*.v
