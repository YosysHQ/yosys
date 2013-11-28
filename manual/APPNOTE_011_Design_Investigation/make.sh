#!/bin/bash
../../yosys example.ys
sed -i '/^label=/ d;' example_*.dot
dot -Tpdf -o example_00.pdf example_00.dot
dot -Tpdf -o example_01.pdf example_01.dot
dot -Tpdf -o example_02.pdf example_02.dot
