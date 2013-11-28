#!/bin/bash
../../yosys example.ys
../../yosys -p 'proc; opt; show -format dot -prefix splice' splice.v
sed -i '/^label=/ d;' example_*.dot splice.dot
dot -Tpdf -o example_00.pdf example_00.dot
dot -Tpdf -o example_01.pdf example_01.dot
dot -Tpdf -o example_02.pdf example_02.dot
dot -Tpdf -o splice.pdf splice.dot
