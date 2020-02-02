#!/bin/bash

mkdir -p temp
cp content1.dat temp/content2.dat

cd ..

echo "Running from the parent directory with content1.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"content1.dat\" memory; synth -top memory"
echo "Running from the parent directory with temp/content2.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"temp/content2.dat\" memory; synth -top memory"
echo "Running from the parent directory with memfile/temp/content2.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"memfile/temp/content2.dat\" memory; synth -top memory"

cd memfile

echo "Running from the same directory with content1.dat"
../../yosys -qp "read_verilog -defer memory.v; chparam -set MEMFILE \"content1.dat\" memory; synth -top memory"
echo "Running from the same directory with temp/content2.dat"
../../yosys -qp "read_verilog -defer memory.v; chparam -set MEMFILE \"temp/content2.dat\" memory; synth -top memory"

cd temp

echo "Running from a child directory with content1.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"content1.dat\" memory; synth -top memory"
echo "Running from a child directory with temp/content2.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"temp/content2.dat\" memory; synth -top memory"
echo "Running from a child directory with content2.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"temp/content2.dat\" memory; synth -top memory"
