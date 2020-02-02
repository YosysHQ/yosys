#!/bin/bash

for i in {1..64}; do
	echo "00001111000000001111111100000000" >> tempfile1.dat
done

mkdir -p temp
cp tempfile1.dat temp/tempfile2.dat

cd ..

echo "Running from the parent directory with tempfile1.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"tempfile1.dat\" memory; synth -top memory"
echo "Running from the parent directory with temp/tempfile2.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"temp/tempfile2.dat\" memory; synth -top memory"
echo "Running from the parent directory with memfile/temp/tempfile2.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"memfile/temp/tempfile2.dat\" memory; synth -top memory"

cd memfile

echo "Running from the same directory with tempfile1.dat"
../../yosys -qp "read_verilog -defer memory.v; chparam -set MEMFILE \"tempfile1.dat\" memory; synth -top memory"
echo "Running from the same directory with temp/tempfile2.dat"
../../yosys -qp "read_verilog -defer memory.v; chparam -set MEMFILE \"temp/tempfile2.dat\" memory; synth -top memory"

cd temp

echo "Running from a child directory with tempfile1.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"tempfile1.dat\" memory; synth -top memory"
echo "Running from a child directory with temp/tempfile2.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"temp/tempfile2.dat\" memory; synth -top memory"
echo "Running from a child directory with tempfile2.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"temp/tempfile2.dat\" memory; synth -top memory"
