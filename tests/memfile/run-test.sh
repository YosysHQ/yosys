#!/bin/bash

echo "* Creating Memory Content Files"

for i in {1..64}
do
	echo "00001111000000001111111100000000" >> tempfile1.dat
done

mkdir -p temp
cp tempfile1.dat temp/tempfile2.dat

cd ..

echo "* Running from the parent directory"
echo "  * Memory Content File: tempfile1.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"tempfile1.dat\" memory; synth -top memory"
echo "  * Memory Content File: temp/tempfile2.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"temp/tempfile2.dat\" memory; synth -top memory"

cd memfile

echo "* Running from the same directory"
echo "  * Memory Content File: tempfile1.dat"
../../yosys -qp "read_verilog -defer memory.v; chparam -set MEMFILE \"tempfile1.dat\" memory; synth -top memory"
echo "  * Memory Content File: temp/tempfile2.dat"
../../yosys -qp "read_verilog -defer memory.v; chparam -set MEMFILE \"temp/tempfile2.dat\" memory; synth -top memory"

cd temp

echo "* Running from a child directory"
echo "  * Memory Content File: tempfile1.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"tempfile1.dat\" memory; synth -top memory"
echo "  * Memory Content File: temp/tempfile2.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"temp/tempfile2.dat\" memory; synth -top memory"
echo "  * Memory Content File: tempfile2.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"temp/tempfile2.dat\" memory; synth -top memory"

echo "* Done"
