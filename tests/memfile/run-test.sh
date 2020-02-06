#!/bin/bash

set -e

mkdir -p temp
cp content1.dat temp/content2.dat

cd ..

echo "Running from the parent directory with content1.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"content1.dat\" memory"
echo "Running from the parent directory with temp/content2.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"temp/content2.dat\" memory"
echo "Running from the parent directory with memfile/temp/content2.dat"
../yosys -qp "read_verilog -defer memfile/memory.v; chparam -set MEMFILE \"memfile/temp/content2.dat\" memory"

cd memfile

echo "Running from the same directory with content1.dat"
../../yosys -qp "read_verilog -defer memory.v; chparam -set MEMFILE \"content1.dat\" memory"
echo "Running from the same directory with temp/content2.dat"
../../yosys -qp "read_verilog -defer memory.v; chparam -set MEMFILE \"temp/content2.dat\" memory"

cd temp

echo "Running from a child directory with content1.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"content1.dat\" memory"
echo "Running from a child directory with temp/content2.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"temp/content2.dat\" memory"
echo "Running from a child directory with content2.dat"
../../../yosys -qp "read_verilog -defer ../memory.v; chparam -set MEMFILE \"temp/content2.dat\" memory"

cd ..

echo "Checking a failure when zero length filename is provided"
if ../../yosys -qp "read_verilog memory.v"; then
	echo "The execution should fail but it didn't happen, which is WRONG."
	exit 1
else
	echo "Execution failed, which is OK."
fi

echo "Checking a failure when not existing filename is provided"
if ../../yosys -qp "read_verilog -defer memory.v; chparam -set MEMFILE \"content3.dat\" memory"; then
	echo "The execution should fail but it didn't happen, which is WRONG."
	exit 1
else
	echo "Execution failed, which is OK."
fi
