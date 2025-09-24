#!/usr/bin/env bash
set -eu

yosys="$PWD/../../yosys"

# these ones are fine because bash handles it
$yosys "file name.ys"
$yosys file\ name.ys

$yosys "file name.v" -o "file name.out" -b verilog
$yosys file\ name.v -o file\ name.out -b verilog

# these already have special handling in Yosys thanks to `extra_args`
$yosys -p 'read_verilog "file name.v"'
$yosys -p 'write_verilog "file name.out"'

# this one isn't a normal frontend so doesn't
# $yosys -p 'script "file name.ys"'

# these get split by space and treated as two separate filenames
# $yosys -p script\ "file name.ys"
# $yosys -p script\ file\ name.ys
# $yosys -p read_verilog\ "file name.v"
# $yosys -p read_verilog\ file\ name.v
# $yosys -p write_verilog\ file\ name.out
# $yosys -p write_verilog\ "file name.out"

# what does test_args say
rm -f plugin.so
CXXFLAGS=$(../../yosys-config --cxxflags)
DATDIR=$(../../yosys-config --datdir)
DATDIR=${DATDIR//\//\\\/}
CXXFLAGS=${CXXFLAGS//$DATDIR/..\/..\/share}
../../yosys-config --exec --cxx ${CXXFLAGS} --ldflags -shared -o plugin.so plugin.cc
yosys_plugin="$yosys -m ./plugin.so"

$yosys_plugin -p test_args\ "quoted spaces"
$yosys_plugin -p test_args\ escaped\ spaces
$yosys_plugin -p test_args\ \"escaped\ quotes\"
$yosys_plugin -p 'test_args "inner quotes"'
$yosys_plugin -p 'test_args "inner \"escaped quotes\""'

$yosys_plugin -p 'read_test_args "file name.v" "file name.ys"'
$yosys_plugin -p 'write_test_args "file name.out"'

# and as a script
$yosys_plugin space_in_name.ys
