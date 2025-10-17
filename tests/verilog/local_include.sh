#!/usr/bin/env bash

set -eu

# only works with read_verilog
yosys='../../yosys -f verilog'
test='-p hierarchy'
subdir=subdir
source=local_include.v
include=temp_foo.v

# no include file should fail
rm -f $include
echo "logger -expect error $include 1; read_verilog $source" | $yosys

# both files local
echo 'module foo (input a, output b); assign b = a; endmodule' > $include
$yosys $test $source

# include local to cwd
mkdir -p $subdir
cp -t $subdir $source
$yosys $test $subdir/$source

# include local to source
mv -t $subdir $include
$yosys $test $subdir/$source

# include local to source, and source is given as an absolute path
$yosys $test $(pwd)/$subdir/$source
