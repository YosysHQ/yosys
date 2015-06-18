#!/bin/bash

cat > $1.tpl <<EOT
%module main
  INVARSPEC ! bool(_trigger)
EOT

cat > $1.ys <<EOT
echo on

read_ilang $1.il
hierarchy; proc; opt
rename -top uut
design -save gold

synth
design -stash gate

design -copy-from gold -as gold uut
design -copy-from gate -as gate uut
miter -equiv -flatten gold gate main
hierarchy -top main

dump
write_smv -tpl $1.tpl $1.smv
EOT

set -ex

../../yosys -l $1.log -q $1.ys
NuSMV -bmc $1.smv >> $1.log
grep "^-- invariant .* is true" $1.log

