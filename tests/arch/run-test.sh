#!/bin/bash

set -e

echo "Running syntax check on arch sim models"
for arch in ../../techlibs/*; do
	find $arch -name cells_sim.v -print0 | xargs -0 -n1 -r iverilog -t null -I$arch
done
