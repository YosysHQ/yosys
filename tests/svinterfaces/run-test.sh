#/bin/bash -e

./runone.sh  svinterface1
./runone.sh  svinterface_at_top

./run_simple.sh load_and_derive
