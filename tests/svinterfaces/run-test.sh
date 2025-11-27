#/bin/bash -e
source ../common-env.sh

./runone.sh  svinterface1
./runone.sh  svinterface_at_top

./run_simple.sh load_and_derive
./run_simple.sh resolve_types
./run_simple.sh positional_args
