#!/bin/bash

if [ $# -eq 0 ]; then
	echo "Usage: $0 <job_id>" >&2
	exit 1
fi

job="$1"
set --

set -e
mkdir -p quartus quartus_temp/$job
cd quartus_temp/$job

rm -rf *
cp ../../rtl/$job.v .
/opt/altera/13.0/quartus/bin/quartus_map $job --source=$job.v --family="Cyclone III" 
/opt/altera/13.0/quartus/bin/quartus_fit $job
/opt/altera/13.0/quartus/bin/quartus_eda $job --formal_verification --tool=conformal
cp -v fv/conformal/$job.vo ../../quartus/$job.v

sync
exit 0

