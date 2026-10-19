#!/usr/bin/env bash

set -euo pipefail
cd "$(dirname "$0")/src"
sby --yosys "${YOSYS}" -f bus_dmem_ch0.sby
