#!/usr/bin/env bash

cd "$(dirname "$0")/src"
sby --yosys "${YOSYS}" -f bmc_bus_dmem_ch0.sby
sby --yosys "${YOSYS}" -f cover_bus_dmem_ch0.sby
