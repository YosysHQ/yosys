#!/usr/bin/env bash

exec ../tools/autotest.sh -G -Y ${YOSYS} -j $@ -p 'proc; opt; memory -nomap; techmap -map ../mem_simple_4x1_map.v;; techmap; opt; abc;; stat' mem_simple_4x1_uut.v
