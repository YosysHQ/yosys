#!/usr/bin/env python3

import sys
sys.path.append("../..")

import gen_tests_makefile
from construct_abc_script import ABCScriptCreator

# librelane defaults, see librelane/steps/pyosys.py
config = {
    "CLOCK_PERIOD": 10,
    "SYNTH_ABC_LEGACY_REFACTOR": False,
    "SYNTH_ABC_LEGACY_REWRITE": False,
    "SYNTH_ABC_USE_MFS3": False,
    "SYNTH_ABC_AREA_USE_NF": False,
    "SYNTH_ABC_BUFFERING": False,
    "SYNTH_SIZING": False,
    "MAX_FANOUT_CONSTRAINT": 10,
    "MAX_TRANSITION_CONSTRAINT": None,
}

creator = ABCScriptCreator(config)
template = open("abc_librelane.ys.in").read()
for strategy in ["AREA 0", "AREA 1", "AREA 2", "AREA 3", "DELAY 0", "DELAY 1", "DELAY 2", "DELAY 3", "DELAY 4"]:
    script = creator.generate_abc_script(".", strategy)
    name = strategy.replace(" ", "_").lower()
    with open(f"abc_librelane_{name}.ys", "w") as f:
        f.write(template.replace("@STRATEGY@", strategy).replace("@SCRIPT@", script))

gen_tests_makefile.generate(["--yosys-scripts"])
