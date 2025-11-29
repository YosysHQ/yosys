import os
import sys

from pyosys import libyosys as ys

print(ys)

ys.log("Hello, world!\n")

from pyosys.libyosys import log

print(log)

log("Goodbye, world!\n")

import pyosys

if os.path.basename(sys.executable) == "yosys":
	# make sure it's not importing the directory
	assert "built-in" in repr(pyosys)
