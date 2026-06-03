"""Extracts a list of requirements from a `ScriptPass` command.

Not entirely accurate, but very easy to implement. Should probably be replaced with an implementation
in the kernel that performs the same extraction in a principled way.
"""

import re
import sys
import subprocess

for name in sys.argv[1:]:
	output = subprocess.check_output(["./yosys", "-QT", "-p", f"help {name}"], encoding="ascii")
	header = False
	passes = []
	for line in output.splitlines():
		if line == "The following commands are executed by this synthesis command:":
			header = True
			continue
		if header:
			if m := re.match(r"^        \s*(\w+)", line):
				passes.append(m[1])
	if not header:
		print(output)
		sys.exit(1)
	print()
	print(f"===> {name}")
	for p in sorted(set(passes)):
		print(f"\t\t{p}")
	print()
