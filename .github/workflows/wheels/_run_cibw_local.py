#!/usr/bin/env python3
# Copyright (C) 2024 Efabless Corporation
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
"""
This runs the cibuildwheel step from the wheels workflow locally.
"""

import os
import sys
import yaml
import platform
import subprocess
from pathlib import Path

__yosys_root__ = Path(__file__).absolute().parents[3]

platform_string = platform.system()
if platform_string not in ["Linux", "Darwin"]:
	print(f"Unsupported system {platform_string}.", file=sys.stderr)
	exit(1)

excluded_env_suffixes = {
	"Linux": ["MAC", "WIN"],
	"Windows": ["LINUX", "MAC"],
	"Darwin": ["WIN", "LINUX"],
}[platform_string]

required_downloads = ["ffi"]
if platform_string == "Linux":
	required_downloads += ["bison"]

for source in required_downloads:
	if not (__yosys_root__ / source).is_dir():
		print(
			f"You need to download {{{', '.join(required_downloads)}}} in a similar manner to wheels.yml first."
		)
		exit(-1)

with open(__yosys_root__ / ".github" / "workflows" / "wheels.yml") as f:
	workflow = yaml.safe_load(f)

env = os.environ.copy()

steps = workflow["jobs"]["build_wheels"]["steps"]
cibw_step = None
for step in steps:
	if (step.get("uses") or "").startswith("pypa/cibuildwheel"):
		cibw_step = step
		break



for key, value in cibw_step["env"].items():
	if any(key.endswith(tag) for tag in excluded_env_suffixes):
		continue
	env[key] = value

if platform_string == "Darwin":
	# can only build versions installed in /Library/Frameworks/PythonT?.framework/Versions
	abi_tags = ""
	executables = Path("/Library/Frameworks").glob("Python*.framework/Versions/*/bin/python3.*")
	for exec in executables:
		ver = exec.parents[1].name
		if ver == "Current":
			continue # duplicate
		if not exec.name.endswith(ver):
			continue # duplicates, -config, …
		abi_tags += subprocess.check_output([
			exec,
			"-c",
			"import sysconfig; print('cp' + sysconfig.get_config_var('py_version_nodot') + sysconfig.get_config_var('abiflags') + '-*', end=' ')"
		], encoding="utf8")
	env["CIBW_BUILD"] = abi_tags

	# convenience
	for dir in [
		"/opt/homebrew/opt/flex/bin",
		"/opt/homebrew/opt/bison/bin",
	]:
		if os.path.exists(dir):
			env["PATH"] = dir + ":" + env["PATH"]

env["CIBW_ARCHS"] = os.getenv("CIBW_ARCHS", platform.machine())
subprocess.check_call(["cibuildwheel"], env=env)
