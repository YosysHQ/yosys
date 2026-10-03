#!/usr/bin/env python3
# Copyright (C) 2024 UmbraLogic Technologies LLC
# SPDX-License-Identifier: MIT
"""
This runs the cibuildwheel step from the wheels workflow locally.
"""

import os
import sys
import platform
import subprocess
from pathlib import Path

import yaml
from packaging.tags import sys_tags

__yosys_root__ = Path(__file__).absolute().parents[3]

with open(__yosys_root__ / ".github" / "workflows" / "wheels.yml") as f:
	workflow = yaml.safe_load(f)

env = os.environ.copy()

steps = workflow["jobs"]["build_wheels"]["steps"]
cibw_step = None
for step in steps:
	if (step.get("uses") or "").startswith("pypa/cibuildwheel"):
		cibw_step = step
		break

env_filter = {
	"linux": ("_WINDOWS", "_MAC"),
	"darwin": ("_LINUX", "_WINDOWS"),
	"win32": ("_LINUX", "_MAC"),
}[sys.platform]
for key, value in cibw_step["env"].items():
	if key.endswith(env_filter):
		continue
	if key not in env:  # prioritize user-set keys
		env[key] = value

python_tag = next(sys_tags()).interpreter
env["CIBW_BUILD"] = os.getenv("CIBW_BUILD", f"{python_tag}-*")
env["CIBW_ARCHS"] = os.getenv("CIBW_ARCHS", platform.machine())
subprocess.check_call(["cibuildwheel"], env=env)
