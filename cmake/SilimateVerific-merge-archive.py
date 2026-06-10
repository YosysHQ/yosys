# Copyright (c) 2026 Silimate, Inc.
# SPDX-License-Identifier: MIT
"""
Usage: <script> <primary.a> [archive.a [archive.a [archive.a …]]]

Merges a number of .a files such that the symbols of the first archive is
prioritized by extracting and marking all symbols of subsequent archives as
local.
"""
import os
import sys
import shutil
import pathlib
import subprocess

if len(sys.argv) < 2:
	print("Invalid argument count: must have at least one argument.", file=sys.stderr)
	exit(1)

primary = pathlib.Path(sys.argv[1])
files = sys.argv[2:]
cwd = pathlib.Path(".").resolve()

objcopy_bin = shutil.which("objcopy") or shutil.which("llvm-objcopy")
if objcopy_bin is None:
	print("Could not find either objcopy or llvm-objcopy in PATH.", file=sys.stderr)
	exit(1)

prioritized_symbols = set()

object_dir = cwd / "verific-merge" / primary.stem
object_dir.mkdir(parents=True, exist_ok=True)
subprocess.check_call(["ar", "x", primary], cwd=object_dir)
for object in object_dir.glob("*.o"):
	result = subprocess.check_output(["nm", "-gjU", object], encoding="utf8")
	prioritized_symbols.update(filter(lambda x: len(x.strip()), result.splitlines()))

symbol_localize_args = [f"-L{symbol}" for symbol in prioritized_symbols]
final_archive_objects = []
for archive in filter(lambda x: x.endswith(".a"), files):
	file_path = pathlib.Path(archive)
	name = file_path.stem
	object_dir = cwd / "verific-merge" / name
	object_dir.mkdir(parents=True, exist_ok=True)
	subprocess.check_call(["ar", "x", archive], cwd=object_dir)
	for object in object_dir.glob("*.o"):
		if len(symbol_localize_args):
			subprocess.check_call([objcopy_bin, *symbol_localize_args, object])
		final_archive_objects.append(object)

subprocess.check_call(["ar", "rs", primary, *final_archive_objects])
