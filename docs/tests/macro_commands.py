#!/usr/bin/env python3

import logging
from pathlib import Path
import re
import subprocess
import sys

# basic logging setup
logging.basicConfig(level=logging.INFO)

# expects __file__ = yosys/docs/tests/macro_commands.py
TESTS_DIR = Path(__file__).parent.absolute()
ROOT_DIR = TESTS_DIR.parent.parent
logging.log(logging.INFO, f"Using {ROOT_DIR} as root directory")
THIS_FILE = (TESTS_DIR / "macro_commands.py").relative_to(ROOT_DIR)
MACRO_SOURCE = TESTS_DIR.parent / "source" / "code_examples" / "macro_commands"
assert MACRO_SOURCE.exists(), f"can't find macro_commands in {MACRO_SOURCE}"

YOSYS = ROOT_DIR / "yosys"
assert YOSYS.exists(), f"can't find yosys executable in {YOSYS}"

raise_error = False
# get all macro commands being used
for macro in MACRO_SOURCE.glob("*.ys"):
    # log current test
    relative_path = macro.relative_to(ROOT_DIR)
    logging.log(logging.INFO, f"Checking {relative_path}")
    # files in macros_commands should be named {command}.ys
    command = macro.stem
    # run `yosys -h {command}` to capture current sub-commands
    proc = subprocess.run([YOSYS, "-QTh", command], capture_output=True, text=True)
    with open(macro) as f:
        # {command.ys} starts with two commented lines, the first is the text
        # immediately prior to the macro body.  The second is the text
        # immediately after.
        start = f.readline()
        end = f.readline()
        file_content = f.readlines()
    expected_content = []
    for line in file_content:
        line = line.split("#")[0].strip()
        if line:
            expected_content.append(line)
    # parse {command.ys}
    if "#start:" not in start or "#end:" not in end:
        logging.error(f"Missing start and/or end string in {relative_path}, see {THIS_FILE}")
        raise_error = True
        continue
    start = start.replace("#start:", "").strip()
    end = end.replace("#end:", "").strip()
    # attempt to find macro body in help output
    match = re.fullmatch(f".*{start}(.*){end}.*", proc.stdout, re.DOTALL)
    if not match:
        logging.error(f"Couldn't find {start!r} and/or {end!r} in `yosys -h {command}` output")
        raise_error = True
        continue
    match_content = match.group(1).strip().splitlines()
    actual_content = []
    for line in match_content:
        if line:
            actual_content.append(line)
    # iterate over and compare expected v actual
    for (expected, actual) in zip(expected_content, actual_content):
        expected = expected.strip()
        actual = actual.strip()
        # raw match
        if expected == actual:
            continue

        # rip apart formatting to match line parts
        pattern = r"(?P<cmd>\S+)(?P<pass> \[.*\])?(?P<opt>.*?)(?P<cond>\s+\(.*\))?"
        try:
            expected_dict = re.fullmatch(pattern, expected).groupdict()
        except AttributeError:
            logging.error(f"Bad formatting in {relative_path}: {expected!r}")
            raise_error = True
            continue

        try:
            actual_dict = re.fullmatch(pattern, actual).groupdict()
        except AttributeError:
            logging.error(f"Unexpected formatting in `yosys -h {command}` output, {actual!r}")
            raise_error = True
            continue

        does_match = expected_dict["cmd"] == actual_dict["cmd"]

        #todo: check expected_dict["pass"] is a subset of actual_dict["pass"]
        # only check opt and cond match if they're in {command}.ys
        match_keys = ["opt", "cond"]
        for key in match_keys:
            if expected_dict[key] and expected_dict[key] != actual_dict[key]:
                does_match = False

        # raise error on mismatch        
        if not does_match:
            logging.error(f"Expected {expected!r}, got {actual!r}")
            raise_error = True

sys.exit(raise_error)
