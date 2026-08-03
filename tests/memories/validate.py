#!/usr/bin/env python3
import re
import sys
from pathlib import Path

CHECKS = [
    (
        "expect-wr-ports",
        r"parameter \\WR_PORTS {val}$",
        "ERROR: Unexpected number of write ports.",
    ),
    (
        "expect-wr-wide-continuation",
        r"parameter \\WR_WIDE_CONTINUATION {val}$",
        "ERROR: Unexpected write wide continuation.",
    ),
    (
        "expect-rd-ports",
        r"parameter \\RD_PORTS {val}$",
        "ERROR: Unexpected number of read ports.",
    ),
    (
        "expect-rd-clk",
        r"connect \\RD_CLK {val}$",
        "ERROR: Unexpected read clock.",
    ),
    (
        "expect-rd-en",
        r"connect \\RD_EN {val}$",
        "ERROR: Unexpected read enable.",
    ),
    (
        "expect-rd-srst-sig",
        r"connect \\RD_SRST {val}$",
        "ERROR: Unexpected read sync reset.",
    ),
    (
        "expect-rd-srst-val",
        r"parameter \\RD_SRST_VALUE {val}$",
        "ERROR: Unexpected read sync reset value.",
    ),
    (
        "expect-rd-arst-sig",
        r"connect \\RD_ARST {val}$",
        "ERROR: Unexpected read async reset.",
    ),
    (
        "expect-rd-arst-val",
        r"parameter \\RD_ARST_VALUE {val}$",
        "ERROR: Unexpected read async reset value.",
    ),
    (
        "expect-rd-init-val",
        r"parameter \\RD_INIT_VALUE {val}$",
        "ERROR: Unexpected read init value.",
    ),
    (
        "expect-rd-wide-continuation",
        r"parameter \\RD_WIDE_CONTINUATION {val}$",
        "ERROR: Unexpected read wide continuation.",
    ),
    (
        "expect-no-rd-clk",
        r"connect \\RD_CLK 1'x$",
        "ERROR: Expected no read clock.",
    ),
]


def extract_expect_value(src_text: str, key: str):
    pattern = rf"{re.escape(key)}\s+(\S+)"
    m = re.search(pattern, src_text)
    return m.group(1) if m else None


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <source.v> <dump.dmp>", file=sys.stderr)
        return 2

    srcfile = Path(sys.argv[1])
    dmpfile = Path(sys.argv[2])

    try:
        src_text = srcfile.read_text()
    except Exception as e:
        print(f"ERROR: Failed to read {srcfile}: {e}", file=sys.stderr)
        return 2

    try:
        dmp_text = dmpfile.read_text()
    except Exception as e:
        print(f"ERROR: Failed to read {dmpfile}: {e}", file=sys.stderr)
        return 2

    for key, pattern_template, errmsg in CHECKS:
        if "{val}" in pattern_template:
            val = extract_expect_value(src_text, key)
            if val is None:
                continue
            pattern = pattern_template.format(val=re.escape(val))
        else:
            if key not in src_text:
                continue
            pattern = pattern_template

        if not re.search(pattern, dmp_text, re.MULTILINE):
            print(errmsg, file=sys.stderr)
            return 1

    print("ok.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
