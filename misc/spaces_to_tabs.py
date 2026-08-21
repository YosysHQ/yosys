#!/usr/bin/env python3

import re
import sys
from pathlib import Path

changed = False

for filename in sys.argv[1:]:
    path = Path(filename)

    try:
        text = path.read_text()
    except UnicodeDecodeError:
        continue

    # Determine whether this file uses tabs for indentation.
    uses_tabs = any(
        re.match(r"^\t+", line)
        for line in text.splitlines()
    )

    if not uses_tabs:
        continue

    new_text = re.sub(
        r"^(?: {4})+",
        lambda m: "\t" * (len(m.group()) // 4),
        text,
        flags=re.MULTILINE,
    )

    if new_text != text:
        path.write_text(new_text)
        changed = True
        print(f"Converted indentation to tabs: {filename}")

sys.exit(1 if changed else 0)
