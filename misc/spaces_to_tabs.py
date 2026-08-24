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

    # Only modify files that already use tabs for indentation.
    if not re.search(r"(?m)^\t+", text):
        continue

    def convert(match):
        tabs = match.group(1)
        spaces = match.group(2)
        return tabs + "\t" * (len(spaces) // 4) + spaces[len(spaces) // 4 * 4:]

    new_text = re.sub(
        r"^(\t*)( +)",
        convert,
        text,
        flags=re.MULTILINE,
    )

    if new_text != text:
        path.write_text(new_text)
        changed = True
        print(f"Converted indentation to tabs: {filename}")

sys.exit(1 if changed else 0)
