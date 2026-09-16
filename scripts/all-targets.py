#!/usr/bin/env python3
"""Print every buildable target declared in `lakefile.toml`, one per line.

`lake build` with no argument builds only `defaultTargets`, which on this
branch is `Core`.  That leaves every other declared library and executable
unbuilt, so a break in one of them passes CI unnoticed — a syntax error can
survive a "successful" build and surface only when the module is named.
CI therefore builds what this script enumerates, rather than trusting the
default target to stand for the repository.
"""

import re
import sys
from pathlib import Path

LAKEFILE = Path(__file__).resolve().parent.parent / "lakefile.toml"

BLOCK = re.compile(r"\[\[lean_(lib|exe)\]\]\n((?:[^\[\n][^\n]*\n|\n)*)")
NAME = re.compile(r'name\s*=\s*"([^"]+)"')


def main() -> int:
    if not LAKEFILE.is_file():
        print("all-targets: lakefile.toml not found", file=sys.stderr)
        return 2
    # Read BYTES and decode leniently: `read_text` raises on invalid UTF-8,
    # and a gate script that dies on its input has not checked it either.
    text = LAKEFILE.read_bytes().decode("utf-8", errors="replace")
    names = [m.group(1) for b in BLOCK.finditer(text)
             for m in [NAME.search(b.group(2))] if m]
    if not names:
        print("all-targets: no targets parsed — has the lakefile format changed?",
              file=sys.stderr)
        return 2
    print("\n".join(names))
    return 0


if __name__ == "__main__":
    sys.exit(main())
