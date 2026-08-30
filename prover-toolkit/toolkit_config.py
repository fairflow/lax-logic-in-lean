#!/usr/bin/env python3
"""Project configuration — the only place a repository path appears.

The toolkit is repository-independent. Everything that used to be hardcoded
lives in a `toolkit.json` next to the project you are working on, so the same
code drives LaxLogic, Mathlib, or a private development without edits.

Resolution order:
  1. --config <path>, if the caller passes one
  2. $PROVER_TOOLKIT_CONFIG
  3. ./toolkit.json, walking upwards from the working directory

A config is a small JSON document:

    {
      "repo":     "/abs/path/to/lean/project",   // where `lake` runs
      "corpora":  ["corpora/laxlogic.json"],     // benchmark source lists
      "index":    {"roots": [{"path": "...", "label": "laxlogic"}],
                   "port": 8080},
      "exclude":  ["wip", "Archive", ".claude"]
    }

Nothing here is specific to any repository: a project that is private simply
keeps its own `toolkit.json` private and never publishes it.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

DEFAULT_EXCLUDE = ["wip", "Archive", "archive", ".claude", ".lake", ".git"]


class Config:
    def __init__(self, data: dict, source: Path | None = None):
        self.source = source
        self._d = data
        if "repo" not in data:
            raise ValueError(f"{source or 'config'}: missing required key 'repo'")

    @property
    def repo(self) -> Path:
        p = Path(self._d["repo"]).expanduser()
        if not p.is_absolute() and self.source:
            p = (self.source.parent / p).resolve()
        return p

    @property
    def corpora(self) -> list[Path]:
        base = self.source.parent if self.source else Path.cwd()
        return [(base / c).resolve() if not Path(c).is_absolute() else Path(c)
                for c in self._d.get("corpora", [])]

    @property
    def index_roots(self) -> list[dict]:
        return self._d.get("index", {}).get("roots", [])

    @property
    def index_port(self) -> int:
        return int(self._d.get("index", {}).get("port", 8080))

    @property
    def exclude(self) -> list[str]:
        return self._d.get("exclude", DEFAULT_EXCLUDE)

    @property
    def allow_axioms(self) -> list[str] | None:
        """Optional absolute axiom ceiling. Normally absent: the axiom gate
        works by regression against the proof being replaced, not a fixed list.
        See README - an absolute policy was tried and was wrong."""
        return self._d.get("allow_axioms")


def find_config(explicit: str | os.PathLike | None = None) -> Config:
    if explicit:
        p = Path(explicit).expanduser().resolve()
        return Config(json.loads(p.read_text()), p)
    env = os.environ.get("PROVER_TOOLKIT_CONFIG")
    if env:
        p = Path(env).expanduser().resolve()
        return Config(json.loads(p.read_text()), p)
    here = Path.cwd().resolve()
    for d in [here, *here.parents]:
        cand = d / "toolkit.json"
        if cand.exists():
            return Config(json.loads(cand.read_text()), cand)
    raise FileNotFoundError(
        "no toolkit.json found. Create one (see toolkit_config.py docstring), "
        "or pass --config, or set PROVER_TOOLKIT_CONFIG.")
