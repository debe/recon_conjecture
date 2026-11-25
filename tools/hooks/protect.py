#!/usr/bin/env python3
"""PreToolUse guard: keep agents out of the trusted zones.

Blocks (exit 2, reason on stderr):
  * Edit / Write / NotebookEdit on a trusted path
  * Bash commands that mention a trusted path together with a write-like operation
  * Bash commands that run the human-only `desk.py approve`

The trusted zones change only through tools/desk.py and tools/gate.py, or by the human.
This is a guard against accidents and shortcuts, not against a determined adversary:
tools/audit.py and the human's git review are the final layers.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

TRUSTED = [
    "lean/Recon/Basic.lean",
    "lean/Recon/Statements/",
    "lean/Recon/Checked/",
    "lean/lakefile.toml",
    "lean/lean-toolchain",
    "lean/lake-manifest.json",
    "ledger/",
    "tools/desk.py",
    "tools/gate.py",
    "tools/audit.py",
    "tools/hooks/",
    "tools/tests/",
    ".claude/settings.json",
    ".claude/settings.local.json",
]

# Bash commands may run from inside lean/, so also match the paths without the prefix.
MENTIONS = TRUSTED + [t[len("lean/"):] for t in TRUSTED if t.startswith("lean/")]

# Mentions that are fine: running the trusted tools themselves.
TOOL_RUN = re.compile(r"python3?\s+(-I\s+)?(\./)?tools/(desk|gate|audit)\.py")

WRITE_HINTS = re.compile(
    r"(>|\btee\b|\bsed\s+-i|\bperl\s+-[a-z]*i|\brm\b|\bmv\b|\bcp\b|\btruncate\b|\bdd\b|"
    r"\bchmod\b|\bchown\b|\bln\b|\binstall\b|\brsync\b|\btouch\b|\bunlink\b|\bshred\b|"
    r"\bgit\s+(checkout|restore|reset|rm|mv|clean|stash|apply|am|cherry-pick|revert)\b|"
    r"open\(|write_text|write_bytes|\.write\(|os\.remove|shutil\.|Path\(.*\)\.unlink|"
    r"json\.dump\b|>>)"
)


def is_trusted(path_str: str, cwd: str) -> str | None:
    p = Path(path_str)
    if not p.is_absolute():
        p = Path(cwd) / p
    try:
        rel = p.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return None
    for t in TRUSTED:
        if rel == t.rstrip("/") or (t.endswith("/") and rel.startswith(t)):
            return t
    return None


def block(msg: str) -> None:
    print(f"BLOCKED by tools/hooks/protect.py: {msg}\n"
          "Trusted zones change only through tools/desk.py and tools/gate.py, or by the "
          "human. See CLAUDE.md, 'Trusted zones'.", file=sys.stderr)
    sys.exit(2)


def main() -> None:
    try:
        data = json.load(sys.stdin)
    except Exception:
        sys.exit(0)
    tool = data.get("tool_name", "")
    inp = data.get("tool_input", {}) or {}
    cwd = data.get("cwd") or str(ROOT)

    if tool in ("Edit", "Write", "MultiEdit", "NotebookEdit"):
        path = inp.get("file_path") or inp.get("notebook_path") or ""
        t = is_trusted(path, cwd) if path else None
        if t:
            block(f"{tool} on trusted path {t}")
        sys.exit(0)

    if tool == "Bash":
        cmd = inp.get("command", "")
        if re.search(r"desk\.py\s+approve\b", cmd):
            block("`desk.py approve` is human-only; ask the human to run it")
        if re.search(r"\bimport\s+desk\b|from\s+desk\s+import|importlib.*desk", cmd):
            block("do not drive desk.py internals from ad-hoc code; use its CLI")
        scrubbed = TOOL_RUN.sub(" ", cmd)
        mentioned = [t for t in MENTIONS if t.rstrip("/") in scrubbed]
        if mentioned and WRITE_HINTS.search(scrubbed):
            block(f"command writes near trusted path(s) {mentioned}")
        sys.exit(0)

    sys.exit(0)


if __name__ == "__main__":
    main()
