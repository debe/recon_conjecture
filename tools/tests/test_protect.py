"""Tests for the PreToolUse guard (fast)."""
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
HOOK = ROOT / "tools" / "hooks" / "protect.py"


def run(tool, cwd=str(ROOT), **inp):
    data = json.dumps({"tool_name": tool, "tool_input": inp, "cwd": cwd})
    return subprocess.run([sys.executable, str(HOOK)], input=data, text=True,
                          capture_output=True).returncode


@pytest.mark.parametrize("path", ["lean/Recon/Basic.lean", "lean/Recon/Checked/L_x.lean",
                                  "lean/Recon/Statements/S_x.lean", "ledger/steps/a.json",
                                  "tools/gate.py", ".claude/settings.json", "lean/lakefile.toml"])
def test_blocks_trusted_writes(path):
    assert run("Write", file_path=str(ROOT / path)) == 2
    assert run("Edit", file_path=path) == 2


@pytest.mark.parametrize("path", ["lean/Recon/Scratch/x/b1.lean", "notes/sketches/x/t1.md",
                                  "CLAUDE.md", "/tmp/elsewhere.txt"])
def test_allows_untrusted_writes(path):
    assert run("Write", file_path=path) == 0


@pytest.mark.parametrize("cmd", [
    "python3 tools/desk.py approve found_001",
    "echo x > ledger/events.jsonl",
    "sed -i s/a/b/ lean/Recon/Basic.lean",
    "cd lean && rm Recon/Checked/L_x.lean",
    "git checkout -- ledger/",
    "python3 -c 'import desk'",
])
def test_blocks_bash(cmd):
    assert run("Bash", command=cmd) == 2


@pytest.mark.parametrize("cmd", [
    "python3 tools/desk.py summary",
    "python3 tools/gate.py check found_001 lean/Recon/Scratch/found_001/b1.lean",
    "cat ledger/steps/found_001.json",
    "cd lean && lake env lean Recon/Scratch/found_001/b1.lean",
    "python3 tools/desk.py summary > notes/rounds/tmp.txt",
])
def test_allows_bash(cmd):
    assert run("Bash", command=cmd) == 0
