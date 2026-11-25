#!/usr/bin/env python3
"""CI policy: rules on the diff of a pull request that the Lean checker cannot see.

  python3 tools/ci_policy.py --base <sha> [--head HEAD] [--labels '["trusted-change"]']

Runs in CI next to `audit.py --clean` (which re-verifies every checked result). This file
checks what a contributor's machine could get wrong or skip:

  1. the checked library and the frozen statements are append-only
  2. trusted files change only in a PR labelled `trusted-change` (labels are maintainer-only)
  3. ledger step records are never deleted, the event log is append-only
     (exception for 1 and 3: `desk.py rename` moves a step's files to its new id; the PR
     records a `renamed` event and needs the `trusted-change` label)
  4. every root step past `proposed` was approved by a maintainer for its current statement
  5. no lease lives in a step record (leases are refs/leases/*)
  6. no reduced step is left with a complete, unassembled reduction

Exit 0 when every rule holds; 1 lists every violation.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAINTAINERS = ROOT / ".github" / "maintainers.txt"
TRUSTED_LABEL = "trusted-change"

APPEND_ONLY = ("lean/Recon/Checked/", "lean/Recon/Statements/")
TRUSTED = (
    "lean/Recon/Basic.lean", "lean/lakefile.toml", "lean/lean-toolchain",
    "lean/lake-manifest.json", "tools/desk.py", "tools/gate.py", "tools/audit.py",
    "tools/ci_policy.py", "tools/live.py", "tools/hooks/", "tools/tests/", ".github/", ".claude/settings.json",
    ".gitattributes",
)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, check=True, capture_output=True,
                          text=True).stdout


def show(rev: str, path: str) -> str | None:
    p = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=ROOT, capture_output=True,
                       text=True)
    return p.stdout if p.returncode == 0 else None


def changes(base: str, head: str) -> list[tuple[str, str]]:
    out = git("diff", "--no-renames", "--name-status", f"{base}..{head}")
    return [(line.split("\t", 1)[0], line.split("\t", 1)[1])
            for line in out.splitlines() if line.strip()]


def steps_at(rev: str) -> dict[str, dict]:
    names = git("ls-tree", "--name-only", rev, "ledger/steps/").split()
    recs = {}
    for name in names:
        if name.endswith(".json"):
            recs[Path(name).stem] = json.loads(show(rev, name) or "{}")
    return recs


def maintainers(rev: str) -> set[str]:
    text = show(rev, ".github/maintainers.txt") or ""
    return {ln.strip() for ln in text.splitlines() if ln.strip() and not ln.startswith("#")}


def renamed_ids(added_lines: Counter) -> set[str]:
    """Old ids of the steps that `desk.py rename` moved, from the event lines a PR adds."""
    out = set()
    for line in added_lines:
        try:
            e = json.loads(line)
        except ValueError:
            continue
        if e.get("kind") == "renamed" and e.get("renamed_from"):
            out.add(e["renamed_from"])
    return out


def deleted_step(path: str) -> str | None:
    """The step id whose statement, checked proof or record lives at `path`, if any."""
    p = Path(path)
    if path.startswith("lean/Recon/Statements/S_") and p.suffix == ".lean":
        return p.stem[len("S_"):]
    if path.startswith("lean/Recon/Checked/L_") and p.suffix == ".lean":
        return p.stem[len("L_"):]
    if path.startswith("ledger/steps/") and p.suffix == ".json":
        return p.stem
    return None


def check(base: str, head: str, labels: set[str] | None) -> list[str]:
    """labels=None: a push to protected main. Every such push is a merged PR that already
    passed the label rule, and a push event carries no labels, so that rule is skipped."""
    problems: list[str] = []
    diff = changes(base, head)

    old_events = Counter((show(base, "ledger/events.jsonl") or "").splitlines())
    new_events = Counter((show(head, "ledger/events.jsonl") or "").splitlines())
    lost = old_events - new_events
    if lost:
        problems.append(f"ledger/events.jsonl: {sum(lost.values())} existing line(s) removed or "
                        f"edited; the event log is append-only")
    renamed = renamed_ids(new_events - old_events)
    rename_ok = labels is None or TRUSTED_LABEL in labels

    for status, path in diff:
        sid = deleted_step(path) if status == "D" else None
        if sid and sid in renamed:
            # `desk.py rename` moved this step's files to its new id. Like a change to the
            # judge, that needs a maintainer's label; a push to main re-checks a merged PR.
            if not rename_ok:
                problems.append(f"{path}: renaming {sid} needs the `{TRUSTED_LABEL}` label")
            continue
        if path.startswith(APPEND_ONLY) and status != "A":
            problems.append(f"{path}: {status} on an append-only path (checked results and "
                            f"frozen statements are never modified or deleted)")
        if path.startswith("ledger/steps/") and status == "D":
            problems.append(f"{path}: step records are never deleted")
    touched_trusted = sorted({p for _, p in diff if p.startswith(TRUSTED)})
    if touched_trusted and labels is not None and TRUSTED_LABEL not in labels:
        problems.append(f"trusted files changed without the `{TRUSTED_LABEL}` label: "
                        + ", ".join(touched_trusted))

    # Approval is judged against the maintainers list of the base: a PR cannot add its
    # own approver.
    allowed = maintainers(base) or maintainers(head)
    recs = steps_at(head)
    for sid, r in sorted(recs.items()):
        if r.get("lease"):
            problems.append(f"{sid}: lease stored in the step record; leases live in "
                            f"refs/leases/{sid}")
        if r.get("is_root") and r.get("status") != "proposed":
            if r.get("human_approved_sha256") != r.get("statement_sha256"):
                problems.append(f"{sid}: root step is {r.get('status')} without a human "
                                f"approval of its current statement")
            elif r.get("approved_by") not in allowed:
                problems.append(f"{sid}: approved_by={r.get('approved_by')!r} is not in "
                                f".github/maintainers.txt")
        if r.get("status") == "reduced":
            for red in r.get("reductions", []):
                if red.get("status") == "checked" and all(
                        recs.get(c, {}).get("status") == "checked" for c in red["children"]):
                    problems.append(f"{sid}: reduction {red['name']} is complete but not "
                                    f"assembled; run `python3 tools/gate.py assemble {sid}`")
    return problems


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--base", required=True)
    ap.add_argument("--head", default="HEAD")
    ap.add_argument("--labels", default=None,
                    help="JSON list of PR label names; omit for a push to protected main")
    a = ap.parse_args(argv)
    labels = None if a.labels is None else set(json.loads(a.labels or "[]"))
    problems = check(a.base, a.head, labels)
    if problems:
        print("POLICY FAILED")
        for p in problems:
            print(" -", p)
        return 1
    print("POLICY PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
