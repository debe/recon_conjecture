"""ci_policy.py on synthetic histories (fast, no Lean)."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import ci_policy  # noqa: E402

ROOT_STEP = {"id": "found_001", "program": "found", "status": "proposed", "is_root": True,
             "statement_sha256": "aaa", "reductions": []}


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True,
                          text=True).stdout.strip()


def put(repo: Path, rel: str, text: str) -> None:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


def commit(repo: Path, msg: str) -> str:
    git(repo, "add", "-A")
    git(repo, "-c", "user.name=t", "-c", "user.email=t@invalid", "commit", "-qm", msg)
    return git(repo, "rev-parse", "HEAD")


@pytest.fixture
def repo(tmp_path, monkeypatch):
    git(tmp_path, "init", "-q")
    put(tmp_path, ".github/maintainers.txt", "# approvers\ndebe\n")
    put(tmp_path, "ledger/steps/found_001.json", json.dumps(ROOT_STEP))
    put(tmp_path, "ledger/events.jsonl", '{"kind":"proposed"}\n')
    put(tmp_path, "lean/Recon/Checked/L_x.lean", "theorem x : True := trivial\n")
    put(tmp_path, "notes/a.md", "a\n")
    base = commit(tmp_path, "base")
    monkeypatch.setattr(ci_policy, "ROOT", tmp_path)
    return tmp_path, base


def check(repo, base, labels=()):
    return ci_policy.check(base, "HEAD", set(labels))


def test_clean_change_passes(repo):
    r, base = repo
    put(r, "notes/a.md", "b\n")
    put(r, "lean/Recon/Checked/L_y.lean", "theorem y : True := trivial\n")
    with open(r / "ledger/events.jsonl", "a") as fh:
        fh.write('{"kind":"checked"}\n')
    commit(r, "ok")
    assert check(r, base) == []


def test_checked_files_are_append_only(repo):
    r, base = repo
    put(r, "lean/Recon/Checked/L_x.lean", "theorem x : True := by trivial\n")
    commit(r, "edit")
    assert any("append-only" in p for p in check(r, base))


def test_trusted_change_needs_label(repo):
    r, base = repo
    put(r, "tools/gate.py", "# changed\n")
    commit(r, "gate")
    assert any("trusted-change" in p for p in check(r, base))
    assert check(r, base, ["trusted-change"]) == []


def test_frozen_root_needs_maintainer_approval(repo):
    r, base = repo
    rec = {**ROOT_STEP, "status": "frozen", "human_approved_sha256": "aaa", "approved_by": "mallory"}
    put(r, "ledger/steps/found_001.json", json.dumps(rec))
    commit(r, "freeze")
    assert any("maintainers" in p for p in check(r, base))
    rec["approved_by"] = "debe"
    put(r, "ledger/steps/found_001.json", json.dumps(rec))
    commit(r, "fix")
    assert check(r, base) == []
    rec["human_approved_sha256"] = "bbb"
    put(r, "ledger/steps/found_001.json", json.dumps(rec))
    commit(r, "stale approval")
    assert any("without a human approval" in p for p in check(r, base))


def test_pr_cannot_add_its_own_approver(repo):
    r, base = repo
    put(r, ".github/maintainers.txt", "debe\nmallory\n")
    rec = {**ROOT_STEP, "status": "frozen", "human_approved_sha256": "aaa", "approved_by": "mallory"}
    put(r, "ledger/steps/found_001.json", json.dumps(rec))
    commit(r, "sneaky")
    assert any("maintainers" in p for p in check(r, base, ["trusted-change"]))


def test_event_log_is_append_only_and_records_stay(repo):
    r, base = repo
    put(r, "ledger/events.jsonl", "")
    (r / "ledger/steps/found_001.json").unlink()
    commit(r, "erase")
    problems = check(r, base)
    assert any("append-only" in p and "events" in p for p in problems)
    assert any("never deleted" in p for p in problems)


def test_no_lease_in_records_and_no_pending_assembly(repo):
    r, base = repo
    parent = {**ROOT_STEP, "id": "found_002", "is_root": False, "status": "reduced",
              "lease": {"holder": "x"},
              "reductions": [{"name": "R_found_002_r1", "status": "checked",
                              "children": ["found_002_r1a"]}]}
    child = {**ROOT_STEP, "id": "found_002_r1a", "is_root": False, "status": "checked"}
    put(r, "ledger/steps/found_002.json", json.dumps(parent))
    put(r, "ledger/steps/found_002_r1a.json", json.dumps(child))
    commit(r, "parallel siblings")
    problems = check(r, base)
    assert any("lease stored" in p for p in problems)
    assert any("gate.py assemble found_002" in p for p in problems)
