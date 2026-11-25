"""Leases as compare-and-swap git refs: two clones of one bare origin race for a step.

Fast (no Lean). The desk's lease code runs against scratch repositories, never this one.
"""
from __future__ import annotations

import subprocess
import sys
import threading
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import desk  # noqa: E402


def sh(cwd: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True)


@pytest.fixture
def clones(tmp_path, monkeypatch):
    monkeypatch.setenv("RECON_LIVE", "off")
    monkeypatch.delenv("RECON_LEASES", raising=False)
    origin = tmp_path / "origin.git"
    sh(tmp_path, "init", "--bare", "-q", str(origin))
    out = []
    for name in ("a", "b"):
        c = tmp_path / name
        sh(tmp_path, "init", "-q", str(c))
        sh(c, "remote", "add", "origin", str(origin))
        out.append(c)
    return out


def as_clone(monkeypatch, clone: Path, who: str) -> None:
    monkeypatch.setattr(desk, "LEASE_REPO", clone)
    monkeypatch.setenv("RECON_HANDLE", who)


def test_one_holder_at_a_time(clones, monkeypatch):
    a, b = clones
    as_clone(monkeypatch, a, "alice")
    info = desk.acquire("found_iso_hypomorphic", "b1", 30, "starting")
    assert info["holder"] == "alice/b1"
    as_clone(monkeypatch, b, "bob")
    with pytest.raises(desk.DeskError, match="leased by alice/b1"):
        desk.acquire("found_iso_hypomorphic", "b1", 30)
    with pytest.raises(desk.DeskError, match="does not hold"):
        desk.renew("found_iso_hypomorphic", "b1", 30)
    with pytest.raises(desk.DeskError, match="held by alice/b1"):
        desk.drop("found_iso_hypomorphic", "b1")
    assert desk.live_lease(desk.read_leases(), "found_iso_hypomorphic")["note"] == "starting"


def test_holder_renews_and_releases(clones, monkeypatch):
    a, b = clones
    as_clone(monkeypatch, a, "alice")
    first = desk.acquire("found_iso_hypomorphic", "b1", 30)
    again = desk.renew("found_iso_hypomorphic", "b1", 60, "precheck 2")
    assert again["since"] == first["since"] and again["expires"] > first["expires"]
    assert desk.drop("found_iso_hypomorphic", "b1") is True
    as_clone(monkeypatch, b, "bob")
    assert desk.read_leases() == {}
    assert desk.acquire("found_iso_hypomorphic", "b2", 30)["holder"] == "bob/b2"


def test_expired_lease_can_be_taken_over(clones, monkeypatch):
    a, b = clones
    as_clone(monkeypatch, a, "alice")
    desk.acquire("found_iso_hypomorphic", "b1", 0)          # expires immediately
    as_clone(monkeypatch, b, "bob")
    assert desk.live_lease(desk.read_leases(), "found_iso_hypomorphic") is None
    assert desk.acquire("found_iso_hypomorphic", "b1", 30)["holder"] == "bob/b1"
    as_clone(monkeypatch, a, "alice")
    with pytest.raises(desk.DeskError, match="does not hold"):
        desk.renew("found_iso_hypomorphic", "b1", 30)


def test_race_has_exactly_one_winner(clones, monkeypatch):
    """Both clones read 'no lease', then both push a create: the remote takes one."""
    a, b = clones
    monkeypatch.setenv("RECON_HANDLE", "racer")
    objs = {}
    for c in (a, b):
        monkeypatch.setattr(desk, "LEASE_REPO", c)
        objs[c] = desk._lease_object(f"racer/{c.name}", 30, None, None)[0]
    results = {}
    barrier = threading.Barrier(2)

    def push(c: Path) -> None:
        barrier.wait()
        p = subprocess.run(["git", "push", "--porcelain", "--force-with-lease=refs/leases/x:",
                            "origin", f"{objs[c]}:refs/leases/x"], cwd=c, capture_output=True,
                           text=True)
        results[c.name] = p.returncode == 0

    threads = [threading.Thread(target=push, args=(c,)) for c in (a, b)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert sorted(results.values()) == [False, True]


def test_local_mode_without_origin(tmp_path, monkeypatch):
    monkeypatch.setenv("RECON_LIVE", "off")
    sh(tmp_path, "init", "-q", ".")
    as_clone(monkeypatch, tmp_path, "solo")
    desk.acquire("kelly_degree_sequence", "b1", 30)
    with pytest.raises(desk.DeskError):
        monkeypatch.setenv("RECON_HANDLE", "other")
        desk.acquire("kelly_degree_sequence", "b1", 30)
    monkeypatch.setenv("RECON_HANDLE", "solo")
    assert desk.drop("kelly_degree_sequence", "b1") is True
    assert desk.read_leases() == {}
