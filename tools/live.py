#!/usr/bin/env python3
"""Emit live events to the relay behind the canvas page. Best effort, never authoritative.

  python3 tools/live.py emit <kind> [--step ID] [--actor A] [--note TEXT]
  python3 tools/live.py ping                      relay health

As a library (desk.py, gate.py, hooks):  live.emit("leased", "found_001", "debe/b1", minutes=120)

Configuration:
  token  RECON_LIVE_TOKEN, else ~/.config/recon/live.token   (no token: emit does nothing)
  url    RECON_LIVE_URL, else https://recon.knownhosts.org
  off    RECON_LIVE=off

A relay that is down or slow never fails or blocks the caller for long: the POST runs on a
background thread with a short timeout, and the process waits at most that long at exit.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import sys
import threading
import urllib.request
import uuid
from pathlib import Path

URL = os.environ.get("RECON_LIVE_URL", "https://recon.knownhosts.org").rstrip("/")
TIMEOUT = 2.0
MAX_NOTE = 200
HOME = str(Path.home())


def _token() -> str | None:
    tok = os.environ.get("RECON_LIVE_TOKEN")
    if tok:
        return tok.strip()
    p = Path.home() / ".config" / "recon" / "live.token"
    try:
        return p.read_text().strip() or None
    except OSError:
        return None


def _clean(v):
    if isinstance(v, str):
        v = v.replace(HOME, "~")
        return v if len(v) <= MAX_NOTE else v[: MAX_NOTE - 1] + "…"
    if isinstance(v, (list, tuple)):
        return [_clean(x) for x in v][:20]
    if isinstance(v, dict):
        return {k: _clean(x) for k, x in list(v.items())[:20]}
    return v


def _post(body: bytes, token: str) -> int | None:
    req = urllib.request.Request(URL + "/events", data=body, method="POST", headers={
        "Authorization": f"Bearer {token}", "Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as r:
            return r.status
    except Exception:
        return None


def payload(kind: str, step: str | None, actor: str | None, **data) -> bytes:
    ev = {"id": uuid.uuid4().hex, "ts": _dt.datetime.now(_dt.timezone.utc).isoformat(
        timespec="seconds"), "kind": kind, "step": step, "actor": actor}
    ev.update({k: _clean(v) for k, v in data.items() if v is not None})
    # compact, one line: the relay forwards these exact bytes as one SSE data line
    return json.dumps(ev, separators=(",", ":"), ensure_ascii=False).encode()


def emit(kind: str, step: str | None = None, actor: str | None = None, wait: bool = False,
         **data) -> threading.Thread | None:
    if os.environ.get("RECON_LIVE") == "off":
        return None
    token = _token()
    if not token:
        return None
    body = payload(kind, step, actor, **data)
    t = threading.Thread(target=_post, args=(body, token), name="recon-live", daemon=False)
    t.start()
    if wait:
        t.join(TIMEOUT + 0.5)
    return t


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("emit")
    p.add_argument("kind"); p.add_argument("--step"); p.add_argument("--actor")
    p.add_argument("--note"); p.add_argument("--data", help="extra JSON object")
    sub.add_parser("ping")
    a = ap.parse_args(argv)
    if a.cmd == "ping":
        try:
            with urllib.request.urlopen(URL + "/health", timeout=TIMEOUT) as r:
                print(r.read().decode().strip())
                return 0
        except Exception as e:
            print(f"relay unreachable: {e}")
            return 1
    token = _token()
    if not token:
        print("no token (RECON_LIVE_TOKEN or ~/.config/recon/live.token)")
        return 1
    extra = json.loads(a.data) if a.data else {}
    code = _post(payload(a.kind, a.step, a.actor, note=a.note, **extra), token)
    print(f"relay answered {code}")
    return 0 if code in (200, 202) else 1


if __name__ == "__main__":
    sys.exit(main())
