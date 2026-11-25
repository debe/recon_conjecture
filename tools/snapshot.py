#!/usr/bin/env python3
"""Build the canvas page's snapshot (site/state.json) from the ledger on this checkout.

  python3 tools/snapshot.py [--out site/state.json] [--events 300]

Run by .github/workflows/pages.yml on every push to main, so the page always starts from
the merged truth; live events from the relay are layered on top in the browser.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import desk  # noqa: E402

KEEP = ("id", "program", "title", "status", "parent", "children", "is_root", "priority",
        "statement_en", "statement_lean", "statement_file", "negated_twin", "created",
        "frozen_at", "approved_by")


def step_view(s: dict) -> dict:
    v = {k: s.get(k) for k in KEEP}
    v["fidelity_passes"] = len({f["reviewer"] for f in s.get("fidelity", [])
                                if f["verdict"] == "pass"
                                and f.get("sha256") == s.get("statement_sha256")})
    v["dead_ends"] = [{"approach": d.get("approach", "")[:200], "reason": d.get("reason"),
                       "by": d.get("by"), "at": d.get("at")} for d in s.get("dead_ends", [])]
    v["sketches"] = len(s.get("sketches", []))
    v["reductions"] = [{"name": r["name"], "children": r["children"], "status": r["status"]}
                       for r in s.get("reductions", [])]
    for key in ("checked", "refuted"):
        if s.get(key):
            v[key] = {"file": s[key]["file"], "at": s[key].get("at"), "by": s[key].get("by"),
                      "axioms": s[key].get("axioms", [])}
    return v


def build(n_events: int) -> dict:
    events = []
    if desk.EVENTS.exists():
        for line in desk.EVENTS.read_text().splitlines()[-n_events:]:
            try:
                events.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    try:
        leases = desk.read_leases()
    except desk.DeskError:
        leases = {}
    return {
        "generated_at": desk.now(),
        "commit": os.environ.get("GITHUB_SHA", ""),
        "repo": os.environ.get("GITHUB_REPOSITORY", "debe/recon_conjecture"),
        "programs": desk.load_programs(),
        "steps": [step_view(s) for s in desk.all_steps()],
        "leases": {k: {x: v.get(x) for x in ("holder", "since", "expires", "note")}
                   for k, v in leases.items()},
        "events": events,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", default=str(desk.ROOT / "site" / "state.json"))
    ap.add_argument("--events", type=int, default=300)
    a = ap.parse_args(argv)
    out = Path(a.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(build(a.events), ensure_ascii=False, separators=(",", ":")))
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
