#!/usr/bin/env python3
"""Audit: re-verify every checked result from scratch. The backstop behind the gate.

  python3 tools/audit.py            hashes + lexical + wrapper/axiom check of every result
  python3 tools/audit.py --clean    also delete Recon build outputs and rebuild everything

Exit 0 when everything verifies; 1 lists every problem found.
"""
from __future__ import annotations

import argparse
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import desk  # noqa: E402
import gate  # noqa: E402

ROOT = desk.ROOT


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--clean", action="store_true")
    a = ap.parse_args()
    problems: list[str] = []
    steps = desk.all_steps()
    known_statements = {(ROOT / s["statement_file"]).resolve() for s in steps}
    known_results: set[Path] = set()

    for f in sorted(desk.STATEMENTS.glob("*.lean")):
        if f.resolve() not in known_statements:
            problems.append(f"statement file without ledger record: {f.relative_to(ROOT)}")

    if a.clean:
        out = desk.LEAN / ".lake" / "build" / "lib" / "lean" / "Recon"
        shutil.rmtree(out, ignore_errors=True)
        ok, log = desk.build_module("Recon")
        if not ok:
            problems.append("clean `lake build Recon` failed:\n" + log[-3000:])

    for s in steps:
        sid = s["id"]
        sf = ROOT / s["statement_file"]
        if not sf.exists():
            problems.append(f"{sid}: statement file missing")
            continue
        if desk.sha256_file(sf) != s["statement_sha256"]:
            problems.append(f"{sid}: statement file hash differs from ledger")
        results = []
        if s.get("checked"):
            results.append((sid, s["checked"], f"Recon.Checked.L_{sid}",
                            f"Recon.Statements.S_{sid}", [desk.statement_module(sid)]))
        if s.get("refuted"):
            results.append((f"{sid}_neg", s["refuted"], f"Recon.Checked.L_{sid}_neg",
                            f"Recon.Statements.S_{sid}_neg", [desk.statement_module(sid)]))
        for red in s.get("reductions", []):
            if red.get("status") in ("checked", "dead"):
                exp = " → ".join([*(f"Recon.Statements.S_{c}" for c in red["children"]),
                                  f"Recon.Statements.S_{sid}"])
                results.append((red["name"], red, f"Recon.Checked.{red['name']}", exp,
                                [desk.statement_module(sid),
                                 *(desk.statement_module(c) for c in red["children"])]))
        for name, info, decl, expected, smods in results:
            f = ROOT / info["file"]
            known_results.add(f.resolve())
            if not f.exists():
                problems.append(f"{name}: checked file missing")
                continue
            if desk.sha256_file(f) != info["sha256"]:
                problems.append(f"{name}: checked file hash differs from ledger")
            text = f.read_text()
            try:
                gate.lexical_check(text, decl, set(smods))
                module = gate.module_of(f)
                ok, log = desk.build_module(module)
                if not ok:
                    problems.append(f"{name}: does not build:\n{log[-2000:]}")
                    continue
                axioms = gate.wrapper_check([*smods, module], expected, decl)
                print(f"ok  {name}  axioms={axioms}")
            except (gate.Rejected, gate.Fault) as e:
                problems.append(f"{name}: {e}")

    for f in sorted(desk.CHECKED.glob("*.lean")):
        if f.resolve() not in known_results:
            problems.append(f"file in Checked/ without ledger record: {f.relative_to(ROOT)}")

    if problems:
        print("\nAUDIT FAILED")
        for p in problems:
            print(" -", p)
        return 1
    print(f"\nAUDIT PASSED ({len(known_results)} results, {len(steps)} steps)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
