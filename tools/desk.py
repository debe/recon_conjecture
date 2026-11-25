#!/usr/bin/env python3
"""The desk: the only writer of ledger/ and lean/Recon/Statements/.

Every state change of a step goes through this file (or through gate.py, which calls into
it). Agents never edit ledger/ or Statements/ by hand; tools/hooks/protect.py blocks that.

Commands (run `python3 tools/desk.py -h`):
  summary                         fleet overview (programs, counts, open steps)
  status <id>                     one step record, pretty-printed
  list [--status S] [--program P] list steps
  propose ...                     state a new root step (status: proposed)
  fidelity <id> ...               record one statement-fidelity review
  approve <id>                    HUMAN ONLY: approve a root statement for freezing
  freeze <id>                     proposed -> frozen (roots need 2 fidelity passes + approve)
  next [--program P]              suggest the next frozen, unleased step
  lease <id> --holder H           take a lease (default 120 min); atomic across machines
  beat <id> --holder H [--note T] renew a lease, saying what the holder is doing now
  release <id> --holder H --reason R [--note T]   give a step back with a structured reason
  leases                          list live and expired leases

Leases are git refs `refs/leases/<id>` on origin (or in this repo when there is no origin),
written with compare-and-swap pushes: exactly one claimant wins. They are coordination, not
safety. Identity: `git config recon.handle <github-handle>` (or RECON_HANDLE); holders and
actors are recorded as `<handle>/<label>`.
  dead-end <id> --approach A --reason R --by B     record a failed approach
  sketch <id> --path P --by B     attach a paper sketch (notes/sketches/...)
  program-add ...                 add a program (line of attack)
"""
from __future__ import annotations

import argparse
import contextlib
import datetime as _dt
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import live  # noqa: E402

LEAN = ROOT / "lean"
STATEMENTS = LEAN / "Recon" / "Statements"
CHECKED = LEAN / "Recon" / "Checked"
LEDGER = ROOT / "ledger"
STEPS = LEDGER / "steps"
EVENTS = LEDGER / "events.jsonl"
PROGRAMS = LEDGER / "programs.json"
LOCK = LEDGER / ".lock"

STEP_ID = re.compile(r"^[a-z]+_\d{3}(_r\d+[a-d])*$")
STATUSES = ("proposed", "frozen", "checked", "refuted", "reduced", "withdrawn")
RELEASE_REASONS = (
    "hypothesis_too_weak", "missing_lemma", "statement_seems_false",
    "does_not_elaborate", "out_of_time", "reduced", "other",
)
FIDELITY_PASSES_NEEDED = 2
MAX_STATEMENT_CHARS = 4000

# Statement bodies are Lean terms elaborated in a trusted file. They may use Mathlib and the
# Recon definitions, nothing that runs code or changes syntax.
STATEMENT_FORBIDDEN = re.compile(
    r"\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|macro|syntax|"
    r"elab|notation|infix|infixl|infixr|prefix|postfix|initialize|run_cmd|run_tac|attribute|"
    r"instance|import|set_option|namespace|section|end|open|variable|theorem|lemma|def|abbrev|"
    r"Lean\.Elab|Lean\.Meta)\b|#|\"|--|/-"
)


class DeskError(Exception):
    pass


def now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0).isoformat()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@contextlib.contextmanager
def locked():
    """Serialize every ledger write (and gate runs) across processes."""
    LEDGER.mkdir(parents=True, exist_ok=True)
    with open(LOCK, "w") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(fh, fcntl.LOCK_UN)


# --------------------------------------------------------------------------- records

def step_path(step_id: str) -> Path:
    return STEPS / f"{step_id}.json"


def load(step_id: str) -> dict:
    p = step_path(step_id)
    if not p.exists():
        raise DeskError(f"unknown step {step_id!r}")
    return json.loads(p.read_text())


def save(rec: dict) -> None:
    STEPS.mkdir(parents=True, exist_ok=True)
    tmp = step_path(rec["id"]).with_suffix(".json.tmp")
    tmp.write_text(json.dumps(rec, indent=2, ensure_ascii=False) + "\n")
    tmp.replace(step_path(rec["id"]))


def all_steps() -> list[dict]:
    if not STEPS.exists():
        return []
    return [json.loads(p.read_text()) for p in sorted(STEPS.glob("*.json"))]


def handle() -> str:
    """This machine's GitHub handle: RECON_HANDLE, else `git config recon.handle`."""
    h = os.environ.get("RECON_HANDLE")
    if not h:
        p = subprocess.run(["git", "config", "recon.handle"], cwd=ROOT, capture_output=True,
                           text=True)
        h = p.stdout.strip()
    return h or "local"


def qualify(actor: str) -> str:
    """'b1' -> 'debe/b1'. Already-qualified names and 'human' stay as they are."""
    if "/" in actor:
        return actor
    return f"{handle()}/{actor}"


def event(kind: str, step: str | None, actor: str, ledger: bool = True, **data) -> None:
    """Append to the graveyard (ledger/events.jsonl) and mirror to the live view."""
    actor = qualify(actor)
    if ledger:
        LEDGER.mkdir(parents=True, exist_ok=True)
        line = {"ts": now(), "kind": kind, "step": step, "actor": actor, **data}
        with open(EVENTS, "a") as fh:
            fh.write(json.dumps(line, ensure_ascii=False) + "\n")
    live.emit(kind, step, actor, **data)


def load_programs() -> list[dict]:
    if not PROGRAMS.exists():
        return []
    return json.loads(PROGRAMS.read_text())


def save_programs(progs: list[dict]) -> None:
    PROGRAMS.write_text(json.dumps(progs, indent=2, ensure_ascii=False) + "\n")


def base_id(target: str) -> tuple[str, bool]:
    """'found_001_neg' -> ('found_001', True); 'found_001' -> ('found_001', False)."""
    if target.endswith("_neg"):
        return target[: -len("_neg")], True
    return target, False


# --------------------------------------------------------------------------- leases (git refs)

LEASE_REPO = ROOT          # tests point this at a scratch clone
EMPTY_TREE_INPUT = ""      # `git mktree` on empty input writes the empty tree


class LeaseLost(DeskError):
    pass


def _git(*args: str, check: bool = True) -> subprocess.CompletedProcess:
    env = {**os.environ, "GIT_AUTHOR_NAME": "recon-desk", "GIT_AUTHOR_EMAIL": "desk@invalid",
           "GIT_COMMITTER_NAME": "recon-desk", "GIT_COMMITTER_EMAIL": "desk@invalid",
           "GIT_TERMINAL_PROMPT": "0"}
    p = subprocess.run(["git", *args], cwd=LEASE_REPO, capture_output=True, text=True, env=env,
                       input=EMPTY_TREE_INPUT if args[:1] == ("mktree",) else None, timeout=60)
    if check and p.returncode != 0:
        raise DeskError(f"git {' '.join(args[:2])} failed: {p.stderr.strip()[-500:]}")
    return p


def _remote() -> bool:
    if os.environ.get("RECON_LEASES") == "local":
        return False
    return _git("remote", "get-url", "origin", check=False).returncode == 0


def _expired(info: dict) -> bool:
    return _dt.datetime.fromisoformat(info["expires"]) <= _dt.datetime.now(_dt.timezone.utc)


def read_leases() -> dict[str, dict]:
    """Every lease, live or expired: {step: {holder, since, expires, note, sha}}."""
    if _remote():
        _git("fetch", "--quiet", "--prune", "--no-tags", "origin",
             "+refs/leases/*:refs/remote-leases/*")
        ns = "refs/remote-leases/"
    else:
        ns = "refs/leases/"
    out = _git("for-each-ref", "--format=%(objectname) %(refname) %(contents:subject)", ns).stdout
    leases = {}
    for line in out.splitlines():
        sha, ref, subject = (line.split(" ", 2) + [""])[:3]
        try:
            info = json.loads(subject)
        except json.JSONDecodeError:
            continue
        info["sha"] = sha
        leases[ref.removeprefix(ns)] = info
    return leases


def live_lease(leases: dict[str, dict], sid: str) -> dict | None:
    info = leases.get(sid)
    return info if info and not _expired(info) else None


def _cas(sid: str, new: str | None, expect: str) -> bool:
    """Set (or delete, new=None) refs/leases/<sid> only if it currently equals `expect`
    ('' = must not exist). True when this caller won."""
    ref = f"refs/leases/{sid}"
    if _remote():
        spec = f"{new}:{ref}" if new else f":{ref}"
        p = _git("push", "--quiet", "--porcelain", f"--force-with-lease={ref}:{expect}",
                 "origin", spec, check=False)
        if p.returncode == 0:
            return True
        if "stale info" in p.stdout + p.stderr or "rejected" in p.stdout + p.stderr:
            return False
        raise DeskError(f"lease push failed: {(p.stdout + p.stderr).strip()[-500:]}")
    if new:
        p = _git("update-ref", ref, new, expect or "0" * 40, check=False)
    else:
        p = _git("update-ref", "-d", ref, expect, check=False)
    return p.returncode == 0


def _lease_object(holder: str, minutes: int, note: str | None, since: str | None) -> tuple[str, dict]:
    exp = _dt.datetime.now(_dt.timezone.utc) + _dt.timedelta(minutes=minutes)
    info = {"holder": holder, "since": since or now(),
            "expires": exp.replace(microsecond=0).isoformat()}
    if note:
        info["note"] = note[:200]
    tree = _git("mktree").stdout.strip()
    sha = _git("commit-tree", tree, "-m", json.dumps(info, ensure_ascii=False)).stdout.strip()
    return sha, info


def acquire(sid: str, holder: str, minutes: int, note: str | None = None) -> dict:
    """Take or renew a lease. Raises DeskError if someone else holds it or wins the race."""
    holder = qualify(holder)
    cur = read_leases().get(sid)
    if cur and not _expired(cur) and cur["holder"] != holder:
        raise DeskError(f"{sid} is leased by {cur['holder']} until {cur['expires']}")
    mine = cur and cur["holder"] == holder
    sha, info = _lease_object(holder, minutes, note, cur["since"] if mine else None)
    if not _cas(sid, sha, cur["sha"] if cur else ""):
        raise LeaseLost(f"lost the race for {sid}: another holder took it just now")
    return info


def renew(sid: str, holder: str, minutes: int, note: str | None = None) -> dict:
    holder = qualify(holder)
    cur = read_leases().get(sid)
    if not cur or cur["holder"] != holder:
        raise DeskError(f"{holder} does not hold the lease on {sid}"
                        + (f" ({cur['holder']} does)" if cur else ""))
    return acquire(sid, holder, minutes, note)


def drop(sid: str, holder: str) -> bool:
    """Delete our (or an expired) lease. False when there was none."""
    holder = qualify(holder)
    cur = read_leases().get(sid)
    if not cur:
        return False
    if cur["holder"] != holder and not _expired(cur):
        raise DeskError(f"lease on {sid} is held by {cur['holder']}")
    if not _cas(sid, None, cur["sha"]):
        raise LeaseLost(f"lease on {sid} changed while releasing it")
    return True


# --------------------------------------------------------------------------- statements

def check_statement_body(body: str) -> None:
    body = body.strip()
    if not body:
        raise DeskError("empty statement")
    if len(body) > MAX_STATEMENT_CHARS:
        raise DeskError(f"statement longer than {MAX_STATEMENT_CHARS} characters")
    m = STATEMENT_FORBIDDEN.search(body)
    if m:
        raise DeskError(f"statement contains forbidden token {m.group(0)!r}")
    if re.fullmatch(r"\(?\s*False\s*\)?", body) or re.fullmatch(r"\(?\s*True\s*\)?", body):
        raise DeskError("statement is trivially True/False")


def statement_module(step_id: str) -> str:
    return f"Recon.Statements.S_{step_id}"


def statement_file(step_id: str) -> Path:
    return STATEMENTS / f"S_{step_id}.lean"


def render_statement(step_id: str, title: str, statement_en: str, body: str,
                     extra_imports: list[str]) -> str:
    imports = ["Recon.Basic", *extra_imports]
    en = statement_en.replace("-/", "- /")
    title = title.replace("-/", "- /")
    lines = [*(f"import {m}" for m in imports), "",
             "-- GENERATED by tools/desk.py. TRUSTED. Do not edit by hand.", "",
             "namespace Recon.Statements", "",
             "open SimpleGraph", "",
             f"/-- {step_id}: {title}", "", en, "-/",
             f"def S_{step_id} : Prop :=", f"  {body.strip()}", "",
             f"/-- Negated twin of `S_{step_id}`: proving it refutes the step. -/",
             f"def S_{step_id}_neg : Prop := ¬ S_{step_id}", "",
             "end Recon.Statements", ""]
    return "\n".join(lines)


def build_module(module: str, timeout: int = 1800) -> tuple[bool, str]:
    proc = subprocess.run(["lake", "build", module], cwd=LEAN, capture_output=True,
                          text=True, timeout=timeout)
    out = (proc.stdout + proc.stderr)[-6000:]
    return proc.returncode == 0, out


def write_statement(step_id: str, title: str, statement_en: str, body: str,
                    extra_imports: list[str]) -> tuple[Path, str]:
    """Write and build a statement file. Raises DeskError (and removes the file) on failure."""
    check_statement_body(body)
    for m in extra_imports:
        if not re.fullmatch(r"Recon\.Statements\.S_[a-z0-9_]+", m):
            raise DeskError(f"statements may only import other statements, not {m!r}")
        dep = m.removeprefix("Recon.Statements.S_")
        if not step_path(dep).exists():
            raise DeskError(f"imported statement {m} has no step record")
    path = statement_file(step_id)
    text = render_statement(step_id, title, statement_en, body, extra_imports)
    STATEMENTS.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    ok, out = build_module(statement_module(step_id))
    if not ok:
        path.unlink(missing_ok=True)
        raise DeskError("statement does not elaborate:\n" + out)
    return path, sha256_text(text)


def new_record(step_id: str, program: str, title: str, statement_en: str, body: str,
               author: str, parent: str | None, path: Path, sha: str, imports: list[str]) -> dict:
    return {
        "id": step_id,
        "program": program,
        "title": title,
        "statement_en": statement_en,
        "statement_lean": body.strip(),
        "statement_imports": imports,
        "statement_file": str(path.relative_to(ROOT)),
        "statement_sha256": sha,
        "status": "proposed",
        "author": author,
        "created": now(),
        "parent": parent,
        "is_root": parent is None,
        "human_approved": False,
        "fidelity": [],
        "children": [],
        "reductions": [],
        "negated_twin": f"{step_id}_neg",
        "dead_ends": [],
        "sketches": [],
        "checked": None,
        "refuted": None,
        "priority": 50,
    }


# --------------------------------------------------------------------------- transitions

def mark_checked(target: str, file_rel: str, sha: str, axioms: list[str], actor: str) -> list[str]:
    """Called by gate.py (under lock) after an ACCEPTED verdict. Returns steps closed."""
    sid, neg = base_id(target)
    rec = load(sid)
    info = {"file": file_rel, "sha256": sha, "axioms": axioms, "at": now(), "by": actor,
            "toolchain": (LEAN / "lean-toolchain").read_text().strip(),
            "mathlib_rev": mathlib_rev()}
    rec.pop("lease", None)
    if neg:
        rec["status"] = "refuted"
        rec["refuted"] = info
        event("refuted", sid, actor, file=file_rel)
    else:
        rec["status"] = "checked"
        rec["checked"] = info
        event("checked", sid, actor, file=file_rel)
    save(rec)
    return [sid]


def mathlib_rev() -> str:
    try:
        man = json.loads((LEAN / "lake-manifest.json").read_text())
        for p in man["packages"]:
            if p["name"] == "mathlib":
                return p.get("rev", "?")
    except Exception:
        pass
    return "?"


def record_dead_end(sid: str, approach: str, reason: str, by: str) -> None:
    rec = load(sid)
    rec["dead_ends"].append({"approach": approach, "reason": reason, "by": by, "at": now()})
    save(rec)
    event("dead_end", sid, by, approach=approach, reason=reason)


# --------------------------------------------------------------------------- commands

def cmd_summary(a) -> None:
    steps = all_steps()
    progs = load_programs()
    by_status: dict[str, int] = {}
    for s in steps:
        by_status[s["status"]] = by_status.get(s["status"], 0) + 1
    print("# Desk summary\n")
    print("Status counts:", ", ".join(f"{k}={v}" for k, v in sorted(by_status.items())) or "none")
    print("\n## Programs")
    for p in progs:
        mine = [s for s in steps if s["program"] == p["id"]]
        done = sum(s["status"] in ("checked", "refuted") for s in mine)
        print(f"- {p['id']} [{p.get('status', 'active')}] {p['title']}: {done}/{len(mine)} closed")
        print(f"    mandate: {p['mandate']}")
    try:
        leases = read_leases()
    except DeskError as e:
        leases = {}
        print(f"\n(leases unavailable: {e})")
    print("\n## Open steps (frozen)")
    for s in sorted((s for s in steps if s["status"] == "frozen"),
                    key=lambda s: (-s.get("priority", 50), s["id"])):
        held = live_lease(leases, s["id"])
        lease = ""
        if held:
            lease = f" LEASED by {held['holder']}" + (f" ({held['note']})" if held.get("note")
                                                      else "")
        print(f"- {s['id']} (p{s.get('priority', 50)}){lease}: {s['title']}"
              f"  [dead ends: {len(s['dead_ends'])}, sketches: {len(s['sketches'])}]")
    print("\n## Awaiting fidelity / approval (proposed)")
    for s in steps:
        if s["status"] == "proposed":
            passes = sum(f["verdict"] == "pass" for f in s["fidelity"])
            print(f"- {s['id']}: {s['title']}  [fidelity passes {passes}/"
                  f"{FIDELITY_PASSES_NEEDED}, human_approved={s['human_approved']}]")
    print("\n## Checked / refuted")
    for s in steps:
        if s["status"] in ("checked", "refuted"):
            print(f"- {s['id']} {s['status'].upper()}: {s['title']}")
    if EVENTS.exists():
        print("\n## Last 10 events")
        for line in EVENTS.read_text().splitlines()[-10:]:
            e = json.loads(line)
            print(f"- {e['ts']} {e['kind']} {e.get('step') or ''} by {e['actor']}")


def cmd_status(a) -> None:
    print(json.dumps(load(a.id), indent=2, ensure_ascii=False))


def cmd_list(a) -> None:
    for s in all_steps():
        if a.status and s["status"] != a.status:
            continue
        if a.program and s["program"] != a.program:
            continue
        print(f"{s['id']}\t{s['status']}\t{s['title']}")


def cmd_propose(a) -> None:
    if not STEP_ID.match(a.id) or "_r" in a.id:
        raise DeskError("root step ids look like <program>_<3 digits>, e.g. found_004")
    program = a.id.split("_")[0]
    if program not in {p["id"] for p in load_programs()}:
        raise DeskError(f"unknown program {program!r}; add it with program-add first")
    body = Path(a.lean_file).read_text() if a.lean_file else a.lean
    if body is None:
        raise DeskError("give --lean or --lean-file")
    with locked():
        if step_path(a.id).exists():
            old = load(a.id)
            if not a.replace:
                raise DeskError(f"{a.id} exists; pass --replace to restate a proposed step")
            if old["status"] != "proposed":
                raise DeskError(f"{a.id} is {old['status']}; only proposed steps can be restated")
        path, sha = write_statement(a.id, a.title, a.en, body, a.imports or [])
        rec = new_record(a.id, program, a.title, a.en, body, a.author, None, path, sha,
                         a.imports or [])
        rec["priority"] = a.priority
        save(rec)
        event("proposed", a.id, a.author, title=a.title)
    print(f"proposed {a.id} -> {rec['statement_file']}")


def cmd_fidelity(a) -> None:
    with locked():
        rec = load(a.id)
        if rec["status"] != "proposed":
            raise DeskError(f"{a.id} is {rec['status']}; fidelity reviews apply to proposed steps")
        if a.reviewer == rec["author"]:
            raise DeskError("the author of a statement cannot review its fidelity")
        if any(f["reviewer"] == a.reviewer and f["sha256"] == rec["statement_sha256"]
               for f in rec["fidelity"]):
            raise DeskError(f"{a.reviewer} already reviewed this version")
        notes = Path(a.notes_file).read_text() if a.notes_file else (a.notes or "")
        rec["fidelity"].append({"reviewer": a.reviewer, "verdict": a.verdict, "notes": notes,
                                "sha256": rec["statement_sha256"], "at": now()})
        save(rec)
        event("fidelity", a.id, a.reviewer, verdict=a.verdict)
    print(f"recorded fidelity {a.verdict} for {a.id} by {a.reviewer}")


def cmd_approve(a) -> None:
    # Human-only. tools/hooks/protect.py blocks agents from running this command.
    with locked():
        rec = load(a.id)
        if rec["status"] != "proposed":
            raise DeskError(f"{a.id} is {rec['status']}")
        who = handle()
        if who == "local":
            raise DeskError("set your GitHub handle first: git config recon.handle <handle>")
        rec["human_approved"] = True
        rec["human_approved_sha256"] = rec["statement_sha256"]
        rec["approved_by"] = who
        save(rec)
        event("approved", a.id, f"{who}/human")
    print(f"approved {a.id} (statement sha {rec['statement_sha256'][:12]})")


def freeze_ready(rec: dict) -> str | None:
    """Return None if the step may be frozen, else the reason it may not."""
    if rec["status"] != "proposed":
        return f"status is {rec['status']}"
    current = [f for f in rec["fidelity"] if f["sha256"] == rec["statement_sha256"]]
    if any(f["verdict"] == "fail" for f in current):
        return "a fidelity review of the current statement failed; restate it"
    reviewers = {f["reviewer"] for f in current if f["verdict"] == "pass"}
    if len(reviewers) < FIDELITY_PASSES_NEEDED:
        return f"needs {FIDELITY_PASSES_NEEDED} distinct fidelity passes, has {len(reviewers)}"
    if rec["is_root"] and not (rec["human_approved"]
                               and rec.get("human_approved_sha256") == rec["statement_sha256"]):
        return "root statement needs human approval: python3 tools/desk.py approve " + rec["id"]
    return None


def cmd_freeze(a) -> None:
    with locked():
        rec = load(a.id)
        why = freeze_ready(rec)
        if why:
            raise DeskError(f"cannot freeze {a.id}: {why}")
        if sha256_file(ROOT / rec["statement_file"]) != rec["statement_sha256"]:
            raise DeskError("statement file changed on disk since it was proposed")
        rec["status"] = "frozen"
        rec["frozen_at"] = now()
        save(rec)
        event("frozen", a.id, a.actor)
    print(f"frozen {a.id}")


def cmd_next(a) -> None:
    leases = read_leases()
    cands = [s for s in all_steps() if s["status"] == "frozen" and not live_lease(leases, s["id"])
             and (not a.program or s["program"] == a.program)]
    cands.sort(key=lambda s: (-s.get("priority", 50), len(s["dead_ends"]), s["id"]))
    if not cands:
        print("no open step")
        return
    s = cands[0]
    print(json.dumps({k: s[k] for k in ("id", "title", "statement_en", "statement_lean",
                                         "statement_file", "dead_ends", "sketches")},
                     indent=2, ensure_ascii=False))


def cmd_lease(a) -> None:
    rec = load(a.id)
    if rec["status"] != "frozen":
        raise DeskError(f"{a.id} is {rec['status']}, not frozen")
    info = acquire(a.id, a.holder, a.minutes, a.note)
    event("leased", a.id, info["holder"], minutes=a.minutes, note=a.note)
    print(f"leased {a.id} to {info['holder']} until {info['expires']}")


def cmd_beat(a) -> None:
    info = renew(a.id, a.holder, a.minutes, a.note)
    # heartbeats go to the live view only; the ledger keeps leases, releases and verdicts
    event("beat", a.id, info["holder"], ledger=False, note=a.note, expires=info["expires"])
    print(f"renewed {a.id} for {info['holder']} until {info['expires']}")


def cmd_release(a) -> None:
    holder = qualify(a.holder)
    drop(a.id, holder)
    with locked():
        rec = load(a.id)
        rec.pop("lease", None)
        if a.note:
            rec["dead_ends"].append({"approach": a.note, "reason": a.reason, "by": holder,
                                     "at": now()})
        save(rec)
        event("released", a.id, holder, reason=a.reason, note=a.note)
    print(f"released {a.id} ({a.reason})")


def cmd_leases(a) -> None:
    leases = read_leases()
    if not leases:
        print("no leases")
    for sid, info in sorted(leases.items()):
        state = "expired" if _expired(info) else "live"
        print(f"{sid}\t{state}\t{info['holder']}\tuntil {info['expires']}\t"
              f"{info.get('note', '')}")


def cmd_dead_end(a) -> None:
    with locked():
        record_dead_end(a.id, a.approach, a.reason, a.by)
    print(f"recorded dead end on {a.id}")


def cmd_sketch(a) -> None:
    p = (ROOT / a.path).resolve()
    if not str(p).startswith(str((ROOT / "notes" / "sketches").resolve())):
        raise DeskError("sketches live under notes/sketches/")
    if not p.exists():
        raise DeskError(f"{a.path} does not exist")
    with locked():
        rec = load(a.id)
        rec["sketches"].append({"path": str(p.relative_to(ROOT)), "by": a.by, "at": now(),
                                "survived_refutation": a.survived})
        save(rec)
        event("sketch", a.id, a.by, path=str(p.relative_to(ROOT)))
    print(f"attached sketch to {a.id}")


def cmd_program_add(a) -> None:
    if not re.fullmatch(r"[a-z]+", a.id):
        raise DeskError("program ids are lower-case letters only")
    with locked():
        progs = load_programs()
        if any(p["id"] == a.id for p in progs):
            raise DeskError(f"program {a.id} exists")
        progs.append({"id": a.id, "title": a.title, "mandate": a.mandate, "status": "active",
                      "created": now()})
        save_programs(progs)
        event("program_added", None, a.actor, program=a.id)
    print(f"added program {a.id}")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="desk.py", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("summary").set_defaults(fn=cmd_summary)
    p = sub.add_parser("status"); p.add_argument("id"); p.set_defaults(fn=cmd_status)
    p = sub.add_parser("list"); p.add_argument("--status"); p.add_argument("--program")
    p.set_defaults(fn=cmd_list)

    p = sub.add_parser("propose")
    p.add_argument("id"); p.add_argument("--title", required=True)
    p.add_argument("--en", required=True, help="the statement in plain English")
    p.add_argument("--lean", help="the Lean Prop body")
    p.add_argument("--lean-file", help="file holding the Lean Prop body")
    p.add_argument("--imports", nargs="*", help="other Recon.Statements.S_* modules to import")
    p.add_argument("--author", required=True)
    p.add_argument("--priority", type=int, default=50)
    p.add_argument("--replace", action="store_true")
    p.set_defaults(fn=cmd_propose)

    p = sub.add_parser("fidelity")
    p.add_argument("id"); p.add_argument("--reviewer", required=True)
    p.add_argument("--verdict", choices=("pass", "fail"), required=True)
    p.add_argument("--notes"); p.add_argument("--notes-file")
    p.set_defaults(fn=cmd_fidelity)

    p = sub.add_parser("approve"); p.add_argument("id"); p.set_defaults(fn=cmd_approve)
    p = sub.add_parser("freeze"); p.add_argument("id")
    p.add_argument("--actor", default="desk"); p.set_defaults(fn=cmd_freeze)
    p = sub.add_parser("next"); p.add_argument("--program"); p.set_defaults(fn=cmd_next)

    for name, fn in (("lease", cmd_lease), ("beat", cmd_beat)):
        p = sub.add_parser(name); p.add_argument("id"); p.add_argument("--holder", required=True)
        p.add_argument("--minutes", type=int, default=120)
        p.add_argument("--note", help="what the holder is doing now (shown live)")
        p.set_defaults(fn=fn)
    sub.add_parser("leases").set_defaults(fn=cmd_leases)

    p = sub.add_parser("release"); p.add_argument("id"); p.add_argument("--holder", required=True)
    p.add_argument("--reason", choices=RELEASE_REASONS, required=True); p.add_argument("--note")
    p.set_defaults(fn=cmd_release)

    p = sub.add_parser("dead-end"); p.add_argument("id")
    p.add_argument("--approach", required=True); p.add_argument("--reason", required=True)
    p.add_argument("--by", required=True); p.set_defaults(fn=cmd_dead_end)

    p = sub.add_parser("sketch"); p.add_argument("id"); p.add_argument("--path", required=True)
    p.add_argument("--by", required=True)
    p.add_argument("--survived", action="store_true", help="survived the refutation pass")
    p.set_defaults(fn=cmd_sketch)

    p = sub.add_parser("program-add"); p.add_argument("id"); p.add_argument("--title", required=True)
    p.add_argument("--mandate", required=True); p.add_argument("--actor", default="human")
    p.set_defaults(fn=cmd_program_add)

    a = ap.parse_args(argv)
    try:
        a.fn(a)
    except DeskError as e:
        print(f"desk: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
