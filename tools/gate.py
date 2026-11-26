#!/usr/bin/env python3
"""The gate: the only judge of what counts as "checked".

  gate.py precheck <target> <file>     every check, records nothing (use while iterating)
  gate.py check <target> <file>        official verdict; ACCEPTED promotes the file to
                                       lean/Recon/Checked/ and closes the step in the ledger
  gate.py check-reduction <bundle.json>  kernel-check a reduction  S_c1 -> ... -> S_parent,
                                       then create the children as frozen steps
  gate.py assemble <id>                close a reduced parent whose children are all checked

<target> is a step id (prove the step) or <id>_neg (prove the negated twin = refute it).

Verdict line (last line of output): ACCEPTED | REJECTED: <reason> | FAULT: <reason>
Exit codes: 0 accepted, 1 rejected, 2 fault.

What the gate guarantees for an ACCEPTED file:
  1. lexical rules (no sorry/axiom/native_decide/meta-programming/notation/instances...)
  2. shape: helpers in `namespace Recon.Checked.L_<target>`, last declaration is
     `theorem Recon.Checked.L_<target> : Recon.Statements.S_<target>`
  3. the module builds with the pinned toolchain and Mathlib
  4. an independent wrapper file, importing the frozen statement separately, typechecks
     `example : Recon.Statements.S_<target> := Recon.Checked.L_<target>`
  5. `#print axioms` lists nothing beyond propext, Classical.choice, Quot.sound
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import desk  # noqa: E402

ROOT, LEAN, CHECKED, STATEMENTS = desk.ROOT, desk.LEAN, desk.CHECKED, desk.STATEMENTS
GATE_DIR = LEAN / ".gate"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ALLOWED_OPTIONS = {"maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats",
                   "synthInstance.maxSize"}
MAX_BYTES = 512 * 1024
BUILD_TIMEOUT = 45 * 60
LEAN_TIMEOUT = 20 * 60

FORBIDDEN_WORDS = [
    "sorry", "admit", "axiom", "axioms", "native_decide", "implemented_by", "extern", "unsafe",
    "opaque", "macro", "macro_rules", "syntax", "elab", "elab_rules", "notation", "infix",
    "infixl", "infixr", "prefix", "postfix", "initialize", "builtin_initialize", "run_cmd",
    "run_tac", "run_elab", "run_meta", "attribute", "scoped", "export", "structure", "inductive",
    "class", "mutual", "partial", "declare_syntax_cat", "register_option", "local_notation",
    "omit", "include", "deriving", "ofReduceBool", "trustCompiler", "_root_",
]
FORBIDDEN_RE = [
    (re.compile(r"\b(" + "|".join(map(re.escape, FORBIDDEN_WORDS)) + r")\b"), "forbidden word"),
    (re.compile(r"#[a-zA-Z_]"), "`#` command or `#` notation"),
    (re.compile(r"\""), "double quote / string literal"),
    (re.compile(r"\bLean\.(Elab|Meta|Parser|Compiler|IR|Environment)\b"), "meta-programming"),
    (re.compile(r"\bopen\s+(Lean|Elab|Meta)\b"), "meta-programming"),
    (re.compile(r"(?<!local )\binstance\b"), "global instance (use `local instance` or none)"),
    (re.compile(r"@\[\s*(?!simp\]|local simp\])"), "attribute other than @[simp]/@[local simp]"),
    (re.compile(r"\$\{|\bdecreasing_by\b.*\bsorry\b"), "suspicious construct"),
]


class Rejected(Exception):
    pass


class Fault(Exception):
    pass


class _DryRunDone(Exception):
    pass


# --------------------------------------------------------------------------- helpers

def run(cmd: list[str], timeout: int) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, cwd=LEAN, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        raise Rejected(f"timeout after {timeout}s: {' '.join(cmd)}")
    except OSError as e:
        raise Fault(str(e))
    return p.returncode, (p.stdout + p.stderr)


def tail(text: str, n: int = 4000) -> str:
    return text[-n:]


def module_of(path: Path) -> str:
    rel = path.resolve().relative_to(LEAN.resolve()).with_suffix("")
    return ".".join(rel.parts)


def checked_modules() -> set[str]:
    mods = set()
    for s in desk.all_steps():
        for key in ("checked", "refuted"):
            if s.get(key):
                mods.add(module_of(ROOT / s[key]["file"]))
        for red in s.get("reductions", []):
            if red.get("status") == "checked":
                mods.add(module_of(ROOT / red["file"]))
    return mods


def strip_header(text: str) -> tuple[list[str], str]:
    """Split the file into its leading import lines and the rest."""
    lines = text.split("\n")
    imports, i = [], 0
    while i < len(lines) and (lines[i].startswith("import ") or not lines[i].strip()):
        if lines[i].strip():
            m = re.fullmatch(r"import ([A-Za-z0-9_.]+)", lines[i].strip())
            if not m:
                raise Rejected(f"malformed import line: {lines[i]!r}")
            imports.append(m.group(1))
        i += 1
    return imports, "\n".join(lines[i:])


# --------------------------------------------------------------------------- the rules

def lexical_check(text: str, decl: str, statement_modules: set[str]) -> None:
    if len(text.encode("utf-8")) > MAX_BYTES:
        raise Rejected("file larger than 512 KiB")
    if "\r" in text or "\t" in text:
        raise Rejected("tabs or carriage returns in file")
    imports, body = strip_header(text)
    if not imports:
        raise Rejected("no imports")
    if re.search(r"\bimport\b", body):
        raise Rejected("`import` after the header")
    ok_checked = checked_modules()
    for m in imports:
        if m == "Mathlib" or m.startswith("Mathlib."):
            continue
        if m == "Recon.Basic" or m in statement_modules:
            continue
        if m.startswith("Recon.Statements.S_"):
            dep = m.removeprefix("Recon.Statements.S_").removesuffix("_neg")
            if desk.step_path(dep).exists():
                continue
        if m in ok_checked:
            continue
        raise Rejected(f"import not allowed: {m} (only Mathlib, Recon.Basic, statements, "
                       f"and already-checked Recon.Checked modules)")
    for rx, what in FORBIDDEN_RE:
        mm = rx.search(body)
        if mm:
            line = body[: mm.start()].count("\n") + len(imports) + 1
            raise Rejected(f"{what}: {mm.group(0)!r} near line {line}")
    for mm in re.finditer(r"set_option\s+([A-Za-z.]+)", body):
        if mm.group(1) not in ALLOWED_OPTIONS:
            raise Rejected(f"set_option {mm.group(1)} not allowed")
    shape_check(body, decl)


DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(theorem|lemma|def|abbrev|example|local instance)\b\s*([^\s:({\[]*)", re.M)


def shape_check(body: str, decl: str) -> None:
    """Helpers inside `namespace <decl>`, final theorem `<decl>` last, at top level."""
    stack: list[str] = []
    final_seen = False
    top_level_ok = re.compile(r"^(open\s|set_option\s|--|/-|\s|$)")
    in_block_comment = False
    for raw in body.split("\n"):
        line = raw.rstrip()
        if in_block_comment:
            if "-/" in line:
                in_block_comment = False
            continue
        if line.lstrip().startswith("/-") and "-/" not in line:
            in_block_comment = True
            continue
        m = re.match(r"^(namespace|section)\s+(\S+)\s*$", line)
        if m:
            if final_seen:
                raise Rejected("nothing may follow the final theorem")
            if m.group(1) == "section":
                raise Rejected("use `namespace`, not `section`")
            name = m.group(2)
            full = ".".join(stack + [name]) if stack else name
            if not stack and not (full == decl or full.startswith(decl + ".")
                                  or full == decl + "_aux"):
                raise Rejected(f"helpers must live in `namespace {decl}`, found `{full}`")
            stack.append(name)
            continue
        m = re.match(r"^end(\s+(\S+))?\s*$", line)
        if m:
            if not stack:
                raise Rejected("`end` without an open namespace")
            if m.group(2) != stack[-1]:
                raise Rejected(f"`end` must name what it closes (`end {stack[-1]}`)")
            stack.pop()
            continue
        if re.match(r"^\s*(namespace|section|end)\b", line):
            raise Rejected("`namespace`/`section`/`end` must start at column 0")
        if stack:
            continue
        # top level
        d = DECL_RE.match(line)
        if d:
            kind, name = d.group(1), d.group(2)
            if kind == "theorem" and name == decl:
                if final_seen:
                    raise Rejected("final theorem declared twice")
                final_seen = True
                continue
            raise Rejected(f"top-level `{kind} {name}` outside `namespace {decl}`")
        if final_seen:
            continue  # the final theorem's proof body
        if line and not top_level_ok.match(line):
            raise Rejected(f"unexpected top-level line: {line[:80]!r}")
    if stack:
        raise Rejected(f"unclosed namespace {stack[-1]}")
    if not final_seen:
        raise Rejected(f"no final `theorem {decl} : ...`")
    stmt = decl.replace("Recon.Checked.L_", "Recon.Statements.S_").replace(
        "Recon.Checked.R_", "")
    if decl.startswith("Recon.Checked.L_"):
        if not re.search(rf"^theorem {re.escape(decl)}\s*:\s*{re.escape(stmt)}\s*:=",
                         body, re.M):
            raise Rejected(f"final theorem must read `theorem {decl} : {stmt} :=` on one line")


def axioms_of(output: str, decl: str) -> list[str]:
    if f"'{decl}' does not depend on any axioms" in output:
        return []
    m = re.search(rf"'{re.escape(decl)}' depends on axioms: \[([^\]]*)\]", output, re.S)
    if not m:
        raise Fault("could not read `#print axioms` output:\n" + tail(output, 1500))
    return [a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()]


def wrapper_check(imports: list[str], expected_type: str, decl: str) -> list[str]:
    """Elaborate the claim in a fresh file whose statement imports are independent."""
    GATE_DIR.mkdir(exist_ok=True)
    w = GATE_DIR / "Wrapper.lean"
    w.write_text("\n".join([*(f"import {m}" for m in imports), "",
                            f"example : {expected_type} := {decl}", "",
                            f"#print axioms {decl}", ""]))
    code, out = run(["lake", "env", "lean", str(w)], LEAN_TIMEOUT)
    if code != 0 or re.search(r"(^|\n)[^\n]*error", out):
        raise Rejected("wrapper does not typecheck against the frozen statement:\n" + tail(out))
    axioms = axioms_of(out, decl)
    bad = sorted(set(axioms) - ALLOWED_AXIOMS)
    if bad:
        raise Rejected(f"uses axioms outside the standard three: {bad}")
    return axioms


def precheck_file(text: str, decl: str, expected_type: str, stmt_modules: set[str]) -> list[str]:
    """Full check without touching Checked/: lexical + compile a temp copy + axioms."""
    lexical_check(text, decl, stmt_modules)
    GATE_DIR.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=GATE_DIR, delete=False) as fh:
        fh.write(text.rstrip("\n") + "\n\n"
                 f"example : {expected_type} := {decl}\n\n#print axioms {decl}\n")
        tmp = Path(fh.name)
    try:
        code, out = run(["lake", "env", "lean", str(tmp)], LEAN_TIMEOUT)
    finally:
        tmp.unlink(missing_ok=True)
    if code != 0:
        raise Rejected("does not elaborate:\n" + tail(out))
    axioms = axioms_of(out, decl)
    bad = sorted(set(axioms) - ALLOWED_AXIOMS)
    if bad:
        raise Rejected(f"uses axioms outside the standard three: {bad}")
    return axioms


def remove_build_outputs(module: str) -> None:
    rel = Path(*module.split("."))
    for d in (LEAN / ".lake" / "build" / "lib" / "lean", LEAN / ".lake" / "build" / "ir"):
        for f in d.glob(str(rel) + ".*"):
            f.unlink(missing_ok=True)


def promote_and_build(text: str, dest: Path, decl: str, expected_type: str,
                      stmt_imports: list[str]) -> list[str]:
    """Copy into Checked/, lake build it, run the independent wrapper. Roll back on failure."""
    if dest.exists():
        raise Rejected(f"{dest.relative_to(ROOT)} already exists (step already closed?)")
    dest.write_text(text)
    module = module_of(dest)
    try:
        code, out = run(["lake", "build", module], BUILD_TIMEOUT)
        if code != 0:
            raise Rejected("lake build failed:\n" + tail(out))
        return wrapper_check([*stmt_imports, module], expected_type, decl)
    except BaseException:
        dest.unlink(missing_ok=True)
        remove_build_outputs(module)
        raise


# --------------------------------------------------------------------------- commands

def target_info(target: str) -> tuple[dict, str, str, str, Path]:
    sid, neg = desk.base_id(target)
    rec = desk.load(sid)
    if rec["status"] != "frozen":
        raise Rejected(f"step {sid} is {rec['status']}, not frozen (only frozen steps are open)")
    if desk.sha256_file(ROOT / rec["statement_file"]) != rec["statement_sha256"]:
        raise Fault(f"statement file of {sid} differs from its recorded hash; run audit.py")
    decl = f"Recon.Checked.L_{target}"
    expected = f"Recon.Statements.S_{target}"
    smod = desk.statement_module(sid)
    return rec, decl, expected, smod, CHECKED / f"L_{target}.lean"


def cmd_precheck(target: str, file: str) -> list[str]:
    rec, decl, expected, smod, _ = target_info(target)
    return precheck_file(Path(file).read_text(), decl, expected, {smod})


def cmd_check(target: str, file: str, actor: str) -> list[str]:
    text = Path(file).read_text()
    with desk.locked():
        rec, decl, expected, smod, dest = target_info(target)
        sid = rec["id"]
        try:
            lexical_check(text, decl, {smod})
            axioms = promote_and_build(text, dest, decl, expected, [smod])
        except Rejected as e:
            desk.event("verdict", sid, actor, target=target, verdict="REJECTED",
                       reason=str(e)[:500])
            raise
        rel = str(dest.relative_to(ROOT))
        desk.event("verdict", sid, actor, target=target, verdict="ACCEPTED", file=rel)
        desk.mark_checked(target, rel, desk.sha256_file(dest), axioms, actor)
        if not target.endswith("_neg"):
            cascade_assemble(rec, actor)
        else:
            cascade_refutation(rec, actor)
    return axioms


def cmd_check_reduction(bundle_path: str, actor: str, dry: bool = False) -> list[str]:
    """Bundle JSON:
    {"parent": "kelly_degree_sequence", "by": "label",
     "children": [{"slug": "edge_count", "title": "...", "statement_en": "...",
                   "statement_lean": "..."}, ...],
     "proof_file": "lean/Recon/Scratch/kelly_degree_sequence/r1.lean"}
    Each child's id is <parent>__<slug>, its slug a snake_case name for what it claims. The
    proof file proves `theorem Recon.Checked.R_<parent>_r<k> :
        Recon.Statements.S_<child1> → ... → Recon.Statements.S_<parent>`, where k numbers the
    parent's reduction attempts (run `gate.py next-reduction <parent>`).
    """
    b = json.loads(Path(bundle_path).read_text())
    parent = b["parent"]
    with desk.locked():
        rec = desk.load(parent)
        if rec["status"] != "frozen":
            raise Rejected(f"parent {parent} is {rec['status']}, not frozen")
        k = len(rec.get("reductions", [])) + 1
        kids = b["children"]
        if not 2 <= len(kids) <= 4:
            raise Rejected("a reduction has 2 to 4 children")
        try:
            ids = [desk.child_id(parent, c.get("slug", "")) for c in kids]
        except desk.DeskError as e:
            raise Rejected(str(e))
        if len(set(ids)) != len(ids):
            raise Rejected("two children share a slug")
        taken = [i for i in ids if desk.step_path(i).exists()]
        if taken:
            raise Rejected(f"step ids already exist: {', '.join(taken)}; pick other slugs")
        bodies = [c["statement_lean"].strip() for c in kids]
        if len(set(bodies)) != len(bodies):
            raise Rejected("duplicate children")
        norm = lambda s: re.sub(r"\s+", " ", s).strip()
        for c in bodies:
            if norm(c) == norm(rec["statement_lean"]):
                raise Rejected("a child restates the parent")
            if re.search(rf"\bS_{re.escape(parent)}\b", c):
                raise Rejected("a child refers to the parent statement")
            if len(c) > desk.MAX_STATEMENT_CHARS:
                raise Rejected(f"a child statement is longer than {desk.MAX_STATEMENT_CHARS} "
                               "characters")
        written: list[Path] = []
        try:
            shas = []
            for cid, c in zip(ids, kids):
                try:
                    path, sha = desk.write_statement(cid, c["title"], c["statement_en"],
                                                     c["statement_lean"],
                                                     c.get("imports", []))
                except desk.DeskError as e:
                    raise Rejected(f"child {cid}: {e}")
                written.append(path)
                shas.append(sha)
            rname = f"R_{parent}_r{k}"
            decl = f"Recon.Checked.{rname}"
            expected = " → ".join([*(f"Recon.Statements.S_{c}" for c in ids),
                                   f"Recon.Statements.S_{parent}"])
            text = (ROOT / b["proof_file"]).read_text()
            smods = {desk.statement_module(parent), *(desk.statement_module(c) for c in ids)}
            lexical_check(text, decl, smods)
            if not re.search(rf"^theorem {re.escape(decl)}\s*:", text, re.M):
                raise Rejected(f"final theorem must be `theorem {decl} : {expected} :=`")
            dest = CHECKED / f"{rname}.lean"
            axioms = promote_and_build(text, dest, decl, expected, sorted(smods))
            if dry:
                dest.unlink(missing_ok=True)
                remove_build_outputs(module_of(dest))
                raise _DryRunDone()
        except _DryRunDone:
            for p in written:
                p.unlink(missing_ok=True)
                remove_build_outputs(module_of(p))
            return ids
        except BaseException as e:
            for p in written:
                p.unlink(missing_ok=True)
                remove_build_outputs(module_of(p))
            if isinstance(e, Rejected):
                desk.event("verdict", parent, actor, target=f"R_{parent}_r{k}",
                           verdict="REJECTED", reason=str(e)[:500])
            raise
        for cid, c, path, sha in zip(ids, kids, written, shas):
            child = desk.new_record(cid, rec["program"], c["title"], c["statement_en"],
                                    c["statement_lean"], b.get("by", actor), parent, path, sha,
                                    c.get("imports", []))
            child["status"] = "frozen"  # safe: the implication is kernel-checked
            child["frozen_at"] = desk.now()
            child["priority"] = rec.get("priority", 50)
            desk.save(child)
            desk.event("frozen", cid, actor, via=f"reduction {rname}")
        rel = str(dest.relative_to(ROOT))
        rec.setdefault("reductions", []).append(
            {"name": rname, "file": rel, "children": ids, "status": "checked",
             "sha256": desk.sha256_file(dest), "axioms": axioms, "at": desk.now(), "by": actor})
        rec["children"] = sorted(set(rec["children"]) | set(ids))
        rec["status"] = "reduced"
        rec.pop("lease", None)
        desk.save(rec)
        desk.event("reduced", parent, actor, reduction=rname, children=ids)
    return ids


def cascade_assemble(child_rec: dict, actor: str) -> None:
    """After a step is checked, close every reduced ancestor whose reduction is complete."""
    parent_id = child_rec.get("parent")
    while parent_id:
        parent = desk.load(parent_id)
        if parent["status"] != "reduced":
            return
        done = None
        for red in parent["reductions"]:
            if red["status"] != "checked":
                continue
            if all(desk.load(c)["status"] == "checked" for c in red["children"]):
                done = red
                break
        if not done:
            return
        assemble(parent, done, actor)
        parent_id = parent.get("parent")


def assemble(parent: dict, red: dict, actor: str) -> None:
    pid = parent["id"]
    decl = f"Recon.Checked.L_{pid}"
    kids = red["children"]
    imports = ["Mathlib", desk.statement_module(pid), f"Recon.Checked.{red['name']}",
               *(f"Recon.Checked.L_{c}" for c in kids)]
    text = "\n".join([*(f"import {m}" for m in imports), "",
                      f"theorem {decl} : Recon.Statements.S_{pid} :=",
                      f"  Recon.Checked.{red['name']} "
                      + " ".join(f"Recon.Checked.L_{c}" for c in kids), ""])
    dest = CHECKED / f"L_{pid}.lean"
    # The step is 'reduced', not 'frozen'; temporarily treat it as open for the build.
    lexical_check(text, decl, {desk.statement_module(pid)})
    axioms = promote_and_build(text, dest, decl, f"Recon.Statements.S_{pid}",
                               [desk.statement_module(pid)])
    rel = str(dest.relative_to(ROOT))
    desk.event("verdict", pid, actor, target=pid, verdict="ACCEPTED", file=rel,
               via=f"assembly of {red['name']}")
    desk.mark_checked(pid, rel, desk.sha256_file(dest), axioms, actor)


def cascade_refutation(rec: dict, actor: str) -> None:
    """A refuted child kills the reductions that used it; the parent re-opens."""
    parent_id = rec.get("parent")
    if not parent_id:
        return
    parent = desk.load(parent_id)
    changed = False
    for red in parent.get("reductions", []):
        if rec["id"] in red["children"] and red["status"] == "checked":
            red["status"] = "dead"
            changed = True
            for c in red["children"]:
                crec = desk.load(c)
                if crec["status"] == "frozen":
                    crec["status"] = "withdrawn"
                    desk.save(crec)
            parent["dead_ends"].append({"approach": f"reduction {red['name']}",
                                        "reason": f"child {rec['id']} refuted", "by": actor,
                                        "at": desk.now()})
    if changed and parent["status"] == "reduced" and not any(
            r["status"] == "checked" for r in parent["reductions"]):
        parent["status"] = "frozen"
    if changed:
        desk.save(parent)
        desk.event("reduction_dead", parent_id, actor, refuted_child=rec["id"])


def main(argv: list[str]) -> int:
    import argparse
    ap = argparse.ArgumentParser(prog="gate.py", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("precheck", "check"):
        p = sub.add_parser(name); p.add_argument("target"); p.add_argument("file")
        p.add_argument("--actor", default="agent")
    p = sub.add_parser("check-reduction"); p.add_argument("bundle")
    p.add_argument("--actor", default="agent")
    p.add_argument("--dry", action="store_true", help="check everything, record nothing")
    p = sub.add_parser("next-reduction"); p.add_argument("parent")
    p = sub.add_parser("assemble"); p.add_argument("id"); p.add_argument("--actor", default="gate")
    a = ap.parse_args(argv)
    try:
        if a.cmd == "precheck":
            sid = desk.base_id(a.target)[0]
            try:
                axioms = cmd_precheck(a.target, a.file)
            except Rejected as e:
                first = next((ln for ln in str(e).splitlines() if ln.strip()), "")
                desk.event("precheck", sid, a.actor, ledger=False, target=a.target, ok=False,
                           reason=first)
                raise
            desk.event("precheck", sid, a.actor, ledger=False, target=a.target, ok=True)
            print(f"precheck ok, axioms: {axioms}")
            print("PRECHECK PASSED (not recorded; run `gate.py check` for the verdict)")
            return 0
        if a.cmd == "check":
            axioms = cmd_check(a.target, a.file, a.actor)
            print(f"axioms: {axioms}")
            print("ACCEPTED")
            return 0
        if a.cmd == "check-reduction":
            ids = cmd_check_reduction(a.bundle, a.actor, a.dry)
            if a.dry:
                print(f"dry run ok, children would be: {ids}")
                print("PRECHECK PASSED (not recorded; rerun without --dry)")
                return 0
            print(f"children frozen: {ids}")
            print("ACCEPTED")
            return 0
        if a.cmd == "next-reduction":
            rec = desk.load(a.parent)
            k = len(rec.get("reductions", [])) + 1
            print(json.dumps({"theorem": f"Recon.Checked.R_{a.parent}_r{k}",
                              "child_id": f"{a.parent}__<slug>",
                              "slug": "snake_case name for what the child claims, starting "
                                      "with a letter; set it as \"slug\" on each bundle child",
                              "type": "Recon.Statements.S_<child 1> → ... → "
                                      f"Recon.Statements.S_{a.parent}",
                              "imports": [desk.statement_module(a.parent),
                                          f"Recon.Statements.S_{a.parent}__<slug> per child"]},
                             indent=2))
            return 0
        if a.cmd == "assemble":
            with desk.locked():
                cascade_assemble({"parent": a.id}, a.actor)
            print("ACCEPTED")
            return 0
    except Rejected as e:
        print(f"REJECTED: {e}")
        return 1
    except (Fault, desk.DeskError) as e:
        print(f"FAULT: {e}")
        return 2
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
