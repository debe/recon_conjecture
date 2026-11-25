"""Adversarial tests for the gate.

The ledger is redirected to a temp dir. Statement and Checked files are real (Lean must import
them) and use the reserved program `gatetest`; they are removed afterwards.

Run: python3 -m pytest tools/tests -q        (slow tests compile Lean; about 2-5 minutes)
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import desk  # noqa: E402
import gate  # noqa: E402

S1 = "gatetest_add_zero"
S2 = "gatetest_add_zero_both"      # S1 is a prefix of S2: renames must not touch S2
S1_RENAMED = "gatetest_zero_right"
KIDS = [f"{S2}__right", f"{S2}__left"]
DECL = f"Recon.Checked.L_{S1}"
STMT = f"Recon.Statements.S_{S1}"

GOOD = f"""import Mathlib
import Recon.Statements.S_{S1}

namespace {DECL}
lemma helper (n : ℕ) : n + 0 = n := rfl
end {DECL}

theorem {DECL} : {STMT} :=
  fun n => {DECL}.helper n
"""


def variant(body_helper: str = "lemma helper (n : ℕ) : n + 0 = n := rfl",
            final: str = f"theorem {DECL} : {STMT} :=\n  fun n => {DECL}.helper n",
            imports: str = f"import Mathlib\nimport Recon.Statements.S_{S1}") -> str:
    return f"{imports}\n\nnamespace {DECL}\n{body_helper}\nend {DECL}\n\n{final}\n"


def _cleanup_lean(ids: list[str]) -> None:
    for sid in ids:
        for p in (desk.statement_file(sid), gate.CHECKED / f"L_{sid}.lean",
                  gate.CHECKED / f"L_{sid}_neg.lean"):
            if p.exists():
                gate.remove_build_outputs(gate.module_of(p))
                p.unlink()
    for p in gate.CHECKED.glob("R_gatetest_*.lean"):
        gate.remove_build_outputs(gate.module_of(p))
        p.unlink()


@pytest.fixture(scope="module", autouse=True)
def quiet_identity():
    """Tests approve as a fixed handle and never publish live events."""
    import os
    saved = {k: os.environ.get(k) for k in ("RECON_HANDLE", "RECON_LIVE", "RECON_LEASES")}
    os.environ.update(RECON_HANDLE="tester", RECON_LIVE="off", RECON_LEASES="local")
    yield
    for k, v in saved.items():
        if v is None:
            os.environ.pop(k, None)
        else:
            os.environ[k] = v


@pytest.fixture(scope="module")
def ledger(tmp_path_factory):
    tmp = tmp_path_factory.mktemp("ledger")
    saved = {k: getattr(desk, k) for k in ("LEDGER", "STEPS", "EVENTS", "PROGRAMS", "LOCK")}
    desk.LEDGER, desk.STEPS = tmp, tmp / "steps"
    desk.EVENTS, desk.PROGRAMS, desk.LOCK = tmp / "events.jsonl", tmp / "programs.json", tmp / ".lock"
    ids = [S1, S2, S1_RENAMED, *KIDS]
    _cleanup_lean(ids)
    assert desk.main(["program-add", "gatetest", "--title", "t", "--mandate", "tests"]) == 0
    for sid, body in ((S1, "∀ n : ℕ, n + 0 = n"), (S2, "∀ n : ℕ, n + 0 = n ∧ 0 + n = n")):
        assert desk.main(["propose", sid, "--title", "t", "--en", "test", "--lean", body,
                          "--author", "tester"]) == 0
        for r in ("rev-a", "rev-b"):
            assert desk.main(["fidelity", sid, "--reviewer", r, "--verdict", "pass"]) == 0
        assert desk.main(["approve", sid]) == 0
        assert desk.main(["freeze", sid]) == 0
    yield tmp
    _cleanup_lean(ids)
    for k, v in saved.items():
        setattr(desk, k, v)


# ---------------------------------------------------------------- desk rules (fast)

def test_author_cannot_review(ledger):
    assert desk.main(["propose", "gatetest_self_review", "--title", "t", "--en", "e",
                      "--lean", "∀ n : ℕ, n = n", "--author", "alice"]) == 0
    assert desk.main(["fidelity", "gatetest_self_review", "--reviewer", "alice", "--verdict", "pass"]) == 1
    desk.statement_file("gatetest_self_review").unlink()


def test_root_needs_human_approval(ledger):
    assert desk.main(["propose", "gatetest_needs_approval", "--title", "t", "--en", "e",
                      "--lean", "∀ n : ℕ, n = n + 0", "--author", "alice"]) == 0
    for r in ("rev-a", "rev-b"):
        desk.main(["fidelity", "gatetest_needs_approval", "--reviewer", r, "--verdict", "pass"])
    assert desk.main(["freeze", "gatetest_needs_approval"]) == 1
    desk.statement_file("gatetest_needs_approval").unlink()


@pytest.mark.parametrize("sid", ["gatetest_001", "gatetest", "gatetest_Foo", "gatetest__x",
                                 "gatetest_x_neg", "gatetest_9lives", "Gatetest_x"])
def test_ids_name_claims_not_counters(ledger, sid):
    assert desk.main(["propose", sid, "--title", "t", "--en", "e",
                      "--lean", "∀ n : ℕ, n = n", "--author", "alice"]) == 1
    assert not desk.step_path(sid).exists()


@pytest.mark.parametrize("slug", ["", "1a", "a__b", "x_neg", "neg", "Edge"])
def test_child_slugs_rejected(slug):
    with pytest.raises(desk.DeskError):
        desk.child_id("p_x", slug)


def test_child_id():
    assert desk.child_id("kelly_degree_sequence", "edge_count") == "kelly_degree_sequence__edge_count"


@pytest.mark.parametrize("body", ["False", "sorry", "by native_decide", "\"x\" = \"x\"",
                                  "True -- comment"])
def test_statement_body_rules(body):
    with pytest.raises(desk.DeskError):
        desk.check_statement_body(body)


# ---------------------------------------------------------------- lexical / shape (fast)

BAD = {
    "sorry": variant(body_helper="lemma helper (n : ℕ) : n + 0 = n := by sorry"),
    "axiom": variant(body_helper="axiom helper (n : ℕ) : n + 0 = n"),
    "native_decide": variant(body_helper="lemma helper (n : ℕ) : n + 0 = n := by native_decide"),
    "eval": variant(body_helper="lemma helper (n : ℕ) : n + 0 = n := rfl\n#eval 1"),
    "global instance": variant(body_helper="instance : Inhabited ℕ := ⟨0⟩\n"
                                           "lemma helper (n : ℕ) : n + 0 = n := rfl"),
    "macro": variant(body_helper="macro x:term : term => x\n"
                                 "lemma helper (n : ℕ) : n + 0 = n := rfl"),
    "root escape": variant(body_helper="def _root_.Recon.Foo : Prop := True\n"
                                       "lemma helper (n : ℕ) : n + 0 = n := rfl"),
    "scratch import": variant(imports=f"import Mathlib\nimport Recon.Statements.S_{S1}\n"
                                      f"import Recon.Scratch.{S1}.b1"),
    "weaker statement": variant(final=f"theorem {DECL} : ∀ n : ℕ, n = n :=\n  fun n => rfl"),
    "helper outside namespace": f"import Mathlib\nimport Recon.Statements.S_{S1}\n\n"
                                f"lemma helper (n : ℕ) : n + 0 = n := rfl\n\n"
                                f"theorem {DECL} : {STMT} :=\n  fun n => helper n\n",
    "wrong end": GOOD.replace(f"end {DECL}", "end"),
    "attribute": variant(body_helper="@[reducible] def helper2 := 1\n"
                                     "lemma helper (n : ℕ) : n + 0 = n := rfl"),
    "set_option": variant(body_helper="set_option debug.skipKernelTC true in\n"
                                      "lemma helper (n : ℕ) : n + 0 = n := rfl"),
    "trailing code": GOOD + "\nnamespace Foo\nend Foo\n",
}


@pytest.mark.parametrize("name", sorted(BAD))
def test_lexical_rejects(ledger, name):
    with pytest.raises(gate.Rejected):
        gate.lexical_check(BAD[name], DECL, {f"Recon.Statements.S_{S1}"})


def test_lexical_accepts_good(ledger):
    gate.lexical_check(GOOD, DECL, {f"Recon.Statements.S_{S1}"})


# ---------------------------------------------------------------- full Lean runs (slow)

def write(tmp_path: Path, name: str, text: str) -> str:
    p = tmp_path / name
    p.write_text(text)
    return str(p)


def test_precheck_rejects_ill_typed(ledger, tmp_path):
    bad = variant(body_helper="lemma helper (n : ℕ) : n + 0 = n + 1 := rfl")
    with pytest.raises(gate.Rejected):
        gate.cmd_precheck(S1, write(tmp_path, "bad.lean", bad))


def test_check_accepts_and_closes(ledger, tmp_path):
    axioms = gate.cmd_check(S1, write(tmp_path, "good.lean", GOOD), "tester")
    assert set(axioms) <= gate.ALLOWED_AXIOMS
    rec = desk.load(S1)
    assert rec["status"] == "checked"
    assert (gate.CHECKED / f"L_{S1}.lean").exists()
    # a second proof of a closed step is refused
    with pytest.raises(gate.Rejected):
        gate.cmd_check(S1, write(tmp_path, "good2.lean", GOOD), "tester")


def test_rename_moves_a_checked_step(ledger):
    old_sha = desk.load(S1)["statement_sha256"]
    s2_text = desk.statement_file(S2).read_text()
    assert desk.main(["rename", S1, S1_RENAMED]) == 0
    rec = desk.load(S1_RENAMED)
    assert rec["status"] == "checked" and rec["renamed_from"] == S1
    assert rec["negated_twin"] == f"{S1_RENAMED}_neg"
    assert rec["human_approved_sha256"] == rec["statement_sha256"] != old_sha   # carried over
    assert all(f["sha256"] == rec["statement_sha256"] for f in rec["fidelity"])
    assert not desk.step_path(S1).exists() and not desk.statement_file(S1).exists()
    assert not (gate.CHECKED / f"L_{S1}.lean").exists()
    proof = gate.CHECKED / f"L_{S1_RENAMED}.lean"
    assert rec["checked"]["file"].endswith(f"L_{S1_RENAMED}.lean")
    assert rec["checked"]["sha256"] == desk.sha256_file(proof)
    assert S1 not in proof.read_text()
    assert f"S_{S1_RENAMED}_neg" in desk.statement_file(S1_RENAMED).read_text()
    assert desk.statement_file(S2).read_text() == s2_text         # the prefix sibling is untouched
    assert desk.main(["rename", S1_RENAMED, "kelly_zero_right"]) == 1   # keeps its program


def test_reduction_then_assembly(ledger, tmp_path):
    a, b = KIDS
    proof = f"""import Mathlib
import Recon.Statements.S_{S2}
import Recon.Statements.S_{a}
import Recon.Statements.S_{b}

theorem Recon.Checked.R_{S2}_r1 : Recon.Statements.S_{a} → Recon.Statements.S_{b} → Recon.Statements.S_{S2} :=
  fun ha hb n => ⟨ha n, hb n⟩
"""
    import json
    bundle = {"parent": S2, "by": "tester", "proof_file": write(tmp_path, "r1.lean", proof),
              "children": [
                  {"slug": "right", "title": "a", "statement_en": "n+0=n",
                   "statement_lean": "∀ n : ℕ, n + 0 = n"},
                  {"slug": "left", "title": "b", "statement_en": "0+n=n",
                   "statement_lean": "∀ n : ℕ, 0 + n = n"}]}
    bpath = write(tmp_path, "bundle.json", json.dumps(bundle))
    assert gate.cmd_check_reduction(bpath, "tester", dry=True) == KIDS
    assert not desk.statement_file(a).exists()  # dry run leaves nothing
    unnamed = {**bundle, "children": [{k: v for k, v in c.items() if k != "slug"}
                                      for c in bundle["children"]]}
    with pytest.raises(gate.Rejected):
        gate.cmd_check_reduction(write(tmp_path, "unnamed.json", json.dumps(unnamed)), "tester", dry=True)
    ids = gate.cmd_check_reduction(bpath, "tester")
    assert desk.load(S2)["status"] == "reduced"
    for cid, prf in zip(ids, ("Nat.add_zero n", "Nat.zero_add n")):
        d = f"Recon.Checked.L_{cid}"
        text = (f"import Mathlib\nimport Recon.Statements.S_{cid}\n\n"
                f"theorem {d} : Recon.Statements.S_{cid} :=\n  fun n => {prf}\n")
        gate.cmd_check(cid, write(tmp_path, f"{cid}.lean", text), "tester")
    assert desk.load(S2)["status"] == "checked"  # assembled automatically
    assert (gate.CHECKED / f"L_{S2}.lean").exists()
