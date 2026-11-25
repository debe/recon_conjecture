# Fleet setup: todo

## Phase 1: single machine (done)
- [x] git init, .gitignore
- [x] Lean project: Lean v4.36.0 + Mathlib v4.36.0, cache downloaded
- [x] `Recon/Basic.lean`: card, Hypomorphic, Reconstructible, Recognizable, ClassReconstructible, ReconstructionConjecture + 4 anchors (compiles)
- [x] `tools/desk.py`, `tools/gate.py`, `tools/audit.py`, `tools/search/small_graphs.py`
- [x] `tools/hooks/protect.py` + `.claude/settings.json`
- [x] agents (6) and workflows (7); CLAUDE.md
- [x] seed programs; propose found_001
- [x] first commit, pushed to github.com/debe/recon_conjecture

## Phase 2: two humans, two fleets (branch `debe/collab`, PR #1)
- [x] CI tracer: `.github/workflows/gate.yml` (policy + `audit.py --clean` + tool tests) green on GitHub
- [x] `tools/ci_policy.py` + tests (append-only, trusted-change label, maintainer approval from base, event log, leases, assembly)
- [x] leases as compare-and-swap refs `refs/leases/<id>` (tests: race has one winner, takeover, renew, release; verified against GitHub)
- [x] handle identity (`git config recon.handle`), `approved_by`, union merge for `ledger/events.jsonl`
- [x] hook: precise redirect check (no more `2>&1` false positives), maintainer-only actions (labels, merge, push to main), new trusted paths
- [x] small_graphs: individualise-and-refine canonical form (Petersen 60 s+ → 8 ms; 549 MB → 47 MB), geng for n ≤ 10
- [x] relay (Rust, zero-copy SSE fan-out, token auth) + unit tests + local end-to-end test
- [x] `tools/live.py` emitter; desk/gate/CI/subagent hook emit events
- [x] canvas page `site/` + `tools/snapshot.py` + `pages.yml` (tested headless at desktop and phone width)
- [x] docs: CLAUDE.md §1/4/5/7/9/11/12, CONTRIBUTING.md, relay/README.md
- [ ] human: run `relay/bootstrap.sh` (tokens, GitHub secret, DNS, TLS, deploy)
- [ ] human: enable Pages (source: GitHub Actions), branch protection on main, merge PR #1
- [ ] human: invite Michael (needs his handle), add him to maintainers, send relay token, borg ticket
- [ ] two-party smoke run on found_001 (second clone with `recon.handle=sim`)

## Review
- CI on GitHub: Mathlib cache fetch works on hosted runners (77 GB free), policy and audit pass, tool tests (incl. Lean compile tests) pass in about 2 minutes.
- First CI run failed: an empty `lean/Recon/Checked/` is not tracked by git, and lake's glob needs the directory (fixed with `.gitkeep`).
- The auto-mode classifier refused writing secrets to GitHub and the production server from the agent; those steps are in `relay/bootstrap.sh` for a human to run.
