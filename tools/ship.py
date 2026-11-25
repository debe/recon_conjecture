#!/usr/bin/env python3
"""Ship the fleet's work: branch, commit, pull request, wait for CI, merge.

Pull requests are the orchestration. An agent ships its own results, and CI on the PR is the
judge. Branch protection on main requires the `gate` check on a branch that is up to date with
main, so a merge lands only what CI verified against the current main. A PR that touches
trusted files still needs a maintainer's `trusted-change` label: without it CI fails, and ship
stops and says so.

  ship.py "found_002 checked: degree sequence recognizable"   commit, open the PR, merge on green
  ship.py --no-merge "..."                                     stop once CI is green
  ship.py                                                      on a branch with an open PR: wait, merge

Only the fleet's outputs are committed (ledger/, lean/Recon/{Checked,Statements}/, notes/),
after `audit.py` passes. `--all` commits every change instead (for work on the tooling).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import live  # noqa: E402

OUTPUTS = ["ledger", "lean/Recon/Checked", "lean/Recon/Statements", "notes"]
CHECK = "gate"
POLL = 15            # seconds between CI polls
CI_TIMEOUT = 45 * 60  # a clean audit of a large library takes a while
MAX_UPDATES = 5      # rounds of "main moved, update the branch, wait for CI again"


class ShipError(Exception):
    pass


def sh(*cmd: str, check: bool = True, env: dict | None = None) -> str:
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, env=env)
    if check and r.returncode != 0:
        raise ShipError(f"{' '.join(cmd[:3])} failed: {(r.stderr or r.stdout).strip()}")
    return r.stdout.strip()


def git(*args: str, check: bool = True) -> str:
    return sh("git", *args, check=check)


def handle() -> str:
    h = os.environ.get("RECON_HANDLE") or git("config", "recon.handle", check=False)
    if not h:
        raise ShipError("set your GitHub handle: git config recon.handle <handle>")
    return h


def repo_slug() -> str:
    url = git("remote", "get-url", "origin")
    m = re.search(r"github\.com[:/](.+?/.+?)(?:\.git)?$", url)
    if not m:
        raise ShipError(f"origin is not a GitHub repository: {url}")
    return m.group(1)


class GitHub:
    def __init__(self, repo: str, user: str):
        token = os.environ.get("GH_TOKEN") or sh("gh", "auth", "token", "--user", user, check=False) \
            or sh("gh", "auth", "token")
        self.env = {**os.environ, "GH_TOKEN": token}
        self.repo = repo

    def api(self, path: str, method: str = "GET", **fields) -> dict | list:
        cmd = ["gh", "api", "-X", method, f"repos/{self.repo}/{path}"]
        for k, v in fields.items():
            cmd += ["-F" if isinstance(v, bool) else "-f", f"{k}={str(v).lower() if isinstance(v, bool) else v}"]
        out = sh(*cmd, env=self.env)
        return json.loads(out) if out else {}


def slug(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")[:40].rstrip("-") or "work"


def commit(title: str, everything: bool) -> None:
    outputs = ["--", *[p for p in OUTPUTS if (ROOT / p).exists()]]
    if not git("status", "--porcelain", *([] if everything else outputs)):
        return
    # The library is audited locally only when it changed; CI audits everything from scratch anyway.
    if git("status", "--porcelain", *outputs):
        audit = subprocess.run([sys.executable, "tools/audit.py"], cwd=ROOT, capture_output=True, text=True)
        if audit.returncode != 0 or "AUDIT PASSED" not in audit.stdout:
            raise ShipError("audit.py did not pass; nothing committed:\n" + audit.stdout[-2000:] + audit.stderr[-1000:])
    if not title:
        raise ShipError("there are changes to commit: give a title, e.g. ship.py \"found_002 checked: ...\"")
    branch = git("branch", "--show-current")
    if branch in ("", "main"):
        branch = f"{handle()}/{slug(title)}-{time.strftime('%m%d%H%M')}"
        git("switch", "-c", branch)
    git("add", *(["-A"] if everything else outputs))
    git("commit", "-q", "-m", title)
    print(f"committed on {branch}: {title}")


def open_pr(gh: GitHub, branch: str, title: str, body: str) -> dict:
    owner = gh.repo.split("/")[0]
    found = gh.api(f"pulls?head={owner}:{branch}&state=open")
    if found:
        return found[0]
    pr = gh.api("pulls", "POST", title=title or git("log", "-1", "--format=%s"), head=branch, base="main",
                body=body or "Shipped by the fleet with `tools/ship.py`. CI on this PR is the verdict.")
    live.emit("pr_opened", actor=f"{handle()}/ship", pr=pr["number"], url=pr["html_url"], title=pr["title"])
    return pr


def latest_run(gh: GitHub, sha: str) -> dict | None:
    runs = gh.api(f"commits/{sha}/check-runs?check_name={CHECK}").get("check_runs", [])
    return max(runs, key=lambda r: r["id"]) if runs else None   # the newest run wins


def wait_ci(gh: GitHub, sha: str, after_id: int = 0, timeout: int = CI_TIMEOUT) -> dict | None:
    """The newest completed gate run on `sha` with an id above `after_id`, or None on timeout."""
    deadline = time.time() + timeout
    while time.time() < deadline:
        run = latest_run(gh, sha)
        if run and run["id"] > after_id and run["status"] == "completed":
            return run
        time.sleep(POLL)
    return None


def failure_report(gh: GitHub, run: dict, pr: dict) -> str:
    m = re.search(r"/actions/runs/(\d+)", run.get("details_url") or "")
    log = sh("gh", "run", "view", m.group(1), "--repo", gh.repo, "--log-failed", check=False, env=gh.env) if m else ""
    tail = "\n".join(line.split("\t")[-1] for line in log.splitlines()[-25:])
    hint = ""
    if "trusted-change" in log:
        hint = "\nThis PR changes trusted files: a maintainer must add the `trusted-change` label, then run ship.py again."
    elif "gate.py assemble" in log:
        hint = "\nRun the `gate.py assemble <id>` that CI names, then ship.py again."
    return f"CI {run['conclusion']} on PR #{pr['number']}: {run.get('details_url', '')}\n{tail}{hint}"


def settle(gh: GitHub, number: int) -> dict:
    """GitHub computes mergeability in the background; wait until it has an answer."""
    for _ in range(20):
        pr = gh.api(f"pulls/{number}")
        if pr.get("mergeable_state") not in (None, "unknown"):
            return pr
        time.sleep(3)
    return pr


def ship(gh: GitHub, pr: dict, merge: bool) -> int:
    number = pr["number"]
    print(f"PR #{number}: {pr['html_url']}")
    for _ in range(MAX_UPDATES):
        sha = gh.api(f"pulls/{number}")["head"]["sha"]
        print(f"waiting for CI ({CHECK}) on {sha[:7]} ...", flush=True)
        last = latest_run(gh, sha)
        if last and last["status"] == "completed" and last["conclusion"] != "success":
            # Shipping again after a failure: only a newer run (after a label, or a re-run) can
            # change the verdict, so wait a while for one before repeating the old report.
            print("the last CI run failed; waiting for a newer one (after a label or a re-run)", flush=True)
            run = wait_ci(gh, sha, after_id=last["id"], timeout=10 * 60) or last
        else:
            run = wait_ci(gh, sha)
        if run is None:
            raise ShipError(f"CI did not finish within {CI_TIMEOUT // 60} minutes on {sha[:7]}")
        if run["conclusion"] != "success":
            raise ShipError(failure_report(gh, run, pr))
        print("CI green")
        if not merge:
            return 0
        pr = settle(gh, number)
        state = pr.get("mergeable_state")
        if state == "behind":
            print("main moved on: updating the branch and waiting for CI again")
            gh.api(f"pulls/{number}/update-branch", "PUT", expected_head_sha=sha)
            for _ in range(20):
                time.sleep(3)
                if gh.api(f"pulls/{number}")["head"]["sha"] != sha:
                    break
            continue
        if state == "dirty":
            raise ShipError(f"PR #{number} conflicts with main: `git pull --no-rebase origin main`, resolve, "
                            "run audit.py, push, then ship.py again")
        gh.api(f"pulls/{number}/merge", "PUT", merge_method="merge", sha=sha)
        print(f"merged PR #{number}")
        return 0
    raise ShipError(f"main kept moving: gave up after {MAX_UPDATES} updates of PR #{number}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("title", nargs="?", default="", help="commit message and PR title")
    ap.add_argument("--body", default="", help="PR description")
    ap.add_argument("--no-merge", action="store_true", help="stop once CI is green")
    ap.add_argument("--all", action="store_true", help="commit every change, not only the fleet's outputs")
    a = ap.parse_args()
    try:
        gh = GitHub(repo_slug(), handle())
        commit(a.title, a.all)
        branch = git("branch", "--show-current")
        if branch in ("", "main"):
            raise ShipError("nothing to ship: no changes, and not on a work branch")
        git("push", "-q", "-u", "origin", "HEAD")
        rc = ship(gh, open_pr(gh, branch, a.title, a.body), merge=not a.no_merge)
        if rc == 0 and not a.no_merge:
            git("switch", "-q", "main")
            git("pull", "-q", "--ff-only")
            git("branch", "-D", branch, check=False)
            print("main is up to date")
        return rc
    except ShipError as e:
        print(f"ship: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
