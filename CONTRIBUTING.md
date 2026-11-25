# Joining the fleet

You run your own Claude Code fleet on your own machine. Results reach the shared library
through pull requests that CI re-verifies from scratch, so nothing about your machine has to
be trusted. Read `CLAUDE.md` first; it is the operating manual your agents follow too.

## One-time setup

1. **Access.** A maintainer adds you as a collaborator (write access: you push branches and
   lease refs; `main` takes PRs only).
2. **Clone and fetch Mathlib** (about 7 GB, a few minutes):
   ```sh
   git clone https://github.com/debe/recon_conjecture && cd recon_conjecture
   cd lean && lake exe cache get && lake build Recon && cd ..
   python3 -m pip install networkx pytest
   ```
3. **Identity.** Your GitHub handle names your leases and your approvals:
   ```sh
   git config recon.handle <your-github-handle>
   ```
   To approve root statements, a maintainer adds your handle to `.github/maintainers.txt`
   (a `trusted-change` PR).
4. **Live view (optional).** Ask a maintainer for a publisher token and save it:
   ```sh
   mkdir -p ~/.config/recon && chmod 700 ~/.config/recon
   (umask 077; printf %s '<token>' > ~/.config/recon/live.token)
   python3 tools/live.py ping
   ```
   The maintainer adds the token's SHA-256 to the relay (`relay/README.md`).
5. **Borg (optional).** Install borg, then join the `recon` team collective with the
   ticket a maintainer sends you:
   ```sh
   borg mesh join <ticket> --paths ~/path/to/recon_conjecture --apply
   borg service install
   ```
6. **nauty (optional).** `sudo apt install nauty` makes small-graph searches exhaustive up
   to n = 10.

## A round

```sh
git switch main && git pull
claude            # "run a campaign round", or work on one step; see CLAUDE.md §9
```

The fleet ships its own results with `python3 tools/ship.py "<title>"`: audit, branch,
commit, PR, wait for CI, merge on green. CI on the PR is the verdict, and branch protection
on `main` lets nothing else in. A PR that changes trusted files needs the `trusted-change`
label from a maintainer; until then CI fails and ship stops and says so.

## Tests

`python3 -m pytest tools/tests -q` (about 4 minutes: the gate tests compile Lean).
