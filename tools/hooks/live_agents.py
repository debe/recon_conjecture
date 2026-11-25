#!/usr/bin/env python3
"""SubagentStart / SubagentStop hook: tell the live view that an agent of this machine's fleet
started or stopped, with its label, step and workflow phase. Never blocks: always exits 0.

Claude Code writes each subagent's `agent-<id>.meta.json` (description = the workflow label,
for example `builder:kelly_edge_sum:b1`) about two seconds after SubagentStart fires. So the
start hook hands the event to a detached child that waits for that file and then posts; the
stop hook reads it directly. The description, phase and workflow id are all the page gets: no
prompt text, no paths."""
from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[1]
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))
import live  # noqa: E402

META_WAIT = 30.0   # seconds the detached child waits for the meta file


def meta_path(data: dict) -> Path | None:
    tp, sid, aid = data.get("transcript_path"), data.get("session_id"), data.get("agent_id")
    if not (tp and sid and aid):
        return None
    hits = sorted((Path(tp).parent / sid / "subagents").glob(f"**/agent-{aid}.meta.json"))
    return hits[0] if hits else None


def info(data: dict) -> dict:
    """Label, step, phase and workflow run of the agent, from its meta file (best effort)."""
    p = meta_path(data)
    if not p:
        return {}
    try:
        meta = json.loads(p.read_text())
    except (OSError, ValueError):
        return {}
    desc = str(meta.get("description") or "")
    step = next((seg for seg in desc.split(":")
                 if seg and (ROOT / "ledger" / "steps" / f"{seg}.json").exists()), None)
    wf = p.parent.name if p.parent.name.startswith("wf_") else None
    return {"label": desc, "step": step, "phase": meta.get("workflowPhase"), "workflow": wf}


def post(kind: str, data: dict, extra: dict) -> None:
    handle = subprocess.run(["git", "config", "recon.handle"], cwd=TOOLS, capture_output=True,
                            text=True).stdout.strip() or "local"
    agent_type = data.get("agent_type") or data.get("subagent_type") or "agent"
    step = extra.pop("step", None)
    live.emit(kind, step, f"{handle}/{agent_type}", wait=True, agent_type=agent_type,
              agent_id=data.get("agent_id") or data.get("session_id"), **extra)


def start_after_meta(raw: str) -> None:
    data = json.loads(raw)
    deadline = time.monotonic() + META_WAIT
    while meta_path(data) is None and time.monotonic() < deadline:
        time.sleep(0.25)
    post("agent_start", data, info(data))


def main() -> None:
    if len(sys.argv) == 3 and sys.argv[1] == "--start-after-meta":
        start_after_meta(sys.argv[2])
        return
    try:
        data = json.load(sys.stdin)
    except Exception:
        return
    event = data.get("hook_event_name", "")
    if event == "SubagentStart":
        subprocess.Popen([sys.executable, __file__, "--start-after-meta", json.dumps(data)],
                         stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                         stderr=subprocess.DEVNULL, start_new_session=True)
    elif event == "SubagentStop":
        post("agent_stop", data, info(data))


if __name__ == "__main__":
    try:
        main()
    finally:
        sys.exit(0)
