#!/usr/bin/env python3
"""SubagentStart / SubagentStop hook: tell the live view that an agent of this machine's fleet
started or stopped. Never blocks: always exits 0, the POST runs with a short timeout."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
import live  # noqa: E402


def main() -> None:
    try:
        data = json.load(sys.stdin)
    except Exception:
        return
    event = data.get("hook_event_name", "")
    kind = {"SubagentStart": "agent_start", "SubagentStop": "agent_stop"}.get(event)
    if not kind:
        return
    handle = subprocess.run(["git", "config", "recon.handle"], cwd=TOOLS, capture_output=True,
                            text=True).stdout.strip() or "local"
    agent_type = data.get("agent_type") or data.get("subagent_type") or "agent"
    live.emit(kind, None, f"{handle}/{agent_type}", wait=True, agent_type=agent_type,
              agent_id=data.get("agent_id") or data.get("session_id"))


if __name__ == "__main__":
    try:
        main()
    finally:
        sys.exit(0)
