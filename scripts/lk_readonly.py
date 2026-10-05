#!/usr/bin/env python3
"""Read-only SAIR Lean Kernel API queries.

Reuses `lk_playground.get_key`/`curl` so the SAIR key is never placed on a
command line, never printed, and never written to a file.

Every command here is a GET. Nothing in this file mutates server state.

Usage:
  python3 lk_readonly.py leaderboard [problem]
  python3 lk_readonly.py mine
  python3 lk_readonly.py solutions <problem>
  python3 lk_readonly.py spec
  python3 lk_readonly.py runs [limit]
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lk_playground  # noqa: E402
from lk_playground import curl  # noqa: E402

COMP = "/api/public/v1/competitions/lean-kernel-challenge"

# lk_playground.curl hardcodes the *playground* base; the competitive endpoints
# (leaderboard, submissions) live one level up. Rebind it for this process only.
lk_playground.BASE = "https://api.sair.foundation"


def show(obj, limit=4000):
    print(json.dumps(obj, indent=1)[:limit])


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "leaderboard"
    if cmd == "leaderboard":
        path = f"{COMP}/leaderboard"
        if len(sys.argv) > 2:
            path += f"?problem={sys.argv[2]}"
        show(curl("GET", path), 12000)
    elif cmd == "mine":
        show(curl("GET", f"{COMP}/submissions/mine"), 8000)
    elif cmd == "solutions":
        show(curl("GET", f"{COMP}/playground/solutions?problem={sys.argv[2]}"), 12000)
    elif cmd == "spec":
        show(curl("GET", f"{COMP}/submission-spec"), 4000)
    elif cmd == "runs":
        lim = sys.argv[2] if len(sys.argv) > 2 else "40"
        show(curl("GET", f"{COMP}/playground/runs?limit={lim}"), 20000)
    else:
        print(__doc__)


if __name__ == "__main__":
    main()