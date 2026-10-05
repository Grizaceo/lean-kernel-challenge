#!/usr/bin/env python3
"""Tabulate the live LKC leaderboard + our standing (read-only).

Usage: python3 lk_board.py [--full]
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lk_playground  # noqa: E402
from lk_playground import curl  # noqa: E402

lk_playground.BASE = "https://api.sair.foundation"
COMP = "/api/public/v1/competitions/lean-kernel-challenge"
PROBLEMS = ["fib", "mertens", "primecount", "partition", "permanent", "polydisc", "ca-rule110", "sha256"]


def leaderboard():
    d = curl("GET", f"{COMP}/leaderboard")
    if not d.get("ok"):
        raise SystemExit(json.dumps(d)[:400])
    return d["data"]


def main():
    full = "--full" in sys.argv
    lb = leaderboard()
    problems = lb.get("problems", lb)

    mine = curl("GET", f"{COMP}/submissions/mine")
    ours = {}
    if mine.get("ok"):
        for s in mine["data"]["items"]:
            rep = (s.get("dailyEvaluation") or {}).get("replayReport") or {}
            ours.setdefault(s["problem"], []).append(
                (s["submissionId"], int(rep.get("computationTotal") or 0),
                 rep.get("eligible"), s.get("status")))

    print(f"rankingContract={lb.get('rankingContract')}  "
          f"metric={lb.get('metric')}")
    for p in PROBLEMS:
        blk = problems.get(p, {})
        ranked = blk.get("ranked", [])
        print(f"\n=== {p}  ({len(ranked)} ranked) ===")
        for i, r in enumerate(ranked[: (99 if full else 5)], 1):
            mark = ""
            for sid, tot, elig, st in ours.get(p, []):
                if tot == int(r["computationTotal"]):
                    mark = "   <-- NOSOTROS"
            print(f"  {i:3}. {int(r['computationTotal']):>16,}  "
                  f"cov={r.get('coverage', {}).get('completed')}/"
                  f"{r.get('coverage', {}).get('planned')}  "
                  f"team={str(r.get('teamName') or r.get('teamId'))[:28]}{mark}")
        for p2 in PROBLEMS:
            if p2 != p:
                continue
        for sid, tot, elig, st in ours.get(p, []):
            pos = next((i for i, r in enumerate(ranked, 1)
                        if int(r["computationTotal"]) == tot), None)
            print(f"  >>> our submission {sid}: computationTotal={tot:,} "
                  f"eligible={elig} status={st} rank={pos}/{len(ranked)}")
        tail = ranked[5:] if not full else []
        if tail:
            print(f"  ... +{len(tail)} more; worst={int(ranked[-1]['computationTotal']):,}")


if __name__ == "__main__":
    main()