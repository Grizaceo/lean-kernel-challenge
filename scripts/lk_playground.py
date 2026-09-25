#!/usr/bin/env python3
"""SAIR Lean Kernel Playground client.

Usage:
  python3 lk_playground.py submit-run <problem> <path-to-Submission.lean> <name>
  python3 lk_playground.py poll <runId>
  python3 lk_playground.py limits
  python3 lk_playground.py history
  python3 lk_playground.py runs

Reads SAIR_KEY from ~/.hermes/workspace/ACTIVE/SAIR/igp24/.env
"""
import json
import sys
import uuid
from pathlib import Path

import requests

ENV_PATH = Path.home() / ".hermes/workspace/ACTIVE/SAIR/igp24/.env"
BASE = "https://api.sair.foundation/api/public/v1/competitions/lean-kernel-challenge/playground"


def get_key():
    for line in ENV_PATH.read_text().splitlines():
        l = line.strip()
        if l.startswith("export "):
            l = l[7:]
        if l.startswith("SAIR_KEY="):
            return l.partition("=")[2].strip().strip('"').strip("'")
    raise SystemExit("SAIR_KEY not found in " + str(ENV_PATH))


def headers():
    return {"Authorization": f"Bearer {get_key()}"}


def submit_run(problem, src_path, name):
    src = Path(src_path).read_text()
    payload = {
        "problemId": problem,
        "name": name,
        "files": {"Submission.lean": src},
    }
    r = requests.post(f"{BASE}/solutions", json=payload, headers=headers(), timeout=60)
    r.raise_for_status()
    sol = r.json()["data"]
    print(f"solution: {sol['solutionId']} rev {sol['revision']}")

    run_body = {
        "solutionId": sol["solutionId"],
        "revision": sol["revision"],
        "idempotencyKey": f"playground-run:{uuid.uuid4()}",
    }
    r2 = requests.post(f"{BASE}/runs", json=run_body, headers=headers(), timeout=60)
    r2.raise_for_status()
    run = r2.json()["data"]
    print(f"run: {run['runId']} status={run['status']}")
    return run["runId"]


def poll(run_id, wait=True, timeout_s=600, interval=15):
    import time
    start = time.time()
    while True:
        r = requests.get(f"{BASE}/runs/{run_id}", headers=headers(), timeout=30)
        d = r.json()["data"]
        status = d.get("status")
        if status == "done" or not wait:
            return d
        if time.time() - start > timeout_s:
            print("timeout waiting", file=sys.stderr)
            return d
        time.sleep(interval)


def print_result(d):
    print(f"run {d['runId']} [{d['problemId']}] verdict={d.get('verdict')} conclusion={d.get('finalConclusion')}")
    m = d.get("metrics") or {}
    if m:
        print(f"  mode={m.get('mode')} median={m.get('instructionMedian')} @ n={m.get('headlineN')} cpu={m.get('timingExecutorCpu')}")
        for s in m.get("slots", []):
            print(f"  {s['caseId']:8} input={s['input']:>10} instr={int(s['instructions']):>14,} wall={s['wallTimeMs']}ms mem={int(s['peakMemoryBytes'])/1e6:.0f}MB")
    if d.get("reasonCode"):
        print(f"  REJECTED: {d.get('reasonCode')} — {d.get('reasonMessage')}")
        if d.get("logExcerpt"):
            print(f"  log: {d['logExcerpt'][:500]}")


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "limits"
    if cmd == "submit-run":
        run_id = submit_run(sys.argv[2], sys.argv[3], sys.argv[4])
        d = poll(run_id)
        print_result(d)
    elif cmd == "poll":
        d = poll(sys.argv[2], wait=False)
        print_result(d)
    elif cmd == "limits":
        for p in ["fib","mertens","primecount","partition","permanent","polydisc","ca-rule110","sha256"]:
            r = requests.get(f"{BASE}/run-limits?problem={p}", headers=headers(), timeout=30)
            d = r.json()["data"]
            std = d.get("standard", {})
            print(f"{p:12} std {std.get('used',0)}/{std.get('dailyLimit',0)} remaining={std.get('remaining')} | light remaining={d.get('light',{}).get('remaining')}")
    elif cmd == "history":
        r = requests.get(f"{BASE}/run-history", headers=headers(), timeout=30)
        for it in r.json()["data"]["items"]:
            m = it.get("metrics") or {}
            print(f"{it['runId']:4} {it['problemId']:13} {it.get('verdict'):10} median={m.get('instructionMedian')}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
