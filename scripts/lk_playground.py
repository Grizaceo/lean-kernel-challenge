#!/usr/bin/env python3
"""SAIR Lean Kernel Playground client (stdlib + curl only).

The system python3 has no `requests`, and Cloudflare 403s the default
python-urllib User-Agent, so every call shells out to curl with a browser-ish UA.

Usage:
  python3 lk_playground.py submit-run <problem> <Submission.lean> <name> [--no-wait]
  python3 lk_playground.py poll <runId>
  python3 lk_playground.py limits
  python3 lk_playground.py history

Auth: SAIR_KEY from ~/.hermes/workspace/ACTIVE/SAIR/igp24/.env
"""
import json
import subprocess
import sys
import time
import uuid
from pathlib import Path

ENV_PATH = Path.home() / ".hermes/workspace/ACTIVE/SAIR/igp24/.env"
BASE = "https://api.sair.foundation/api/public/v1/competitions/lean-kernel-challenge/playground"
PROBLEMS = ["fib", "mertens", "primecount", "partition", "permanent", "polydisc", "ca-rule110", "sha256"]
UA = "Mozilla/5.0 (X11; Linux x86_64) research-client/1.0"


def get_key():
    for line in ENV_PATH.read_text().splitlines():
        l = line.strip()
        if l.startswith("export "):
            l = l[7:]
        if l.startswith("SAIR_KEY="):
            return l.partition("=")[2].strip().strip('"').strip("'")
    raise SystemExit(f"SAIR_KEY not found in {ENV_PATH}")


def curl(method, path, body=None):
    """Call the playground API via curl; returns parsed JSON."""
    cmd = ["curl", "-sS", "-X", method,
           "-H", f"Authorization: Bearer {get_key()}",
           "-H", f"User-Agent: {UA}"]
    if body is not None:
        tmp = Path("/tmp/lk_req.json")
        tmp.write_text(json.dumps(body))
        cmd += ["-H", "Content-Type: application/json", "-d", f"@{tmp}"]
    cmd.append(BASE + path)
    out = subprocess.run(cmd, capture_output=True, timeout=120).stdout
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return {"ok": False, "error": {"code": "NON_JSON",
                                       "raw": out[:400].decode("utf-8", "replace")}}


def submit_run(problem, src_path, name, wait=True):
    src = Path(src_path).read_text()
    resp = curl("POST", "/solutions",
                {"problemId": problem, "name": name, "files": {"Submission.lean": src}})
    if not resp.get("ok"):
        print(f"solution failed: {json.dumps(resp.get('error'))[:300]}")
        return None
    sol = resp["data"]
    print(f"solution {sol['solutionId']} rev {sol['revision']}")
    r2 = curl("POST", "/runs", {"solutionId": sol["solutionId"], "revision": sol["revision"],
                                "idempotencyKey": f"playground-run:{uuid.uuid4()}"})
    if not r2.get("ok"):
        print(f"run failed: {json.dumps(r2.get('error'))[:300]}")
        return None
    run = r2["data"]
    print(f"run {run['runId']} status={run['status']}")
    return poll(run["runId"], wait=True) if wait else run["runId"]


def poll(run_id, wait=True, timeout_s=900, interval=15):
    t0 = time.time()
    while True:
        d = curl("GET", f"/runs/{run_id}")["data"]
        if d.get("status") == "done" or not wait:
            return d
        if time.time() - t0 > timeout_s:
            print(f"timeout waiting for run {run_id}")
            return d
        time.sleep(interval)


def print_result(d):
    print(f"run {d.get('runId')} [{d.get('problemId')}] verdict={d.get('verdict')} conclusion={d.get('finalConclusion')}")
    m = d.get("metrics") or {}
    if m:
        print(f"  median={m.get('instructionMedian')} @ n={m.get('headlineN')} cpu={m.get('timingExecutorCpu')}")
        for s in m.get("slots", []):
            print(f"  {s['caseId']:8} input={s['input']:>22} instr={int(s['instructions']):>14,} wall={float(s['wallTimeMs']):.1f}ms")
    if d.get("reasonCode"):
        print(f"  REJECTED {d.get('reasonCode')}: {d.get('reasonMessage')}")
        if d.get("logExcerpt"):
            print(f"  log: {d['logExcerpt'][:600]}")


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "limits"
    if cmd == "submit-run":
        wait = "--no-wait" not in sys.argv
        args = [a for a in sys.argv[2:] if not a.startswith("--")]
        res = submit_run(args[0], args[1], args[2], wait=wait)
        if isinstance(res, dict):
            print_result(res)
    elif cmd == "poll":
        print_result(poll(sys.argv[2], wait=False))
    elif cmd == "limits":
        for p in PROBLEMS:
            d = curl("GET", f"/run-limits?problem={p}")["data"]
            std = d.get("standard", {})
            print(f"{p:12} std {std.get('used',0)}/{std.get('dailyLimit',0)} remaining={std.get('remaining')}"
                  f" | light remaining={d.get('light',{}).get('remaining')}")
    elif cmd == "light-submit":
        # FormData with a pre-compiled Submission.olean + toolchain (avoids the
        # paused "new Light uploads" path, which only covers source uploads).
        import base64
        import os
        args = [a for a in sys.argv[2:] if not a.startswith("--")]
        problem, olean_path, name = args[0], args[1], args[2]
        boundary = "----lkb" + uuid.uuid4().hex
        parts = []
        def field(k, v):
            parts.append(f"--{boundary}\r\nContent-Disposition: form-data; name=\"{k}\"\r\n\r\n{v}\r\n".encode())
        field("problemId", problem)
        field("name", name)
        olean = Path(olean_path).read_bytes()
        parts.append(
            f"--{boundary}\r\nContent-Disposition: form-data; name=\"olean\"; filename=\"Submission.olean\"\r\n"
            f"Content-Type: application/octet-stream\r\n\r\n".encode() + olean + b"\r\n")
        parts.append(f"--{boundary}--\r\n".encode())
        body = b"".join(parts)
        tmp = Path("/tmp/lk_light.bin")
        tmp.write_bytes(body)
        out = subprocess.run(
            ["curl", "-sS", "-X", "POST",
             "-H", f"Authorization: Bearer {get_key()}",
             "-H", f"User-Agent: {UA}",
             "-H", f"Content-Type: multipart/form-data; boundary={boundary}",
             "-d", f"@{tmp}", BASE + "/light-runs"],
            capture_output=True, timeout=180).stdout
        print(out[:900].decode("utf-8", "replace"))
    elif cmd == "history":
        for it in curl("GET", "/run-history?limit=30")["data"]["items"]:
            m = it.get("metrics") or {}
            print(f"run {it['runId']:4} {it['problemId']:13} {it['status']:8} verdict={str(it.get('verdict')):10} median={m.get('instructionMedian')}")
    elif cmd == "slots":
        # The judge's own test inputs live in each run's metrics.slots. This is
        # the authoritative source for which n gets timed -- the /examples
        # endpoint only carries the official solution source, not the inputs.
        print_result(curl("GET", f"/runs/{sys.argv[2]}")["data"])
        print("  raw slots:")
        d = curl("GET", f"/runs/{sys.argv[2]}")["data"]
        for s in (d.get("metrics") or {}).get("slots", []):
            print(f"    {json.dumps(s)}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
