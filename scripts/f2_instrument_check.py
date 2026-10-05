#!/usr/bin/env python3
"""F2 step 0 — validate the instrument before spending a cell on it.

Three questions, in order of cost:
  Q1  does a trivial probe build, export and replay end-to-end?
  Q2  does the official timer open its OWN instruction counter here
      (--count-instructions), i.e. do we get the judge metric with no
      process-startup floor?
  Q3  if Q2 fails, what is the real floor and the real noise, so the F2 table
      states its own resolution instead of pretending to more?
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from f2_harness import (build_and_export, problem_dir, probe_source,  # noqa: E402
                        replay)

pdir = problem_dir("partition")
work = Path("/home/gris96/.hermes/profiles/eidos/cache/scratch/f2-instrument")
work.mkdir(parents=True, exist_ok=True)

# Q1: smallest honest probe -- one 64-bit add, proved the way the JUDGE proves
# it. A source-level `theorem check : ... := rfl` does NOT reach the exported
# environment (the module imports fine, but `F2Probe.check` is an unknown
# identifier and lean4export PANICs with rc=0), so this probe must declare the
# theorem through Lean.addDecl exactly like f2_harness.probe_source does.
# This was the stale part: the check had drifted behind the harness it validates.
SRC = probe_source("Nat.add", 2 ** 32, 2 ** 31, 2 ** 32 + 2 ** 31, "F2Probe.check")

print("=== Q1: build + export of a trivial 64-bit probe (addDecl form) ===", flush=True)
try:
    export = build_and_export(pdir, SRC, "F2Probe.check", work)
    print(f"    export OK: {export.stat().st_size:,} B at {export}", flush=True)
except Exception as exc:
    print(f"    FAILED: {exc}", flush=True)
    raise SystemExit(1)

print("=== Q2: official timer with --count-instructions (window-only metric) ===", flush=True)
res = replay(pdir, export, "F2Probe.check", reps=3, count_instructions=True)
print(json.dumps(res, indent=1), flush=True)

print("=== Q3: same export WITHOUT the flag (process-wide icount) ===", flush=True)
res_noflag = replay(pdir, export, "F2Probe.check", reps=3, count_instructions=False)
print(json.dumps(res_noflag, indent=1), flush=True)

(work / "q1_probe.lean").write_text(SRC)
(work / "q1_export.out").write_bytes(export.read_bytes())
print(f"\nartifacts in {work}", flush=True)
