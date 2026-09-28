#!/usr/bin/env python3
"""How deep must the kernel go before it can time this candidate at all?

measure.py reports a kernel "declaration type mismatch" for a candidate whose
executable crosscheck passes exhaustively. The judge's generated Perf.lean pins
`set_option maxRecDepth 4000000`; past that the kernel's defeq check gives up
and reports inequality rather than a depth error. So a candidate can be
correct, fast, and still ungradeable -- and the failure looks exactly like
being wrong.

This changes nothing but that one constant, so the difference between a pass
and a fail is attributable to the recursion budget and nothing else.
"""
from __future__ import annotations

import argparse
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from measure import (  # noqa: E402
    _load_judge, build_and_export, problem_dir, replay, run, stage, tool_env,
)
import measure  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problem")
    ap.add_argument("cand")
    ap.add_argument("n", type=int)
    ap.add_argument("--type", dest="value_type", default="Nat")
    ap.add_argument("--depth", type=int, default=4_000_000)
    ap.add_argument("--reps", type=int, default=2)
    args = ap.parse_args()

    measure.VALUE_TYPE = args.value_type
    judge = _load_judge()
    pdir = problem_dir(args.problem)
    env = tool_env(pdir)
    work = Path(tempfile.mkdtemp(prefix=f"depth-{args.problem}-"))
    src = work / "Cand.lean"
    src.write_text(Path(args.cand).read_text())
    backup = stage(src, pdir)
    try:
        for lib in ("Spec", "Submission"):
            rc, out = run(["lake", "build", lib], pdir, env)
            if rc != 0:
                print(f"{lib} build FAILED:\n{out[-1200:]}")
                return 2
        v = measure.oracle_value(judge, pdir, args.n, env)
        try:
            theorem, export = build_and_export(
                judge, pdir, args.n, v, env, work,
                max_rec_depth=args.depth)
        except SystemExit as e:
            msg = str(e)
            first = next((x.strip() for x in msg.splitlines()
                          if "error" in x), msg.strip()[:110])
            print(f"depth={args.depth:>12,}  FAILED  value={v}  {first[:100]}")
            return 1
        res = replay(pdir, export, theorem, args.reps)
        ins, sp = res.get("instructions"), res.get("instr_spread")
        spread = f"{100.0*(sp[1]-sp[0])/max(sp[0],1):.2f}%" if sp and sp[0] else ""
        print(f"depth={args.depth:>12,}  OK       value={v}  "
              f"INSTRUCTIONS={ins:,.0f}  spread={spread}")
        return 0
    finally:
        (pdir / "Submission.lean").write_text(backup.read_text())
        backup.unlink(missing_ok=True)
        (pdir / "Perf.lean").unlink(missing_ok=True)
        (pdir / "EvalVal.lean").unlink(missing_ok=True)
        (pdir / "Perf.olean").unlink(missing_ok=True)


if __name__ == "__main__":
    sys.exit(main())
