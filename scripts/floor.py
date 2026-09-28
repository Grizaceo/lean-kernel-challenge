#!/usr/bin/env python3
"""Measure the FLOOR of each problem: the replay cost with a trivial `impl`.

Why this is the first measurement, not the last (2026-09-27)
-----------------------------------------------------------
ca-rule110 finished at 178M instructions, and decomposing run 335 against
run 315 at the known 10.4x init ratio put a FIXED cost of ~166M in the judge's
metric that does not depend on the algorithm at all -- kernel start-up and
environment load, which the judge does count.

That number is problem-specific, and it decides whether a problem is worth
quota at all. `ca-rule110`'s spec is self-contained (57 lines, no Mathlib).
`fib`, `mertens` and `primecount` target Mathlib functions and pull large
transitive closures, so their floors may be far larger -- possibly larger than
the whole budget of the current ca-rule110 run. A problem whose floor already
eats the score has no algorithmic headroom, and the only way to find that out
is to measure before spending a run on it.

So: stage a `Submission.lean` that imports the same Spec the real submission
would, define `impl _ = 0`, and replay the official `impl n = 0` theorem. What
is left is the environment. It costs no quota.

Usage:
    python3 scripts/floor.py primecount [fib ...]
    python3 scripts/floor.py --all
"""
from __future__ import annotations

import argparse
import statistics
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from measure import (  # noqa: E402
    ICOUNT, _load_judge, build_and_export, problem_dir, replay, run, stage,
    tool_env,
)

# Problems whose std quota is already spent keep their value: re-measuring the
# floor of ca-rule110 is still informative, but it costs no slot either way.
ALL = ["primecount", "mertens", "fib", "partition", "polydisc", "sha256",
       "permanent", "ca-rule110"]

TRIVIAL = """\
import Spec

namespace Submission

def impl (_ : Nat) : Nat := 0

end Submission
"""


def floor_for(judge, problem: str, reps: int, n: int = 0) -> dict:
    pdir = problem_dir(problem)
    env = tool_env(pdir)
    work = Path(tempfile.mkdtemp(prefix=f"floor-{problem}-"))
    # stage() takes a candidate dir OR a file; give it the file directly.
    src = work / "Trivial.lean"
    src.write_text(TRIVIAL)
    backup = stage(src, pdir)
    try:
        # The problem's Spec and Submission libs have to exist before
        # Perf.lean can import them. The judge builds the whole package;
        # floor.py builds only the two it needs, to stay cheap. Mathlib itself
        # is the expensive part and is already warm after the first problem.
        for lib in ("Spec", "Submission"):
            rc, out = run(["lake", "build", lib], pdir, env)
            if rc != 0:
                raise SystemExit(f"{lib} lib does not build:\n{out[-1500:]}")
        theorem, export = build_and_export(judge, pdir, n, "0", env, work)
        res = replay(pdir, export, theorem, reps)
    finally:
        (pdir / "Submission.lean").write_text(backup.read_text())
        backup.unlink(missing_ok=True)
    res["problem"] = problem
    res["export_bytes"] = export.stat().st_size if export.exists() else 0
    return res


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problems", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--reps", type=int, default=3)
    args = ap.parse_args()

    problems = ALL if args.all else args.problems
    if not problems:
        ap.error("name at least one problem, or pass --all")

    judge = _load_judge()
    print(f"floor = official replay of a trivial `impl` that imports the same "
          f"Spec (instructions, {args.reps} reps, icount="
          f"{'on' if ICOUNT.exists() else 'OFF'})")
    print()
    print(f"{'problem':<14}{'instructions':>18}{'spread':>10}{'export KiB':>12}")
    print("-" * 54)
    for p in problems:
        try:
            r = floor_for(judge, p, args.reps)
        except SystemExit as e:
            print(f"{p:<14}{'FAILED':>18}   {str(e)[:400]}")
            continue
        ins = r.get("instructions")
        sp = r.get("instr_spread")
        spread = ""
        if sp and sp[0]:
            lo, hi = sp
            spread = f"{100.0*(hi-lo)/max(lo,1):.1f}%"
        print(f"{p:<14}{(f'{ins:,.0f}' if ins else '?'):>18}{spread:>10}"
              f"{r['export_bytes']/1024:>12,.0f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
