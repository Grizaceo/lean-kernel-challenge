#!/usr/bin/env python3
"""Measure the REFERENCE cost of each problem: the cheapest legal submission.

`def impl n := <specFn> n` with `impl_correct := rfl` is a legal submission for
every problem in the challenge (the spec's target is itself a plain function),
and it is the floor for "how expensive is the reference algorithm in the
kernel". Anything a real submission does has to beat this, minus the ~168.86M
environment floor that floor.py established as problem-independent.

This is a baseline, not a submission. It costs no quota: nothing is sent.

Usage:
    python3 scripts/baseline.py --all
    python3 scripts/baseline.py primecount fib
"""
from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from measure import (  # noqa: E402
    _load_judge, build_and_export, problem_dir, replay, run, stage, tool_env,
)
from floor import ALL  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
PROBLEMS = ROOT / "problems"

# floor.py's numbers, as a constant so the report can subtract it.
FLOOR = 168_860_000


def spec_target(problem: str) -> tuple[str, str]:
    """(name, return type) of the spec's TARGET function.

    The target is the last top-level `def`/`abbrev` in the spec: every spec
    defines its helpers first and the thing you must reproduce last. Matching
    on a `*Spec` suffix is not enough -- ca-rule110's target is `caSpecN` --
    and a strict binder pattern is not enough either, because `(n : Nat)`
    contains the very colons such a pattern has to exclude.

    Return type is the text after the last arrow, or after the last top-level
    colon, whichever applies.
    """
    text = (PROBLEMS / problem / "Spec.lean").read_text()
    decls = list(re.finditer(r"^(?:def|abbrev)\s+(\w+)(.*?):=", text, re.M))
    if not decls:
        raise SystemExit(f"{problem}: no top-level def/abbrev found")
    m = decls[-1]
    name, rest = m.group(1), m.group(2)
    if "→" in rest or "->" in rest:
        ret = re.split(r"→|->", rest)[-1]
    elif ":" in rest:
        ret = rest.rsplit(":", 1)[-1]
    else:
        ret = "Nat"
    return name, (ret.strip() or "Nat")


def submission_src(name: str, ret: str) -> str:
    return (
        "import Spec\n\n"
        "namespace Submission\n\n"
        f"def impl (n : Nat) : {ret} := {name} n\n\n"
        f"theorem impl_correct : ∀ n, impl n = {name} n := by\n"
        "  intro n; rfl\n\n"
        "end Submission\n"
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problems", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--n", type=int, default=12,
                    help="input slot; small so the reference's asymptotics do "
                         "not dominate the floor (default 12)")
    args = ap.parse_args()

    problems = ALL if args.all else args.problems
    if not problems:
        ap.error("name at least one problem, or pass --all")

    judge = _load_judge()
    print(f"reference cost = official replay of `impl n = {args.n}` where "
          f"impl just calls the spec function (no quota spent)\n")
    print(f"{'problem':<14}{'total':>16}{'minus floor':>16}{'spread':>9}  target")
    print("-" * 70)
    rows = []
    for p in problems:
        try:
            name, ret = spec_target(p)
            pdir = problem_dir(p)
            env = tool_env(pdir)
            work = Path(tempfile.mkdtemp(prefix=f"base-{p}-"))
            src = work / "Base.lean"
            src.write_text(submission_src(name, ret))
            backup = stage(src, pdir)
            try:
                for lib in ("Spec", "Submission"):
                    rc, out = run(["lake", "build", lib], pdir, env)
                    if rc != 0:
                        raise SystemExit(f"{lib}:\n{out[-1200:]}")
                v = replay_value(judge, pdir, env, work, args.n, name, ret)
                theorem, export = build_and_export(
                    judge, pdir, args.n, str(v), env, work)
                res = replay(pdir, export, theorem, args.reps)
            finally:
                (pdir / "Submission.lean").write_text(backup.read_text())
                backup.unlink(missing_ok=True)
        except SystemExit as e:
            print(f"{p:<14}{'FAILED':>16}   {str(e)[:70]}")
            continue
        ins, sp = res.get("instructions"), res.get("instr_spread")
        if not ins:
            print(f"{p:<14}{'?':>16}   (no instruction count)")
            continue
        over = max(0, ins - FLOOR)
        spread = f"{100.0*(sp[1]-sp[0])/max(sp[0],1):.1f}%" if sp and sp[0] else ""
        print(f"{p:<14}{ins:>16,.0f}{over:>16,.0f}{spread:>9}  {name} : {ret}")
        rows.append((p, ins, over))
    return 0


def replay_value(judge, pdir, env, work, n, name, ret):
    """#eval the reference at n, to know what impl n must equal."""
    (pdir / "BaseVal.lean").write_text(
        f"import Spec\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
        f"#eval show {ret} from ({name} {n})\n")
    rc, out = run(["lake", "env", "lean", "BaseVal.lean"], pdir, env)
    (pdir / "BaseVal.lean").unlink(missing_ok=True)
    if rc != 0:
        raise SystemExit(f"cannot evaluate {name} {n}:\n{out[-1200:]}")
    return out.strip().splitlines()[-1].strip()


if __name__ == "__main__":
    sys.exit(main())
