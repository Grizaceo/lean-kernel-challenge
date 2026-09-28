#!/usr/bin/env python3
"""Ask the kernel what `impl n` actually normalises to.

The crosscheck (Lean's own `decide`/`rfl` at elaboration) says
`mertens-sieve.impl 300` equals `mertensSpec 300`, yet the judge cannot build
the perf theorem for it. Those cannot both be true unless the elaboration-time
comparison and the kernel's defeq check disagree, so print the normal forms
and stop guessing.
"""
from __future__ import annotations

import argparse
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from measure import _load_judge, problem_dir, run, stage, tool_env  # noqa: E402

DIAG = """import Submission
import Spec
set_option maxRecDepth 100000000
set_option maxHeartbeats 0
open Lean Meta Elab in
run_meta do
  let c := mkConst ``Submission.impl
  -- dbg_trace parses as a command, so bind the concatenation first. ppExpr,
  -- not repr: repr of an Expr is a multi-line s-expression.
  let m1 := "impl type: " ++ toString (← ppExpr (← inferType c))
  dbg_trace m1
  let m2 := "impl @N@ whnf: " ++ toString (← ppExpr (← whnf (mkApp c (mkNatLit @N@))))
  dbg_trace m2
  let s := mkConst ``mertensSpec
  let m3 := "mertensSpec @N@ whnf: " ++ toString (← ppExpr (← whnf (mkApp s (mkNatLit @N@))))
  dbg_trace m3
"""

DECIDE = """import Submission
import Spec
set_option maxRecDepth 100000000
set_option maxHeartbeats 0
example : Submission.impl @N@ = mertensSpec @N@ := rfl
"""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problem")
    ap.add_argument("cand")
    ap.add_argument("n", type=int)
    ap.add_argument("--mode", default="whnf", choices=("whnf", "rfl"))
    args = ap.parse_args()

    judge = _load_judge()
    pdir = problem_dir(args.problem)
    env = tool_env(pdir)
    work = Path(tempfile.mkdtemp(prefix="diag-"))
    src = work / "Cand.lean"
    src.write_text(Path(args.cand).read_text())
    backup = stage(src, pdir)
    try:
        for lib in ("Spec", "Submission"):
            rc, out = run(["lake", "build", lib], pdir, env)
            if rc != 0:
                print(f"{lib} build FAILED:\n{out[-800:]}")
                return 2
        # str.replace, not .format: the Lean bodies are full of `{repr ...}`
        # interpolation braces that .format would try to substitute.
        body = (DIAG if args.mode == "whnf" else DECIDE).replace("@N@", str(args.n))
        f = pdir / "Diag.lean"
        f.write_text(body)
        rc, out = run(["lake", "env", "lean", "Diag.lean"], pdir, env)
        for ln in out.splitlines():
            # dbg_trace writes to stderr with no "information:"/"error:" prefix,
            # so filtering on those keywords hides exactly the output we want.
            if ln.strip() and "packages/" not in ln and "lib/lean" not in ln:
                print("  ", ln.strip()[:170])
        print(f"RC={rc}")
        return 0 if rc == 0 else 1
    finally:
        (pdir / "Diag.lean").unlink(missing_ok=True)
        (pdir / "Submission.lean").write_text(backup.read_text())
        backup.unlink(missing_ok=True)


if __name__ == "__main__":
    sys.exit(main())
