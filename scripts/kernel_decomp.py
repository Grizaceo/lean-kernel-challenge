#!/usr/bin/env python3
"""Decompose where the cost actually is, using the OFFICIAL judge instrument.

Why (2026-09-27)
----------------
The earlier attribution "the init is 98.9% of the cost" was read off a
hand-rolled wall-time bench that could not resolve the quantity it was
attributing (millisecond clock, and dead-code-eliminated `let _` calls). The
official instrument (`scripts/measure.py`) showed v2 is only 3.7% faster than
official, so the init was never the big lever it was claimed to be.

`impl n = biter (caSteps n) (initBits (caSeed n))` is a composition of two
stages, so the honest way to attribute cost is to REPLAY EACH STAGE in
isolation with the official kernel timer, at the same official boundary, and
compare against the full replay. If `initOnly` ~= `full`, the init dominates;
if `stepsOnly` ~= `full`, the per-step loop does; if neither does, the cost is
in something neither stage captures (e.g. the `Eq.refl` machinery itself).

This generates `stage n = v` theorems with the SAME construction the judge
uses (`Lean.addDecl` of `stage arg = <lit>` with value `Eq.refl <lit>`, so the
KERNEL reduces the stage body), then replays each with the official `kernel`
timer at the official `target-declaration-replay-v1` boundary. A wrong `v`
makes the build fail, never a wrong number -- the same self-validation the
judge relies on.

Usage:
    kernel_decomp.py <problem> <candidate-dir> <packed-n> [--reps N]
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from measure import (  # noqa: E402
    ICOUNT, LEAN4EXPORT, TIMER, TIMER_PREFIX, _load_judge, problem_dir, run,
    stage, tool_env,
)


def oracle(pdir: Path, expr: str, env: dict) -> int:
    """#eval an arbitrary expression, returning its integer value."""
    (pdir / "DecompVal.lean").write_text(
        "import Submission\n"
        "import Spec\n"
        "set_option maxRecDepth 4000000\n"
        "set_option maxHeartbeats 0\n"
        f"#eval show Nat from ({expr})\n")
    rc, out = run(["lake", "env", "lean", "DecompVal.lean"], pdir, env)
    (pdir / "DecompVal.lean").unlink(missing_ok=True)
    m = re.search(r"(?m)^(\d+)$", out.strip())
    if rc != 0 or not m:
        raise SystemExit(f"#eval failed for `{expr}`:\n{out[-1500:]}")
    return int(m.group(1))


def build_and_time(judge, pdir: Path, env: dict, const_name: str, args: list,
                   value: int, label: str, reps: int) -> dict:
    """Generate `const arg… = value` as an Eq.refl declaration, export, replay.

    `args` is a list because some stage functions are curried/binary (`biter :
    Nat → Nat → Nat`); applying only the first argument would not elaborate.
    """
    # mkAppN takes an Array Expr, not a List (v4.33.1): `#[...]` literal syntax.
    argexpr = "#[" + ", ".join(f"Lean.mkNatLit {a}" for a in args) + "]"
    # caMix32 and the rest of the spec live in problems/<p>/Spec.lean, declared
    # as its own `Spec` lean_lib in the problem lakefile, so `import Spec` is
    # what makes spec-level micro-stages measurable with the same machinery.
    imports = "import Submission\nimport Spec\n"
    token = f"decomp_{const_name.replace('.', '_')}_{'_'.join(map(str, args))}_{value}"
    namespace = f"Decomp_{token}"
    theorem = f"{namespace}.check"
    # Same shape as the judge: mkApp const args on the left, Nat literal on the
    # right, proof = Eq.refl rhs, added directly so the kernel must reduce.
    source = (
        imports +
        "import Lean\n"
        "set_option maxRecDepth 4000000\n"
        "set_option maxHeartbeats 0\n"
        "open Lean Meta Elab in\n"
        "run_meta do\n"
        f"  let c := Lean.mkConst ``{const_name}\n"
        f"  let lhs := Lean.mkAppN c {argexpr}\n"
        f"  let rhs := Lean.mkNatLit {value}\n"
        "  let ty ← mkEq lhs rhs\n"
        "  let pf ← mkEqRefl rhs\n"
        "  Lean.addDecl (.thmDecl {\n"
        f"    name := `{theorem},\n"
        "    levelParams := [],\n"
        "    type := ty,\n"
        "    value := pf })\n"
    )
    (pdir / "DecompPerf.lean").write_text(source)
    olean = pdir / ".lake" / "build" / "lib" / "lean" / "DecompPerf.olean"
    if olean.exists():
        olean.unlink()
    rc, out = run(["lake", "env", "lean", "-o", str(olean), "DecompPerf.lean"],
                  pdir, env)
    if rc != 0:
        (pdir / "DecompPerf.lean").unlink(missing_ok=True)
        raise SystemExit(f"build failed for {label}:\n{out[-1500:]}")

    work = Path(tempfile.mkdtemp(prefix="kdecomp_"))
    export = work / "export.olean.out"
    try:
        artifact_lib = pdir / ".lake" / "build" / "lib" / "lean"
        with export.open("wb") as fh:
            proc = subprocess.run(
                [str(LEAN4EXPORT), "DecompPerf", "--", theorem], cwd=pdir,
                env={**env, "LEAN_PATH": os.pathsep.join((
                    str(artifact_lib),
                    str(Path.home() / ".elan/toolchains/"
                        "leanprover--lean4---v4.33.1/lib/lean")))},
                stdout=fh, stderr=subprocess.PIPE, text=True, timeout=1800)
        if proc.returncode != 0 or not export.exists() or export.stat().st_size == 0:
            raise SystemExit(f"export failed for {label}:\n{proc.stderr[-1500:]}")

        walls, instrs = [], []
        for _ in range(reps):
            cmd = ([str(ICOUNT)] if ICOUNT.exists() else []) + \
                  [str(TIMER), "--target", theorem, str(export)]
            rc, out = run(cmd, pdir)
            recs = [json.loads(ln[len(TIMER_PREFIX):]) for ln in out.splitlines()
                    if ln.startswith(TIMER_PREFIX)]
            if rc != 0 or len(recs) != 1 or recs[0].get("phase") != "complete":
                raise SystemExit(f"timer failed for {label} (rc={rc}):\n{out[-1500:]}")
            if type(recs[0].get("wall_ns")) is int and recs[0]["wall_ns"] > 0:
                walls.append(recs[0]["wall_ns"])
            m = re.search(r"INSTR_TOTAL=(\d+)", out)
            if m:
                instrs.append(int(m.group(1)))
        return {
            "label": label,
            "median_wall_ns": statistics.median(walls) if walls else None,
            "instructions": statistics.median(instrs) if instrs else None,
            "instr_spread": ((min(instrs), max(instrs)) if instrs else None),
        }
    finally:
        (pdir / "DecompPerf.lean").unlink(missing_ok=True)
        shutil.rmtree(work, ignore_errors=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problem")
    ap.add_argument("candidate")
    ap.add_argument("packed_n", type=int)
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--extra", action="append", default=[],
                    help="additional isolated stage as CONST:arg1[,arg2...] "
                         "(arg names must exist in Submission/Spec); repeatable")
    args = ap.parse_args()

    judge = _load_judge()
    pdir = problem_dir(args.problem)
    env = tool_env(pdir)
    candidate = Path(args.candidate).resolve()
    backup = stage(candidate, pdir)
    n = args.packed_n
    seed = n & 0xFFFFFFFF
    steps = n >> 32
    try:
        rc, out = run(["lake", "build", "Submission"], pdir, env)
        if rc != 0:
            raise SystemExit(f"candidate does not build:\n{out[-1500:]}")

        # Resolve the per-stage arguments first, so the stage theorems are
        # exactly the sub-computations `impl` performs at this n.
        mask = oracle(pdir, f"Submission.initBits {seed}", env)
        full = oracle(pdir, f"Submission.impl {n}", env)
        print(f"n={n} (steps={steps} seed={seed}) init_mask={mask} full={full}")

        results = []
        results.append(build_and_time(judge, pdir, env, "Submission.initBits",
                                      [seed], mask, "initOnly", args.reps))
        # The per-step stage inside `impl` is `biter steps (initBits seed)`, so
        # its ARGUMENTS are the step count and the init mask, not the full
        # output. Timing `biter steps full` would measure a different (wrong)
        # computation.
        steps_value = oracle(pdir, f"Submission.biter {steps} {mask}", env)
        results.append(build_and_time(judge, pdir, env, "Submission.biter",
                                      [steps, mask], steps_value, "stepsOnly",
                                      args.reps) | {"value": steps_value})
        # full = the official measurement for reference
        res_full = build_and_time(judge, pdir, env, "Submission.impl", [n], full,
                                  "full", args.reps)
        results.append(res_full)

        # Additional isolated micro-stages, e.g. Spec.caMix32 12345 -- used to
        # attribute the per-cell cost inside the init to individual operations.
        for spec in args.extra:
            const, _, arglist = spec.partition(":")
            cargs = [int(a) for a in arglist.split(",") if a]
            cexpr = f"{const} " + " ".join(map(str, cargs))
            cval = oracle(pdir, cexpr, env)
            results.append(build_and_time(
                judge, pdir, env, const, cargs, cval,
                const.replace(".", "_")[:18], args.reps))

        base = res_full["median_wall_ns"] or 1
        print("=== official kernel-timer decomposition ===")
        print("    INSTR = local PERF_COUNT_HW_INSTRUCTIONS (deterministic; "
              "includes constant process overhead, judge = replay window only)")
        for r in results:
            mw = r["median_wall_ns"]
            ins = r["instructions"]
            sp = ""
            if r["instr_spread"]:
                lo, hi = r["instr_spread"]
                sp = f" (±{100.0*(hi-lo)/max(lo,1):.2f}%)"
            pct = 100.0 * mw / base if base else 0
            print(f"  {r['label']:10s} INSTR = {ins:>15,.0f}{sp}   "
                  f"wall {mw/1e6:7.2f} ms ({pct:5.1f}%)")
        return 0
    finally:
        shutil.copy(backup, pdir / "Submission.lean")
        shutil.rmtree(backup.parent, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
