#!/usr/bin/env python3
"""Run the OFFICIAL judge replay pipeline locally, in wall_time mode.

Why this exists (2026-09-27)
---------------------------
The playground `median` and a hand-rolled `IO.monoMsNow` bench are both the
WRONG instrument for this challenge, and using them cost two wrong conclusions
in one day (see sair-active-2026).

Reading the judge source establishes what is actually scored
(`scripts/score.py`, contract `computation-total-v1`):

  * The performance plan is GROUPED, not "3 slots": `evaluation.groups` in each
    problem's config.json, each group with a `sampling` policy and its own
    timeout. `permanent` = R1/R2/R3 x 5 cases = 15 slots (matches the
    leaderboard's `coverage: 15/15`); `ca-rule110` = C1/C2/C3 x 2 = 6 slots.
  * Each slot is measured by replaying a theorem the judge GENERATES:
    `impl n = v` added as a declaration with value `Eq.refl v`, so the KERNEL
    alone type-checks it and must reduce `impl n` itself. The inputs are
    PACKED: `(scale << 32) | seed` (see `_group_packed_values`).
  * `curve_work = sum(median_instructions over passing slots)` -- a plain SUM,
    so every slot weighs the SAME. A change that only helps the largest
    dimension leaves 10 of 15 slots untouched.
  * `ranking_work = curve_work`, and `eligible` requires
    `completed_slots == planned_slots` (15/15), else the run is accepted but
    unranked.
  * `correctness_work` (the full-closure `∀n` replay) is
    `correctnessRole: verification-only` and does NOT count toward rank. It is
    the number that looks like our playground `median`, which is exactly why
    the playground median misled us.

This wrapper therefore drives the SAME official binaries the judge drives --
`lean` (generated Perf.lean), `lean4export`, and the `kernel` timer -- at the
same `target-declaration-replay-v1` boundary. It deliberately does NOT
reimplement the judge's source generators: it imports `judge.py` and calls
`_VALUE_META` and `_perf_theorem_source` directly, so the theorem it replays is
byte-identical in shape to the official one.

It runs with `TIMING_METRIC` unset, i.e. wall_time, because this VM has no PMU
(`perf_event_paranoid=2`, no `perf` binary). That is not the official metric --
it is a nanosecond-resolution stand-in measured by the official timer around
the official replay window, which is strictly better than `IO.monoMsNow` but
still NOT instructions. Only the remote judge produces instruction counts.

Usage:
    measure.py <problem> <candidate-dir> <packed-n> [--reps N] [--group-check]

`--group-check` replays every slot of the problem's own configured plan (using
a deterministic local seed) and prints the per-slot medians plus the summed
`curve_work`, which is the number the leaderboard ranks.
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

ROOT = Path(__file__).resolve().parents[1]
TIMER = Path(os.environ.get(
    "TIMER_BIN", ROOT / "evaluation/judge/timer-kernel/.lake/build/bin/kernel"))
# Optional instruction counter. Built from scripts/icount.c; see that file for why
# the judge's own metric is reproducible locally despite there being no `perf`
# binary. Absent => the run falls back to the (noisy) wall_time proxy.
ICOUNT = Path(os.environ.get("ICOUNT_BIN", ROOT / ".verify" / "icount"))
LEAN4EXPORT = Path(os.environ.get(
    "LEAN4EXPORT_BIN", ROOT.parent / "repro/lean4export/.lake/build/bin/lean4export"))
TIMER_PREFIX = "KERNEL_TIMING="


def _load_judge():
    """Import the judge's own module so we reuse its generators verbatim."""
    scripts = ROOT / "scripts"
    for p in (str(scripts), str(ROOT / "evaluation" / "judge")):
        if p not in sys.path:
            sys.path.insert(0, p)
    spec = importlib.util.spec_from_file_location(
        "lk_judge", ROOT / "evaluation" / "judge" / "judge.py")
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load the official judge module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def problem_dir(problem: str) -> Path:
    """The judge's own locked template dir, falling back to the dev copy."""
    for cand in (ROOT / "evaluation" / "problems" / problem, ROOT / "problems" / problem):
        if cand.is_dir():
            return cand
    raise SystemExit(f"no problem dir for {problem!r}")


def run(cmd, cwd, env=None, timeout=1800, env_extra=None):
    if env is None:
        env = dict(os.environ)
    if env_extra:
        env = {**env, **env_extra}
    proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True,
                          text=True, timeout=timeout)
    return proc.returncode, (proc.stdout or "") + (proc.stderr or "")


def tool_env(work: Path) -> dict:
    env = dict(os.environ)
    env.setdefault("HOME", str(Path.home()))
    env["LEAN_ABORT_ON_PANIC"] = "1"
    return env


def stage(candidate: Path, pdir: Path) -> Path:
    """Overlay the candidate Submission.lean; return a backup path to restore.

    `candidate` may be the candidate directory or the Submission.lean itself.
    """
    src = candidate / "Submission.lean" if candidate.is_dir() else candidate
    if not src.is_file():
        raise SystemExit(f"no Submission.lean at {src}")
    backup = Path(tempfile.mkdtemp()) / "Submission.lean"
    shutil.copy(pdir / "Submission.lean", backup)
    shutil.copy(src, pdir / "Submission.lean")
    return backup


# Return type of the problem's `impl`, used only to tell Lean how to `#eval` it.
# Nat for every problem except mertens, whose M(n) is genuinely Int. Set from
# `--type`; the judge's own value oracle accepts a negative literal.
VALUE_TYPE = "Nat"


def oracle_value(judge, pdir: Path, n: int, env: dict) -> str:
    """Recover the value `v` for the generated theorem `impl n = v`.

    The judge's own `_eval_impl_value` is explicitly labelled "Legacy-v1
    compatibility oracle only. Stage 1 uses independent reference answers": in
    the official grouped-v2 flow `v` arrives in a signed reference-answer
    bundle that the judge verifies, and it never recomputes it locally. We have
    no bundle, so we must derive `v` ourselves.

    `#eval` is used rather than the judge's `Meta.whnf` oracle because on this
    problem `whnf` does NOT reduce `impl n` to a literal (measured 2026-09-27:
    it returns a non-literal head, while `#eval` yields the correct 78-digit
    value immediately). The judge itself warns that `#eval` runs codegen, which
    can be exponential where kernel reduction is not.

    That divergence risk does not compromise the instrument, because the
    measurement is SELF-VALIDATING: the theorem is built with value `Eq.refl v`,
    so the KERNEL must reduce `impl n` and check it equals `v`. If `v` were
    wrong the build FAILS (the judge notes a wrong `v` "can never be scored")
    -- it can never yield a wrong number. A codegen/kernel divergence would
    surface as a build error, not as a silently wrong cost.
    """
    out_file = pdir / judge._VALUE_OUTPUT
    if out_file.exists():
        out_file.unlink()
    src = (
        "import Submission\n"
        "set_option maxRecDepth 4000000\n"
        "set_option maxHeartbeats 0\n"
        f"#eval show {VALUE_TYPE} from Submission.impl {n}\n"
    )
    (pdir / "EvalVal.lean").write_text(src)
    rc, out = run(["lake", "env", "lean", "EvalVal.lean"], pdir, env)
    (pdir / "EvalVal.lean").unlink(missing_ok=True)
    if rc != 0:
        raise SystemExit(f"#eval oracle failed at n={n}:\n{out[-2000:]}")
    text = out.strip()
    # A negative value is legitimate: mertens' impl returns Int, not Nat.
    m = re.search(r"(?m)^(-?\d+)$", text)
    if not m:
        raise SystemExit(f"#eval oracle produced no integer at n={n}: {text[:200]!r}")
    return m.group(1)


def build_and_export(judge, pdir: Path, n: int, value: str, env: dict, work: Path,
                     max_rec_depth: int | None = None):
    """Compile the generated `impl n = v` theorem and export it for the timer.

    `max_rec_depth` overrides the judge's `maxRecDepth 4000000`. The kernel's
    defeq check gives up past that limit and reports a type MISMATCH rather
    than a depth error, so a correct, fast candidate can look broken. Only
    override this to find out how deep a candidate needs; the judge itself
    always uses its own value.
    """
    source, theorem = judge._perf_theorem_source(n, value, work.name)
    if max_rec_depth is not None:
        source = source.replace("maxRecDepth 4000000",
                                f"maxRecDepth {max_rec_depth}")
    (pdir / "Perf.lean").write_text(source)
    olean = pdir / ".lake" / "build" / "lib" / "lean" / "Perf.olean"
    if olean.exists():
        olean.unlink()
    rc, out = run(["lake", "env", "lean", "-o", str(olean), "Perf.lean"], pdir, env)
    if rc != 0:
        (pdir / "Perf.lean").unlink(missing_ok=True)
        raise SystemExit(f"perf build failed at n={n}:\n{out[-2000:]}")
    export = work / "export.olean.out"
    # lean4export resolves `import Submission` / the Perf module through
    # LEAN_PATH. The judge builds this same environment in
    # `_verified_runtime_env` (artifact_lib + pinned core lib). Without it
    # lean4export reports "unknown module prefix 'Perf'" because it only sees
    # the toolchain's own library dir.
    #
    # The export JSON goes to STDOUT, so it must be written to the file
    # directly (the judge's own `run(..., stdout_path=out_path)` does the same);
    # capturing it via run()'s text return and re-writing would also work but
    # is an extra copy of a multi-MB payload.
    artifact_lib = pdir / ".lake" / "build" / "lib" / "lean"
    # Dependency lib dirs, if any. ca-rule110 is self-contained and needs
    # none, but every Mathlib-backed problem (fib, mertens, primecount, ...)
    # fails with "unknown module prefix 'Mathlib'" without them -- the export
    # has to resolve the same transitive closures the build did. Sorted so the
    # path is reproducible.
    pkg_libs = sorted(
        d for d in (pdir / ".lake" / "packages").glob("*/.lake/build/lib/lean")
        if d.is_dir()
    )
    lean_path = os.pathsep.join([str(artifact_lib), *(str(d) for d in pkg_libs),
                                 str(Path.home() / ".elan/toolchains/"
                                     "leanprover--lean4---v4.33.1/lib/lean")])
    with export.open("wb") as fh:
        proc = subprocess.run(
            [str(LEAN4EXPORT), "Perf", "--", theorem], cwd=pdir,
            env={**env, "LEAN_PATH": lean_path},
            stdout=fh, stderr=subprocess.PIPE, text=True, timeout=1800)
    rc, out = proc.returncode, (proc.stderr or "")
    (pdir / "Perf.lean").unlink(missing_ok=True)
    if rc != 0 or not export.exists() or export.stat().st_size == 0:
        raise SystemExit(f"export failed at n={n}:\n{out[-2000:]}")
    return theorem, export


def replay(pdir: Path, export: Path, theorem: str, reps: int) -> dict:
    """Run the official timer at the official target boundary, N times.

    When the `icount` helper is present the timer runs UNDER the instruction
    counter, so the result carries the judge's own metric
    (PERF_COUNT_HW_INSTRUCTIONS) instead of the wall_time stand-in. That number
    is deterministic, which matters because the wall_time proxy on this host
    swings ~40% peak-to-peak between identical replays and therefore cannot
    rank candidate variants at all.
    """
    samples, walls, rss, instrs = [], [], [], []
    use_icount = ICOUNT.exists()
    for _ in range(reps):
        cmd = ([str(ICOUNT)] if use_icount else []) + \
              [str(TIMER), "--target", theorem, str(export)]
        rc, out = run(cmd, pdir, None)
        records = [ln[len(TIMER_PREFIX):] for ln in out.splitlines()
                   if ln.startswith(TIMER_PREFIX)]
        if rc != 0 or len(records) != 1:
            raise SystemExit(f"timer failed (rc={rc}):\n{out[-2000:]}")
        data = json.loads(records[0])
        if data.get("phase") != "complete":
            raise SystemExit(f"timer did not complete: {data.get('phase')!r}")
        m = re.search(r"INSTR_TOTAL=(\d+)", out)
        if m:
            instrs.append(int(m.group(1)))
        samples.append(data)
        if type(data.get("wall_ns")) is int and data["wall_ns"] > 0:
            walls.append(data["wall_ns"])
        if type(data.get("peak_rss_kb")) is int and data["peak_rss_kb"] > 0:
            rss.append(data["peak_rss_kb"])
    return {
        "samples": samples,
        "median_wall_ns": statistics.median(walls) if walls else None,
        "peak_rss_kb": max(rss) if rss else None,
        "instructions": statistics.median(instrs) if instrs else None,
        "instr_spread": ((min(instrs), max(instrs)) if instrs else None),
    }


def slot_measure(judge, problem: str, candidate: Path, n: int, reps: int) -> dict:
    """Full per-slot pipeline: stage -> oracle -> build -> export -> replay."""
    pdir = problem_dir(problem)
    env = tool_env(pdir)
    backup = stage(candidate, pdir)
    work = Path(tempfile.mkdtemp(prefix="lkmeasure_"))
    try:
        rc, out = run(["lake", "build", "Submission"], pdir, env)
        if rc != 0:
            raise SystemExit(f"candidate does not build:\n{out[-2000:]}")
        value = oracle_value(judge, pdir, n, env)
        theorem, export = build_and_export(judge, pdir, n, value, env, work)
        result = replay(pdir, export, theorem, reps)
        result["value"] = value
        result["n"] = n
        return result
    finally:
        shutil.copy(backup, pdir / "Submission.lean")
        shutil.rmtree(backup.parent, ignore_errors=True)
        shutil.rmtree(work, ignore_errors=True)


def grouped_plan(judge, problem: str, seed: str = "local-dev-seed") -> list:
    """The problem's own configured plan, resolved with a deterministic local
    seed. Official runs use a hidden per-cohort seed, so these inputs are NOT
    the official ones -- the SHAPE (group, case, scale) is what transfers."""
    judge.PERF_SEED = seed
    pdir = problem_dir(problem)
    cfg = json.loads((pdir / "config.json").read_text())
    return judge.performance_plan(cfg, problem)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problem")
    ap.add_argument("candidate")
    ap.add_argument("packed_n", type=int, nargs="?")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--type", dest="value_type", default="Nat",
                    help="return type of impl, for #eval (mertens uses Int)")
    ap.add_argument("--group-check", action="store_true")
    args = ap.parse_args()

    global VALUE_TYPE
    VALUE_TYPE = args.value_type

    if not TIMER.exists():
        raise SystemExit(f"official timer missing: {TIMER}")
    if not LEAN4EXPORT.exists():
        raise SystemExit(f"official lean4export missing: {LEAN4EXPORT}")

    judge = _load_judge()
    candidate = Path(args.candidate).resolve()

    if args.group_check:
        plan = grouped_plan(judge, args.problem)
        total = 0
        total_instr = 0
        print(f"=== {args.problem}: official grouped plan, {len(plan)} slots "
              f"(curve_work = SUM of slot medians) ===")
        for case in plan:
            res = slot_measure(judge, args.problem, candidate, case["n"], args.reps)
            mw = res["median_wall_ns"]
            total += mw or 0
            steps = case["n"] >> 32
            instr = res["instructions"]
            if instr:
                total_instr += instr
            print(f"  {case['group']} case {case['case']}: n={case['n']} "
                  f"(scale={steps}) median_wall={mw/1e6:.2f} ms "
                  f"peak_rss={res['peak_rss_kb']} KiB")
            if instr:
                lo, hi = res["instr_spread"]
                print(f"      INSTRUCTIONS = {instr:,.0f} "
                      f"(spread {lo:,}..{hi:,}, "
                      f"{100.0*(hi-lo)/max(lo,1):.2f}% peak-to-peak) "
                      f"[official metric, user-space]")
        print(f"  --- curve_work (sum of medians) = {total/1e6:.2f} ms "
              f"[wall_time proxy, NOT instructions] ---")
        if total_instr:
            print(f"  --- curve_work_INSTRUCTIONS (sum) = {total_instr:,.0f} "
                  f"[official metric] ---")
        else:
            print("  --- curve_work_INSTRUCTIONS = None (no icount built) ---")
        return 0

    if args.packed_n is None:
        raise SystemExit("pass a packed_n, or use --group-check")
    res = slot_measure(judge, args.problem, candidate, args.packed_n, args.reps)
    print(f"n={res['n']} (scale={res['n'] >> 32}) value={res['value'][:40]}"
          f"{'...' if len(res['value']) > 40 else ''}")
    print(f"  median_wall_ns = {res['median_wall_ns']} "
          f"({res['median_wall_ns']/1e6:.2f} ms)  [wall_time proxy]")
    print(f"  peak_rss_kb   = {res['peak_rss_kb']}")
    if res["instructions"]:
        lo, hi = res["instr_spread"]
        print(f"  INSTRUCTIONS  = {res['instructions']:,.0f}  "
              f"(spread {lo:,}..{hi:,}, {100.0*(hi-lo)/max(lo,1):.2f}% "
              f"peak-to-peak)  [official metric, user-space]")
    else:
        print("  instructions  = None (no icount built; wall_time proxy only)")
    walls = sorted(s["wall_ns"] for s in res["samples"]
                   if type(s.get("wall_ns")) is int and s["wall_ns"] > 0)
    if walls:
        spread = 100.0 * (walls[-1] - walls[0]) / walls[0]
        print(f"  wall spread   = {walls[0]/1e6:.2f}..{walls[-1]/1e6:.2f} ms "
              f"({spread:.1f}% peak-to-peak over {len(walls)} reps) -- "
              f"NOISY, do not rank variants on this")
    return 0


if __name__ == "__main__":
    sys.exit(main())
