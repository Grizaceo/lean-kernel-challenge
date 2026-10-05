#!/usr/bin/env python3
"""F12 -- the marginal cost of arithmetic in the CHAMPION-REACHABLE shape.

PRE-REGISTERED 2026-10-05, BEFORE ANY NUMBER IS PRODUCED. Committed before the run.

WHY THIS EXPERIMENT IS NOW THE ONLY THING THAT MATTERS
------------------------------------------------------
F11 measured the floor in the judge's own shape (`judge._perf_theorem_source`,
imported verbatim):

    impl that computes NOTHING, no recursor .......   199,012
    impl that is a Nat.rec, computes nothing .......   356,917   (k=0)

The partition champion's slot is 238,082. So:

    floor WITHOUT a recursor = 199,012 = 0.836x slot  -> FITS, headroom 39,070
    floor WITH    a recursor = 356,917 = 1.499x slot  -> EXCEEDS by 118,835

That inverts the design. A recursor-using `impl` cannot fit a champion slot even
if it computes NOTHING, so every candidate that recurses is out of reach and the
budget lives in the 39,070 instructions left after a non-recursive floor.

But 39,070 is not yet a budget: nobody has measured what an OPERATION costs in
that shape. F9 says one `Nat.add` costs ~206,328 -- against a floor of 118,230
that is an 88,098 marginal. Those F8/F9 numbers were measured with
`f2_harness.probe_source`, i.e. on bare literals with NO `impl`, NO recursor
machinery -- the very shape F11 just showed to be 40.8% off. Quoting 88,098
against a 199,012 floor would give 2,872,110 per slot = 17.2M over 6 slots =
12.1x the champion, which would wrongly kill every candidate.

So the missing number is the marginal of one operation measured in the shape that
actually reaches the board, with the recursor absent.

THE HYPOTHESES
--------------
H12.1  In the judge shape with no recursor, the marginal cost of one `Nat.add` is
       a small fraction of the floor, so several operations fit in the 39,070 of
       headroom. Prediction: beta is well under 39,070.

H12.2  The marginal is a large fraction of the floor (>= 39,070), so the headroom
       buys at most ONE operation and the budget is one op per slot after all --
       which would make F8/F9's "one operation per slot" conclusion right for the
       wrong reason (right answer, wrong floor).

FALSIFICATION CRITERIA (fixed before the run)
---------------------------------------------
G1  A cell that fails to build, export or complete the replay ABORTS the run.
G2  Intra-cell spread > 5% -> re-measure once, then report with its spread.
G3  THE LADDER MUST TRAVERSE (F10b's G8, kept because F10 died without it):
    Series VOID unless strictly increasing with z(beta) > 3. A flat ladder means
    the body did not force k operations and the run reports the defect.
G4  THE GENERATOR MUST BE THE JUDGE'S: every theorem comes from
    `judge._perf_theorem_source`, imported verbatim, source recorded.
G5  NO RECURSOR ANYWHERE in these probes. Asserted by inspecting the staged
    `Submission.lean` for `Nat.rec`/structural patterns -- a recursor here would
    move the floor to 356,917 and void the whole point of the experiment.
G6  SHAPE CONTROL: the k=0 cell must agree with F11's `J-C-trivial` (199,012)
    within 5%. `fun n => n` and `fun _ => 0` both reduce to a projection with no
    arithmetic, so they are the same measurement; if they disagree, the shape is
    not what this experiment assumes and the run is DRIFTED.
G7  `problems/` restored byte-for-byte in a finally block.
G8  SCOPE: user-space only (LK_EXCLUDE_KERNEL=1). The judge counts a SUPERSET, so
    every figure here is a LOWER bound on the judge's charge. Ratios to this run's
    own k=0 are quotable; the champion's 238,082 is used only as the reference for
    "does it fit", which is the safe direction.

CELLS
-----
`impl := fun n => n + 1 + 1 + ... ` (k times), a left-nested GMP chain with NO
recursor, at a literal n=5. k=0 is `fun n => n`.

MEASUREMENT
-----------
`instructions` from the local timer at `target-declaration-replay-v1`, the same
boundary and instrument as F5/F8/F9/F10/F10b/F11, median of 3, absolute, no
subtraction.
"""
from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import time
from pathlib import Path

sys.set_int_max_str_digits(500_000)

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import f2_harness  # noqa: E402
from f2_harness import TIMER_BIN, ProbeError, lean_path  # noqa: E402
from measure import LEAN4EXPORT, problem_dir, run  # noqa: E402

LADDER = [0, 1, 2, 3, 5, 10, 20]
REPS = 3
N_IN = 5                      # the literal input; small so only k matters
CHAMPION_SLOT = 238_082
F11_FLOOR_NOREC = 199_012     # J-C-trivial, judge shape
F11_FLOOR_REC = 356_917       # F10b A@0, judge-shaped recursor floor
F10B_UNFOLD = 95_398          # marginal per unfold WITH a recursor
G3_Z_MIN = 3.0
G6_TOLERANCE = 0.05


def chain(k: int) -> str:
    """`impl := fun n => n + 1 + ... ` k times. A left-nested GMP chain: no
    recursor, k `Nat.add`s the kernel must reduce."""
    if k == 0:
        return "def impl : Nat → Nat := fun n => n"
    return ("def impl : Nat → Nat := fun n => "
            + " + ".join(["n"] + ["1"] * k))


def load_judge():
    sys.path.insert(0, str(ROOT / "evaluation" / "judge"))
    spec = importlib.util.spec_from_file_location(
        "lk_judge", ROOT / "evaluation" / "judge" / "judge.py")
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load the official judge module")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def fit_lin(points):
    import statistics
    n = len(points)
    if n < 3:
        return None, None, None, None
    xs = [float(x) for x, _ in points]
    ys = [float(y) for _, y in points]
    mx, my = statistics.mean(xs), statistics.mean(ys)
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    beta = sxy / sxx
    alpha = my - beta * mx
    resid = [y - (alpha + beta * x) for x, y in zip(xs, ys)]
    worst = max(abs(r) / y * 100 for r, y in zip(resid, ys))
    sse = sum(r * r for r in resid)
    se = (sse / (n - 2) / sxx) ** 0.5 if n > 2 and sxx > 0 else float("inf")
    return alpha, beta, se, worst


def main() -> int:
    pdir = problem_dir("partition")
    outdir = ROOT / "results" / "cost_model"
    outdir.mkdir(parents=True, exist_ok=True)
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f12-run"
    work.mkdir(parents=True, exist_ok=True)

    judge = load_judge()
    print(f"timer: {TIMER_BIN}   reps={REPS}   ladder k={LADDER}   n={N_IN}", flush=True)
    print(f"headroom after F11's non-recursor floor: "
          f"{CHAMPION_SLOT - F11_FLOOR_NOREC:,} instructions/slot", flush=True)
    print("G3 traversal, G5 no-recursor, G6 shape control vs F11's 199,012.\n",
          flush=True)

    sub, perf = pdir / "Submission.lean", pdir / "Perf.lean"
    olean = pdir / ".lake" / "build" / "lib" / "lean" / "Perf.olean"
    pristine = {
        "Submission.lean": sub.read_bytes(),
        "Perf.lean": perf.read_bytes() if perf.exists() else None,
        "Perf.olean": olean.read_bytes() if olean.exists() else None,
    }
    cells: dict[str, dict] = {}
    sources: dict[str, str] = {}

    def record(k: int) -> bool:
        key = f"chain@{k}"
        body = chain(k)
        v = str(N_IN + k)
        t0 = time.time()
        try:
            staged = f"import Spec\n\nnamespace Submission\n{body}\n\nend Submission\n"
            # G5 -- assert no recursor before measuring.
            for bad in ("Nat.rec", "| ", "match ", "termination_by"):
                if bad in staged:
                    raise ProbeError(f"[G5] staged Submission contains {bad!r}: "
                                     f"the no-recursor premise is violated")
            sub.write_text(staged)
            rc, out = run(["lake", "build", "Submission"], pdir)
            if rc != 0:
                raise ProbeError(f"[build] rc={rc}: {out[-600:]}")

            source, theorem = judge._perf_theorem_source(N_IN, v, work.name)   # G4
            for frag in ("Lean.addDecl (.thmDecl", "Submission.impl",
                         "mkEqRefl rhs", "maxRecDepth 4000000"):
                if frag not in source:
                    raise ProbeError(f"[G4] generator output lacks {frag!r}")
            sources[key] = source

            perf.write_text(source)
            olean.unlink(missing_ok=True)
            rc, out = run(["lake", "env", "lean", "-o", str(olean), "Perf.lean"], pdir)
            if rc != 0:
                raise ProbeError(f"[build Perf] rc={rc}: {out[-600:]}")

            export = work / "export.out"
            with export.open("wb") as fh:
                proc = subprocess.run(
                    [str(LEAN4EXPORT), "Perf", "--", theorem], cwd=pdir,
                    stdout=fh, stderr=subprocess.PIPE, text=True, timeout=1800,
                    env={**os.environ, "LEAN_PATH": lean_path(pdir)})
            f2_harness.check_step("export", proc.returncode, proc.stderr or "")
            if export.stat().st_size <= 512:
                raise ProbeError(f"[export] only {export.stat().st_size} B (header only)")

            res = f2_harness.replay(pdir, export, theorem, REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:                        # G2
                res = f2_harness.replay(pdir, export, theorem, REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cells[key] = dict(k=k, body=body, n=N_IN, v=v, status="ok",
                              window_median=res["window_median"],
                              window_instructions=res["window_instructions"],
                              window_min=res["window_min"],
                              window_max=res["window_max"],
                              window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                              seconds=round(time.time() - t0, 2))
            print(f"  {key:<12} {res['window_median']:>11,.0f} instr   "
                  f"spread={res['window_spread_pct']:.2f}%   "
                  f"({cells[key]['seconds']}s)", flush=True)
        except ProbeError as exc:
            out = outdir / "f12_champion_shape_marginal.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": key,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"  {key:<12} ABORT: {str(exc)[:300]}\nG1 TRIGGERED -> {out}",
                  flush=True)
            return False
        return True

    try:
        for k in LADDER:
            if not record(k):
                return 1
    finally:
        sub.write_bytes(pristine["Submission.lean"])
        if pristine["Perf.lean"] is not None:
            perf.write_bytes(pristine["Perf.lean"])
        else:
            perf.unlink(missing_ok=True)
        if pristine["Perf.olean"] is not None:
            olean.write_bytes(pristine["Perf.olean"])
        else:
            olean.unlink(missing_ok=True)

    pts = sorted((c["k"], c["window_median"]) for c in cells.values()
                 if c.get("status") == "ok")
    alpha, beta, se, resid = fit_lin(pts)
    if alpha is None or beta is None:
        out = outdir / "f12_champion_shape_marginal.json"
        out.write_text(json.dumps({"status": "incomplete", "cells": cells}, indent=1))
        print(f"\nINCOMPLETE -> {out}")
        return 1

    k0 = dict(pts).get(0)
    z = beta / se if se else float("inf")
    # This run's OWN k=0 floor, not F11's -- they are different decls and the
    # "ops that fit" must come from one consistent measurement.
    own_headroom = CHAMPION_SLOT - k0 if k0 else None
    headroom = CHAMPION_SLOT - F11_FLOOR_NOREC   # cross-check against F11 only

    verdicts: list[str] = []
    inst = max(c["window_spread_pct"] for c in cells.values() if c.get("status") == "ok")
    verdicts.append(f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
                    f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}")
    h121 = h122 = "UNRESOLVED (ladder void)"
    if z <= G3_Z_MIN:                                            # G3
        verdicts.append(f"G3 traversal         : beta = {beta:,.0f} +- {se:,.0f}, "
                        f"z = {z:.2f} (needs > {G3_Z_MIN}) -> ladder VOID, the chain "
                        f"did not force k operations. No cost law from this run.")
    else:
        verdicts.append(f"G3 traversal         : beta = {beta:,.0f} +- {se:,.0f} "
                        f"(z = {z:.1f} > {G3_Z_MIN}) -> the chain DID force k adds")
        if beta < headroom:
            verdicts.append(
                f"H12.1 cheap marginal: beta = {beta:,.0f} instr/add is {beta/headroom:.2f}x "
                f"the {headroom:,} of headroom, so {headroom/beta:.2f} adds fit in a "
                f"champion slot -> H12.1 NOT rejected")
            h121 = "NOT rejected"
        else:
            verdicts.append(
                f"H12.2 one-op budget : beta = {beta:,.0f} instr/add >= the {headroom:,} "
                f"of headroom, so at most {headroom/beta:.2f} adds fit per slot -> "
                f"H12.2 NOT rejected: one operation per slot, for a different reason "
                f"than F8/F9 gave")
            h122 = "NOT rejected"
        fits = (f"{(own_headroom / beta):.2f} adds after this run's own floor "
                f"(k=0 = {k0:,})" if own_headroom and own_headroom > 0
                else f"this run's own floor already exceeds the slot")
        verdicts.append(f"ops per slot        : {fits}, or {headroom/beta:.2f} after "
                        f"F11's independently measured floor")
        verdicts.append(
            f"recursor vs chain   : a Nat.rec costs {F10B_UNFOLD:,.0f} per unfold "
            f"(F10b) while a flat add costs {beta:,.0f} here = "
            f"{F10B_UNFOLD/beta:.2f}x. Recursion is the expensive form, not arithmetic.")

    # G6 -- shape control against F11's independently measured floor.
    if k0:
        rel = abs(k0 - F11_FLOOR_NOREC) / F11_FLOOR_NOREC
        if rel <= G6_TOLERANCE:
            verdicts.append(
                f"G6 shape control    : this run's k=0 floor {k0:,} vs F11's "
                f"{F11_FLOOR_NOREC:,} = {k0/F11_FLOOR_NOREC:.4f}x "
                f"(tol {G6_TOLERANCE:.0%}) -> same shape, instrument consistent")
        else:
            verdicts.append(
                f"G6 shape control    : this run's k=0 floor {k0:,} vs F11's "
                f"{F11_FLOOR_NOREC:,} = {k0/F11_FLOOR_NOREC:.4f}x, drift {rel:.1%} > "
                f"{G6_TOLERANCE:.0%} -> run DRIFTED, verdicts above VOID")
    verdicts.append(
        f"G4 generator         : every theorem came from judge._perf_theorem_source; "
        f"sources recorded verbatim. No hand-built substitute.")
    verdicts.append(
        "G5 no recursor       : every staged Submission.lean was asserted free of "
        "Nat.rec / structural patterns / match / termination_by before being built.")
    verdicts.append(
        f"G8 scope            : user-space only (LK_EXCLUDE_KERNEL=1); the judge counts "
        f"a SUPERSET, so these are LOWER bounds on the judge's charge. 'Fits in a "
        f"champion slot' is used only in the safe direction.")
    verdicts.append(
        "G7 restoration       : Submission.lean, Perf.lean and Perf.olean restored "
        "byte-for-byte in a finally block.")

    payload = {
        "status": "ok",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "scope": "user-space only (LK_EXCLUDE_KERNEL=1)",
                       "generator": "judge._perf_theorem_source, imported verbatim",
                       "n_literal": N_IN},
        "references_not_inputs": {
            "champion_slot": CHAMPION_SLOT,
            "f11_floor_norec": F11_FLOOR_NOREC,
            "f11_floor_rec": F11_FLOOR_REC,
            "f10b_unfold_with_recursor": F10B_UNFOLD,
            "headroom": headroom},
        "preregistered": {
            "H12.1": "marginal per add is a small fraction of the floor",
            "H12.2": "marginal >= headroom, so the budget is one op per slot",
            "criteria": {
                "G1": "abort on failed cell", "G2": "spread > 5% -> re-measure",
                "G3": f"ladder VOID unless z(beta) > {G3_Z_MIN}",
                "G4": "theorem must come from judge._perf_theorem_source",
                "G5": "assert no recursor in the staged Submission",
                "G6": f"k=0 must agree with F11 within {G6_TOLERANCE:.0%}",
                "G7": "restore problems/ byte-for-byte",
                "G8": "user-space only; safe direction for the fit test"}},
        "verdicts": {"H12.1": h121 if z > G3_Z_MIN else "UNRESOLVED (ladder void)",
                     "H12.2": h122 if z > G3_Z_MIN else "UNRESOLVED (ladder void)"},
        "ladder": pts,
        "fit": {"alpha": alpha, "beta_instr_per_add": beta, "se_beta": se,
                "worst_residual_pct": resid, "z": z},
        "generator_sources": sources,
        "cells": cells,
    }
    out = outdir / "f12_champion_shape_marginal.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        "F12 -- the marginal cost of arithmetic in the CHAMPION-REACHABLE shape (2026-10-05)",
        "",
        "A flat GMP chain `fun n => n + 1 + 1 + ... `, NO recursor, judge generator.",
        "scope: USER-SPACE only (LK_EXCLUDE_KERNEL=1) -- lower bounds on the judge's charge.",
        "",
        f"{'k (adds)':>10}{'instructions':>14}{'vs k=0':>12}{'implied/add':>14}",
    ]
    base = dict(pts)[0]
    for k, c in pts:
        lines.append(f"{k:>10}{c:>14,.0f}{c - base:>12,.0f}"
                     f"{(c - base) / k if k else 0:>14,.0f}")
    lines += [
        "",
        f"fit: {alpha:,.0f} + ({beta:,.0f} +- {se:,.0f}) * k    z = {z:.1f}    "
        f"worst residual {resid:.1f}%",
        "",
        "VERDICTS (pre-registered in scripts/f12_champion_shape_marginal.py)",
    ] + [f"  {v}" for v in verdicts] + ["", f"wrote {out}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f12_champion_shape_marginal.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())