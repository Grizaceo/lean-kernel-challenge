#!/usr/bin/env python3
"""F10 -- is the 118k declaration floor paid ONCE per declaration, or PER UNFOLD?

PRE-REGISTERED 2026-10-05, BEFORE ANY NUMBER IS PRODUCED. Committed before the
run so the criteria are an artifact, not a recollection.

THE TENSION THIS RESOLVES (inherited from F8/F9, still open)
-------------------------------------------------------------
F8/F9 established the cost model

    cost of one arithmetic operation = declaration floor + arithmetic
      floor per DECLARATION   ~118,230   57%
      arithmetic on the floor  ~ 88,098   43%
      total                    ~206,328

and the hard wall: a champion's slot is 238,082 instructions, so the budget buys
ONE operation (206,328, margin 31,754) and never two (suelo + 1 op = 324,558,
over by 86,476).

The open tension is arithmetic that DISAGREES with that. F5's ladder reads
~121,247 instructions per reduction step; two steps would be ~242,494, i.e.
almost exactly one champion slot (238,082). So the leaderboard's implied ~2
unfolds/slot is consistent with a budget that "only buys one operation" -- but
only if the 118,230 floor is NOT charged again for the second unfold.

Three explanations were left standing by F8, none verified:
  (a) my boundary is user-only (LK_EXCLUDE_KERNEL=1), the judge counts user+kernel
      -> constant bias, only the RATIOS are valid;
  (b) the champion normalises less work than my probe pays for;
  (c) the champion's micro-operation is not an unfold of Nat.rec.

This experiment does not try to pick (a)/(b)/(c) by argument. It measures the one
thing that decides whether the packed-DP candidate design is viable at all:
whether the floor recurs per unfold.

THE QUESTION, IN ONE LINE
-------------------------
Within ONE replayed declaration of the REAL judge shape, is

    c(k) = floor + k * marginal            (floor paid ONCE)      [H10.1]
or
    c(k) = (k + 1) * floor + k * marginal (floor charged PER UNFOLD) [H10.2]

The distinction is the whole design: if H10.2 holds, no amount of packing saves
the candidate, because packing amortises the floor and the floor would not
amortise -- it would recur. If H10.1 holds, the ~68 instr/value that F9 computed
at 4,096 lanes is reachable and a single ~206k operation can carry a whole DP row.

WHY THE LADDER IS BUILT IN THE JUDGE'S OWN SHAPE
------------------------------------------------
Read from `evaluation/judge/judge.py::_perf_theorem_source` and reproduced
verbatim: a UNARY `impl : Nat -> Nat`, the theorem `impl k = v` added through
`Lean.addDecl` with value `Eq.refl v`, `Lean.mkNatLit` for both the input and
the expected output, `mkEq`/`mkEqRefl` for the type and the proof, and
`set_option maxRecDepth 4000000 / maxHeartbeats 0`.

This matters and it is the F9/F5 lesson applied as a guard rather than a note:
"before reading two measured magnitudes as 'the same thing', check the probes
have the SAME SHAPE." F8's floor probe was a bare `Eq.refl` between two literals
-- NOT `impl n = v` -- so calling 118,230 the floor of a real scored slot was
already an assumption. G4 below makes the shape an assertion.

PREREGISTERED HYPOTHESES
------------------------
H10.1  The floor is paid ONCE per declaration. Prediction: the FIRST unfold costs
       roughly the marginal per-unfold cost, i.e. c(1) - c(0) is a small
       fraction of c(0). Supporting: F9 measured the floor as a property of the
       declaration (an `Eq.refl` that computes nothing still costs 118,230), and
       F5's own k=0 point (369,196) already contains one recursor unfold, so F5
       never had a true floor point to compare against.

H10.2  The floor is charged PER UNFOLD. Prediction: c(1) - c(0) is itself about
       as large as c(0), so every unfold repays the whole fixed cost. Supporting:
       F7's packing fit `244,590 + 37.1 * lanes` has an intercept that EXCEEDS a
       champion's entire slot, which is what a per-unfold floor would produce.

H10.3  Control -- the ladder reproduces a prior measurement. Series B's marginal
       per unfold must land within 10% of F5b's `add1` value of 121,537
       instructions/step, measured by the same instrument. If it does not, the
       instrument has drifted and NO ladder result from this run may be used.

FALSIFICATION CRITERIA (fixed before the run; applied literally afterwards)
--------------------------------------------------------------------------
G1  A cell that fails to build, export, or complete the replay ABORTS the run. A
    failed cell is never written as a number. (F2's whole table was invalidated by
    lean4export PANICking with rc=0.)

G2  Intra-cell spread > 5% -> re-measure once; if still > 5%, report the cell
    WITH its spread instead of as a point value.

G3  THE DECISIVE TEST, on Series A (empty body, so the ladder isolates UNFOLDING
    from arithmetic -- F5b measured body-dependence of 4.15x):
      H10.1 is REJECTED  if  c(1) - c(0)  >=  0.90 * c(0)
      H10.2 is REJECTED  if  c(1) - c(0)  <   0.60 * c(0)
      between the two thresholds      -> UNRESOLVED, explicitly not a blend.

G4  SHAPE ASSERTION. Every generated probe source must contain, verbatim, the
    judge constructs: `Lean.addDecl (.thmDecl`, `mkEqRefl`, `mkEq lhs rhs`,
    `Lean.mkNatLit`, `mkApp implC (Lean.mkNatLit`, `maxRecDepth 4000000`,
    `maxHeartbeats 0`. A source missing any of them is a guard violation and
    aborts: a probe of a different shape cannot answer the question.

G5  H10.3 CONTROL. If Series B's fitted marginal is not within 10% of F5b's
    121,537 instr/step, the whole run is declared DRIFTED and every verdict is
    void. Reported either way.

G6  No absolute in this run may be compared slot-to-slot with the leaderboard.
    `LK_EXCLUDE_KERNEL=1` makes these user-space only; the judge counts
    user+kernel. Only ratios to this run's own c(0) are quotable. Any statement
    of the form "fits in a champion's slot" is labelled as user-space-only.

G7  Report negatives with the same detail as positives. If neither H10.1 nor
    H10.2 survives G3, the verdict is UNRESOLVED and the F8/F9 tension is
    declared STILL OPEN -- not resolved by averaging the two models.

MEASUREMENT
-----------
`instructions` from the official timer's KERNEL_TIMING record at the
`target-declaration-replay-v1` boundary -- the boundary the remote judge scores.
Instrument identical to F5/F8/F9: `.verify/timer-kernel-local`,
`LK_EXCLUDE_KERNEL=1`, median of 3 reps, absolute boundary (no subtraction).

WHAT IS DELIBERATELY NOT CONCLUDED HERE
---------------------------------------
This measures the floor's recurrence in a ladder of a synthetic structural
recursor. It does not measure the champion's code, and it cannot verify
explanation (b) "the champion normalises less work than my probe". If H10.1
survives, that settles the DESIGN question only; the ranking question still
needs the real candidate measured in the real plan.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.set_int_max_str_digits(500_000)

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from f2_harness import (COUNT_INSTRUCTIONS, TIMER_BIN, ProbeError,  # noqa: E402
                        build_and_export, problem_dir, replay)

# k = number of recursor unfold steps the kernel must perform.
# The pre-registration asked for {0,1,2,10}; 3 and 5 are added so the linear fit
# is not dominated by the single far point at k=10. The four required points are
# present and none were dropped.
LADDER = [0, 1, 2, 3, 5, 10]
REPS = 3

# Prior measurements, used ONLY as references and controls (never as inputs).
F8_FLOOR = 118_230        # F8 A-const-refl: Eq.refl between literals, no arithmetic
F9_ADD_SMALL = 206_328    # F9 E-add-small: Nat.add 1+1 -- cheapest arithmetic
F5B_ADD1_PER_STEP = 121_537   # F5b add1 body at k=100: instructions per unfold
CHAMPION_SLOT = 238_082   # partition leader computationTotal 1,428,492 / 6 slots

# G4 -- the judge's constructs that MUST appear in every probe source.
REQUIRED_FORMS = [
    "maxRecDepth 4000000",
    "maxHeartbeats 0",
    "Lean.mkConst ``F10Impl.impl",
    "Lean.mkApp implC (Lean.mkNatLit",
    "Lean.mkNatLit",
    "mkEq lhs rhs",
    "mkEqRefl rhs",
    "Lean.addDecl (.thmDecl",
]

# G3 thresholds, fixed now.
H10_1_UPPER = 0.90   # first-unfold/floor ratio above which H10.1 is rejected
H10_2_LOWER = 0.60   # ... below which H10.2 is rejected
G5_TOLERANCE = 0.10  # H10.3 control tolerance


def _impl_def(empty: bool) -> str:
    """The `impl` under test. Unary Nat -> Nat, so the theorem keeps the judge's
    exact unary `Lean.mkApp implC (Lean.mkNatLit k)` shape.

    empty=True  : every branch returns 0 -- the ladder measures UNFOLDING only.
    empty=False : `impl k = k`, i.e. one `Nat.add` per unfold -- the H10.3
                  control that must reproduce F5b's 121,537 instr/step.
    """
    if empty:
        return """namespace F10Impl
def impl : Nat → Nat
  | 0 => 0
  | n + 1 => 0
end F10Impl"""
    # The `n + 1` pattern is `Nat.succ n`, so the binder `n` IS the predecessor.
    # An unnamed `_` here would silently recurse on the WRONG argument: with
    # `impl (_ - 1)` the function computes impl (n+1) = impl (n-1) + 1, which
    # returns 1 for every k >= 1 and makes the self-validating theorem
    # `impl 2 = 2` fail. Named binders, as F5's `iterAdd` used.
    return """namespace F10Impl
def impl : Nat → Nat
  | 0 => 0
  | n + 1 => impl n + 1
end F10Impl"""


def probe_source(k: int, value: int, theorem: str, empty: bool) -> str:
    """`impl k = value` in the judge\'s own generated-theorem shape.

    Reproduces `evaluation/judge/judge.py::_perf_theorem_source` verbatim in the
    parts that determine the cost: the unary application, the raw `Nat` literal
    for the expected value, `mkEq`/`mkEqRefl`, and `Lean.addDecl` with the proof
    as the declaration value -- so the KERNEL alone type-checks it and must reduce
    `impl k` itself, exactly as the judge scores.
    """
    return f"""import Spec
import Lean
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
{_impl_def(empty)}
open Lean Meta Elab in
run_meta do
  let implC := Lean.mkConst ``F10Impl.impl
  let lhs := Lean.mkApp implC (Lean.mkNatLit {k})
  let out ← whnf (← inferType implC).bindingBody!
  let outIsInt := out.isConstOf ``Int
  unless outIsInt || out.isConstOf ``Nat do
    throwError "unsupported impl output type {{out}}"
  let rhs := Lean.mkNatLit {value}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def assert_form(src: str, key: str) -> None:
    """G4. A probe of a different shape cannot answer the question, so this is a
    hard failure rather than a warning."""
    missing = [frag for frag in REQUIRED_FORMS if frag not in src]
    if missing:
        raise ProbeError(f"[G4 shape] {key}: probe source lacks {missing}")


def fit_lin(points: list[tuple[int, int]]):
    """Least squares c = a + b*k, with the standard error of b and the worst
    relative residual. Same estimator F5 used, so the numbers are comparable."""
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
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f10-run"
    work.mkdir(parents=True, exist_ok=True)

    print(f"timer: {TIMER_BIN}   reps={REPS}", flush=True)
    print(f"ladder k={LADDER}", flush=True)
    print("references (NOT inputs): F8 floor 118,230 | F9 add 206,328 | "
          "F5b add1 121,537/step", flush=True)
    print("G4 shape assertion on every probe; G5 instrument-drift control on "
          "Series B.\n", flush=True)

    cells: dict[str, dict] = {}

    def record(key: str, src: str, theorem: str, extra: dict) -> bool:
        t0 = time.time()
        try:
            assert_form(src, key)
            export = build_and_export(pdir, src, theorem, work, module="F10Probe")
            res = replay(pdir, export, theorem, REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:      # G2
                res = replay(pdir, export, theorem, REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cost = res["window_median"]
            cells[key] = dict(extra, status="ok", window_median=cost,
                              window_instructions=res["window_instructions"],
                              window_min=res["window_min"],
                              window_max=res["window_max"],
                              window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                              seconds=round(time.time() - t0, 2))
            print(f"  {key:<16} {cost:>11,.0f} instr   spread="
                  f"{res['window_spread_pct']:.2f}%   ({cells[key]['seconds']}s)",
                  flush=True)
        except ProbeError as exc:
            out = outdir / "f10_floor_once_or_per_unfold.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": key,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"  {key:<16} ABORT: {str(exc)[:300]}\nG1 TRIGGERED -> {out}",
                  flush=True)
            return False
        return True

    # --- Series A (decisive): empty body, so k isolates UNFOLDING. -----------
    for k in LADDER:
        if not record(f"A-empty@{k}", probe_source(k, 0, "F10Probe.check", empty=True),
                      "F10Probe.check", {"series": "A", "body": "empty", "k": k,
                                         "value": 0}):
            return 1

    # --- Series B (H10.3 control): one Nat.add per unfold, must reproduce F5b.
    for k in LADDER:
        if not record(f"B-add1@{k}", probe_source(k, k, "F10Probe.check", empty=False),
                      "F10Probe.check", {"series": "B", "body": "add1", "k": k,
                                         "value": k}):
            return 1

    ok = {k: c for k, c in cells.items() if c.get("status") == "ok"}
    A = sorted((c["k"], c["window_median"]) for k, c in ok.items()
               if c["series"] == "A")
    B = sorted((c["k"], c["window_median"]) for k, c in ok.items()
               if c["series"] == "B")

    c0 = dict(A).get(0)
    c1 = dict(A).get(1)
    first_unfold = (c1 - c0) if (c0 and c1) else None
    ratio = (first_unfold / c0) if (first_unfold is not None and c0) else None

    aA, bA, seA, residA = fit_lin(A)
    aB, bB, seB, residB = fit_lin(B)
    if (aA is None or bA is None or aB is None or bB is None
            or c0 is None or c1 is None or first_unfold is None or ratio is None):
        out = outdir / "f10_floor_once_or_per_unfold.json"
        out.write_text(json.dumps({"status": "incomplete", "ladder_A": A,
                                   "ladder_B": B, "cells": cells}, indent=1))
        print(f"\nINCOMPLETE -- not enough cells for a fit or the k=0/k=1 pair; "
              f"nothing is written as a number. See {out}", flush=True)
        return 1

    verdicts: list[str] = []
    inst = max(c["window_spread_pct"] for c in ok.values())
    verdicts.append(f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
                    f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}")

    # --- G5 first: a drifted instrument voids everything downstream. ---------
    drift = abs(bB - F5B_ADD1_PER_STEP) / F5B_ADD1_PER_STEP if bB else float("inf")
    if drift <= G5_TOLERANCE:
        verdicts.append(
            f"G5 H10.3 control    : Series B marginal = {bB:,.0f} instr/step vs "
            f"F5b {F5B_ADD1_PER_STEP:,} = {bB/F5B_ADD1_PER_STEP:.3f}x "
            f"(tolerance {G5_TOLERANCE:.0%}) -> instrument CONSISTENT")
        drifted = False
    else:
        verdicts.append(
            f"G5 H10.3 control    : Series B marginal = {bB:,.0f} instr/step vs "
            f"F5b {F5B_ADD1_PER_STEP:,} = {bB/F5B_ADD1_PER_STEP:.3f}x, drift "
            f"{drift:.1%} > {G5_TOLERANCE:.0%} -> run DRIFTED, verdicts below VOID")
        drifted = True

    # --- G3, the decisive test. ---------------------------------------------
    if ratio is None:
        verdicts.append("G3 decisive         : no c(0)/c(1) pair -> UNRESOLVED")
        h101 = h102 = "UNRESOLVED"
    elif ratio >= H10_1_UPPER:
        verdicts.append(
            f"G3 decisive         : first unfold costs {first_unfold:,.0f} instr = "
            f"{ratio:.3f}x c(0) (>= {H10_1_UPPER}) -> H10.1 REJECTED. The floor "
            f"IS charged per unfold.")
        h101, h102 = "REJECTED", "NOT rejected"
    elif ratio < H10_2_LOWER:
        verdicts.append(
            f"G3 decisive         : first unfold costs {first_unfold:,.0f} instr = "
            f"{ratio:.3f}x c(0) (< {H10_2_LOWER}) -> H10.2 REJECTED. The floor is "
            f"paid ONCE per declaration.")
        h101, h102 = "NOT rejected", "REJECTED"
    else:
        verdicts.append(
            f"G3 decisive         : first unfold costs {first_unfold:,.0f} instr = "
            f"{ratio:.3f}x c(0), between {H10_2_LOWER} and {H10_1_UPPER} -> "
            f"UNRESOLVED. Neither H10.1 nor H10.2 survives; G7 forbids averaging.")
        h101 = h102 = "UNRESOLVED"

    verdicts.append(
        "G4 shape assertion  : every probe carried mkApp implC (mkNatLit ...), "
        "mkEq/mkEqRefl, addDecl .thmDecl, maxRecDepth 4000000, maxHeartbeats 0. "
        "No probe was substituted.")
    verdicts.append(
        f"G6 scope            : these are USER-SPACE counts (LK_EXCLUDE_KERNEL=1). "
        f"The judge counts user+kernel, so the absolute {CHAMPION_SLOT:,} "
        f"(champion slot) is NOT compared here; only ratios to this run's c(0) "
        f"are quotable.")

    payload = {
        "status": "ok" if not drifted else "ok_but_drifted",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "scope": "user-space only (LK_EXCLUDE_KERNEL=1)",
                       "harness": "identical to F5/F8/F9",
                       "probe_shape": "judge's own _perf_theorem_source form"},
        "references_not_inputs": {"f8_floor": F8_FLOOR, "f9_add_small": F9_ADD_SMALL,
                                  "f5b_add1_per_step": F5B_ADD1_PER_STEP,
                                  "champion_slot": CHAMPION_SLOT},
        "preregistered": {
            "H10.1": "floor paid ONCE per declaration",
            "H10.2": "floor charged PER UNFOLD",
            "H10.3": "Series B reproduces F5b's 121,537 instr/step within 10%",
            "criteria": {
                "G1": "abort on failed cell", "G2": "spread > 5% -> re-measure",
                "G3": {"H10.1_reject_if_ratio_ge": H10_1_UPPER,
                       "H10.2_reject_if_ratio_lt": H10_2_LOWER,
                       "between": "UNRESOLVED, no blending (G7)"},
                "G4": "assert the judge's constructs are present in every source",
                "G5": "void the run if Series B drifts > 10% from F5b",
                "G6": "never compare absolutes to the leaderboard; ratios only",
                "G7": "report negatives with the same detail as positives"},
        },
        "verdicts": {"H10.1": h101, "H10.2": h102,
                     "H10.3": "CONSISTENT" if not drifted else "DRIFTED -- VOID"},
        "ladder_A_empty": A,
        "ladder_B_add1": B,
        "fit_A": {"alpha": aA, "beta_instr_per_step": bA, "se_beta": seA,
                  "worst_residual_pct": residA},
        "fit_B": {"alpha": aB, "beta_instr_per_step": bB, "se_beta": seB,
                  "worst_residual_pct": residB},
        "decisive": {"c0_A": c0, "c1_A": c1, "first_unfold_instr": first_unfold,
                     "first_unfold_over_c0": ratio,
                     "g5_drift": drift},
        "cells": cells,
    }
    out = outdir / "f10_floor_once_or_per_unfold.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        "F10 -- is the 118k floor paid ONCE per declaration or PER UNFOLD? (2026-10-05)",
        "",
        "metric: instructions inside KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "scope : USER-SPACE only (LK_EXCLUDE_KERNEL=1) -- ratios only, G6",
        "shape : the judge's own _perf_theorem_source form (G4 asserted)",
        "",
        f"{'k (unfolds)':>12}{'A empty body':>16}{'A fitted':>12}"
        f"{'B add1 body':>16}{'B fitted':>12}",
    ]
    fA = {k: aA + bA * k for k in range(LADDER[0], LADDER[-1] + 1)} if aA else {}
    fB = {k: aB + bB * k for k in range(LADDER[0], LADDER[-1] + 1)} if aB else {}
    for k in LADDER:
        da, db = dict(A).get(k), dict(B).get(k)
        lines.append(f"{k:>12}{(f'{da:,.0f}' if da else 'FAILED'):>16}"
                     f"{(f'{fA[k]:,.0f}' if fA else '-'):>12}"
                     f"{(f'{db:,.0f}' if db else 'FAILED'):>16}"
                     f"{(f'{fB[k]:,.0f}' if fB else '-'):>12}")
    lines += [
        "",
        f"Series A fit: {aA:,.0f} + ({bA:,.0f} +- {seA:,.0f}) * k   "
        f"worst residual {residA:.1f}%",
        f"Series B fit: {aB:,.0f} + ({bB:,.0f} +- {seB:,.0f}) * k   "
        f"worst residual {residB:.1f}%",
        "",
        f"DECISIVE: c(0)={c0:,.0f}  c(1)={c1:,.0f}  first unfold={first_unfold:,.0f}"
        f"  = {ratio:.3f}x c(0)",
        "",
        "VERDICTS (criteria pre-registered in scripts/f10_floor_once_or_per_unfold.py)",
    ] + [f"  {v}" for v in verdicts] + ["", f"wrote {out}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f10_floor_once_or_per_unfold.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())