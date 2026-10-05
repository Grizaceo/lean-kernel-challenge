#!/usr/bin/env python3
"""F10b -- CORRECTION of F10. The F10 Series A ladder was VOID; this fixes the probe.

PRE-REGISTERED 2026-10-05, BEFORE ANY NUMBER IS PRODUCED. Committed before the run.

WHY F10's SERIES A WAS VOID (and why I did not report it as a result)
--------------------------------------------------------------------
F10 measured an "empty body" ladder and got a flat curve:

    k        0        1        2        3        5        10
    A    239,705  279,826  280,101  280,236  279,837  279,491     (spread 0.27%)

Its G3 test then read c(1)-c(0) = 40,121 = 0.167x c(0) and declared "the floor
is paid ONCE per declaration". That conclusion is NOT supported, and the probe
is the reason:

    def impl : Nat -> Nat
      | 0 => 0
      | n + 1 => 0            <-- returns a CONSTANT

To reduce `impl 5` the kernel matches on 5, takes branch 2, and is handed the
literal 0. It has its answer and STOPS. It never applies `impl` to 4, 3, 2, 1.
k=1..10 are all the SAME computation -- one match, then a constant -- so the flat
curve is not "unfolding is free", it is "the ladder never unfolded past depth 1".

The build did not fail and the self-validating theorem was true, which is exactly
why this slipped through: G1 (a cell that fails aborts) cannot catch a probe that
compiles, type-checks, and measures -- but does not exercise the thing under test.
F10's own Series B proves the mechanism: `impl n + 1` DOES force depth, and it
reproduced F5b's 121,537 instr/step at 1.006x, so the instrument is sound and only
the Series A probe was wrong.

This is the F5/F8 lesson ("a k=0 that contains a recursor is not a floor") applied
one level deeper: a ladder whose body does not force recursion is not a ladder of
unfolds, it is a ladder of matches.

THE FIX
-------
Three bodies, all with the judge's own theorem shape (G4), so the ladder measures
unfold RECURRENCE and not match entry:

  C  constant-empty : `| n + 1 => 0`          depth 1 regardless of k  (F10's A)
  A  recursive-empty: `| n + 1 => impl n`     k nested applications   (the fix)
  B  add1           : `| n + 1 => impl n + 1` k applications + k adds (F10's B)

`A - C` isolates everything the ladder does BEYOND the first match, which is
precisely the quantity the F8/F9 tension turns on. `B - A` is the marginal cost of
one `Nat.add` inside a step, and is the control against F5b.

PREREGISTERED HYPOTHESES
------------------------
H10.1  The floor is paid ONCE per declaration; per-unfold cost is small and does
       not repay the fixed cost. Prediction: the marginal per unfold (Series A's
       beta) is well below the floor c(0).

H10.2  The floor is charged PER UNFOLD; each unfold repays the fixed cost.
       Prediction: beta is comparable to c(0).

H10.4  The per-unfold cost is NOT the ~99,648 that F5b's `empty` body implied, and
       NOT the ~121,247 that F5's ladder implied; F5's ladder was measuring
       "unfold + one add" because its body was `acc + 1`. Prediction from F10's
       measured B - A: if the add-inside-a-step costs ~21,889 (F5b's own
       add1-minus-empty figure, 2,188,857 / 100) then beta_A should land near
       99,648 - 21,889 ~ 78k. Reported either way.

FALSIFICATION CRITERIA (fixed before the run)
---------------------------------------------
G1  A cell that fails to build, export or complete the replay ABORTS the run.
G2  Intra-cell spread > 5% -> re-measure once, then report with its spread.
G3  DECISIVE on Series A: H10.1 rejected if (c(1)-c(0)) >= 0.90 * c(0);
       H10.2 rejected if (c(1)-c(0)) < 0.60 * c(0); between -> UNRESOLVED,
       explicitly not blended (G7).
G4  SHAPE ASSERTION: every probe source must contain the judge's constructs
       verbatim -- mkApp implC (mkNatLit, mkEq lhs rhs, mkEqRefl rhs,
       addDecl (.thmDecl, maxRecDepth 4000000, maxHeartbeats 0.
G5  INSTRUMENT CONTROL: Series B's marginal must be within 10% of F5b's
       121,537 instr/step; otherwise the run is DRIFTED and every verdict is void.
G6  SCOPE: user-space only (LK_EXCLUDE_KERNEL=1). Never compare an absolute here
       to a leaderboard slot. Ratios to this run's own c(0) only.
G7  Report negatives with the same detail as positives; UNRESOLVED stays unresolved.
G8  **THE LADDER MUST ACTUALLY TRAVERSE.** Series A is VOID unless it is strictly
       increasing in k with beta > 3 standard errors (z > 3). A flat A is the
       F10 signature of a body that returns a constant, and the run reports the
       probe defect rather than a cost law. This guard exists because G1 cannot
       catch a probe that compiles, type-checks, and measures the wrong thing.
G9  A Cell that is accidentally the same computation as another cell (A
       statistically indistinguishable from C at every k) is evidence of a
       probe defect, not of a cost law, and is reported as such.

MEASUREMENT
-----------
`instructions` from the official timer's KERNEL_TIMING at the
`target-declaration-replay-v1` boundary. Instrument identical to F5/F8/F9/F10:
`.verify/timer-kernel-local`, LK_EXCLUDE_KERNEL=1, median of 3, no subtraction.
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

LADDER = [0, 1, 2, 3, 5, 10]
REPS = 3

# Prior measurements: references and controls only, never inputs.
F8_FLOOR = 118_230            # F8 A-const-refl: bare Eq.refl between literals
F10A_C0 = 239_705             # F10 Series A k=0, judge shape, invalid ladder
F10A_C1 = 279_826             # F10 Series A k=1  (== "one match")
F10_BETA = 122_250            # F10 Series B marginal (add per unfold)
F5B_ADD1_PER_STEP = 121_537   # F5b add1 at k=100
F5B_EMPTY_PER_STEP = 99_648   # F5b empty at k=100
F5B_ADD_MINUS_EMPTY = (12_613_248 - 10_424_391) / 100   # 21,889/step
CHAMPION_SLOT = 238_082       # partition rank1 1,428,492 / 6 (user+kernel scope)

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

H10_1_UPPER = 0.90
H10_2_LOWER = 0.60
G5_TOLERANCE = 0.10
G8_Z_MIN = 3.0

BODIES = {
    # name: (definition body, value for a given k, what it forces)
    "C": ("| 0 => 0\n  | n + 1 => 0", 0,
          "constant body: the kernel matches once and is DONE, at every k"),
    "A": ("| 0 => 0\n  | n + 1 => impl n", 0,
          "recursive-empty: k NESTED applications, zero arithmetic"),
    "B": ("| 0 => 0\n  | n + 1 => impl n + 1", None,
          "k applications + k adds (the F5/F5b shape)"),
}


def probe_source(k: int, theorem: str, body: str) -> str:
    """`impl k = v` in the judge's own generated-theorem shape.

    The `n + 1` pattern is `Nat.succ n`, so the binder `n` IS the predecessor.
    An unnamed `_` would recurse on the wrong argument: `impl (_ - 1)` computes
    impl (n+1) = impl (n-1) + 1, which returns 1 for every k >= 1 and makes the
    self-validating theorem `impl 2 = 2` fail.
    """
    return f"""import Spec
import Lean
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
namespace F10Impl
def impl : Nat → Nat
  {body}
end F10Impl
open Lean Meta Elab in
run_meta do
  let implC := Lean.mkConst ``F10Impl.impl
  let lhs := Lean.mkApp implC (Lean.mkNatLit {k})
  let out ← whnf (← inferType implC).bindingBody!
  let outIsInt := out.isConstOf ``Int
  unless outIsInt || out.isConstOf ``Nat do
    throwError "unsupported impl output type {{out}}"
  let rhs := Lean.mkNatLit {k if body == BODIES["B"][0] else 0}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def assert_form(src: str, key: str) -> None:
    missing = [frag for frag in REQUIRED_FORMS if frag not in src]
    if missing:
        raise ProbeError(f"[G4 shape] {key}: probe source lacks {missing}")


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
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f10b-run"
    work.mkdir(parents=True, exist_ok=True)

    print(f"timer: {TIMER_BIN}   reps={REPS}", flush=True)
    print(f"ladder k={LADDER}", flush=True)
    print("G8: Series A is VOID unless it strictly increases with z(beta) > 3.", flush=True)
    print("references: F8 floor 118,230 | F5b empty 99,648/step | "
          "F5b add1 121,537/step | F10 B 122,250/step\n", flush=True)

    cells: dict[str, dict] = {}

    def record(key: str, src: str, extra: dict) -> bool:
        t0 = time.time()
        try:
            assert_form(src, key)
            export = build_and_export(pdir, src, "F10Probe.check", work, module="F10Probe")
            res = replay(pdir, export, "F10Probe.check", REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:            # G2
                res = replay(pdir, export, "F10Probe.check", REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cells[key] = dict(extra, status="ok", window_median=res["window_median"],
                              window_instructions=res["window_instructions"],
                              window_min=res["window_min"],
                              window_max=res["window_max"],
                              window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                              seconds=round(time.time() - t0, 2))
            print(f"  {key:<14} {res['window_median']:>11,.0f} instr   "
                  f"spread={res['window_spread_pct']:.2f}%   "
                  f"({cells[key]['seconds']}s)", flush=True)
        except ProbeError as exc:
            out = outdir / "f10b_traversal_ladder.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": key,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"  {key:<14} ABORT: {str(exc)[:300]}\nG1 TRIGGERED -> {out}",
                  flush=True)
            return False
        return True

    for series, (body, _val, what) in BODIES.items():
        for k in LADDER:
            if not record(f"{series}@{k}", probe_source(k, "F10Probe.check", body),
                          {"series": series, "k": k, "forces": what}):
                return 1

    ok = {k: c for k, c in cells.items() if c.get("status") == "ok"}
    ladders = {s: sorted((c["k"], c["window_median"]) for k, c in ok.items()
                         if c["series"] == s) for s in BODIES}
    fits = {s: fit_lin(ladders[s]) for s in BODIES}
    C, A, B = (dict(ladders[s]) for s in ("C", "A", "B"))

    c0, c1 = A.get(0), A.get(1)
    first_unfold = (c1 - c0) if (c0 and c1) else None
    ratio = (first_unfold / c0) if (first_unfold is not None and c0) else None

    verdicts: list[str] = []
    inst = max(c["window_spread_pct"] for c in ok.values())
    verdicts.append(f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
                    f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}")

    # --- G8 FIRST: did the ladder actually traverse? -------------------------
    aA, bA, seA, residA = fits["A"]
    zA = (bA / seA) if (bA and seA not in (None, 0, float("inf"))) else float("inf")
    a_void = False
    if bA is None or zA <= G8_Z_MIN:
        a_void = True
        verdicts.append(
            f"G8 ladder traverses : Series A beta = {bA if bA is None else f'{bA:,.0f}'} "
            f"+- {seA if seA is None else f'{seA:,.0f}'}, z = {zA:.2f} "
            f"(needs > {G8_Z_MIN}) -> Series A VOID: the body did not force k "
            f"unfolds. F10's failure mode reproduced. No cost law from A.")
    else:
        verdicts.append(
            f"G8 ladder traverses : Series A beta = {bA:,.0f} +- {seA:,.0f} "
            f"(z = {zA:.1f} > {G8_Z_MIN}) -> the body DID force k unfolds; A is valid")

    # --- G9: is A just C again? --------------------------------------------
    deltas = {k: (A[k] - C[k]) for k in A if k in C}
    max_rel = max(abs(d) / C[k] for k, d in deltas.items()) if deltas else float("inf")
    if max_rel < 0.02:
        verdicts.append(
            f"G9 A distinct from C: A-C is within {max_rel:.1%} of C at every k -> "
            f"A measures the SAME computation as C. Probe defect, not a cost law.")
    else:
        verdicts.append(
            f"G9 A distinct from C: A-C reaches {max_rel:.1%} of C's cost, so the "
            f"recursive body really does extra work beyond the first match")

    # --- G5 control: B must reproduce F5b ----------------------------------
    bB, seB = fits["B"][1], fits["B"][2]
    if bB is None:
        drift = float("inf")
        drifted = True
        verdicts.append("G5 instrument ctl   : Series B did not fit -> DRIFTED, "
                        "verdicts below VOID")
    else:
        drift = abs(bB - F5B_ADD1_PER_STEP) / F5B_ADD1_PER_STEP
        drifted = drift > G5_TOLERANCE
        verdicts.append(
            f"G5 instrument ctl   : Series B marginal = {bB:,.0f} instr/step vs F5b "
            f"{F5B_ADD1_PER_STEP:,} = {bB/F5B_ADD1_PER_STEP:.3f}x "
            f"(tol {G5_TOLERANCE:.0%}) -> "
            f"{'DRIFTED, verdicts below VOID' if drifted else 'instrument CONSISTENT'}")

    # --- G3 decisive, only if A survived G8 ---------------------------------
    if a_void:
        verdicts.append("G3 decisive         : Series A void under G8 -> UNRESOLVED")
        h101 = h102 = "UNRESOLVED (A void)"
    elif ratio is None:
        verdicts.append("G3 decisive         : no c(0)/c(1) -> UNRESOLVED")
        h101 = h102 = "UNRESOLVED"
    elif ratio >= H10_1_UPPER:
        verdicts.append(
            f"G3 decisive         : first unfold = {first_unfold:,.0f} = {ratio:.3f}x "
            f"c(0) (>= {H10_1_UPPER}) -> H10.1 REJECTED; the floor IS charged per unfold")
        h101, h102 = "REJECTED", "NOT rejected"
    elif ratio < H10_2_LOWER:
        verdicts.append(
            f"G3 decisive         : first unfold = {first_unfold:,.0f} = {ratio:.3f}x "
            f"c(0) (< {H10_2_LOWER}) -> H10.2 REJECTED; the floor is paid ONCE")
        h101, h102 = "NOT rejected", "REJECTED"
    else:
        verdicts.append(
            f"G3 decisive         : first unfold = {first_unfold:,.0f} = {ratio:.3f}x "
            f"c(0), between {H10_2_LOWER} and {H10_1_UPPER} -> UNRESOLVED, not blended (G7)")
        h101 = h102 = "UNRESOLVED"

    # --- H10.4 reconciliation ---------------------------------------------
    if bA and bB:
        add_in_step = bB - bA
        verdicts.append(
            f"H10.4 body tax      : add inside a step = B-beta - A-beta = "
            f"{bB:,.0f} - {bA:,.0f} = {add_in_step:,.0f} instr/step vs F5b's own "
            f"add1-minus-empty {F5B_ADD_MINUS_EMPTY:,.0f} = "
            f"{add_in_step/F5B_ADD_MINUS_EMPTY:.2f}x")
        verdicts.append(
            f"H10.4 vs F5b empty  : A-beta = {bA:,.0f} vs F5b's empty "
            f"{F5B_EMPTY_PER_STEP:,} = {bA/F5B_EMPTY_PER_STEP:.3f}x; and F5's ladder "
            f"beta {F10_BETA:,.0f} (F10 B) vs F5b add1 {F5B_ADD1_PER_STEP:,} = "
            f"{F10_BETA/F5B_ADD1_PER_STEP:.3f}x -> F5's '121k per unfold' was "
            f"'unfold + one add'")
    else:
        add_in_step = None

    verdicts.append(
        "G4 shape assertion  : every probe carried mkApp implC (mkNatLit ...), "
        "mkEq/mkEqRefl, addDecl .thmDecl, maxRecDepth 4000000, maxHeartbeats 0")
    verdicts.append(
        f"G6 scope            : USER-SPACE counts (LK_EXCLUDE_KERNEL=1). The judge "
        f"counts user+kernel, so {CHAMPION_SLOT:,} is NOT compared to these "
        f"absolutes; only ratios to this run's c(0) are quotable")

    payload = {
        "status": "ok" if not (drifted or a_void) else "ok_but_void_cells",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "supersedes": "f10_floor_once_or_per_unfold.json (Series A void: constant body)",
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "scope": "user-space only (LK_EXCLUDE_KERNEL=1)",
                       "harness": "identical to F5/F8/F9/F10",
                       "probe_shape": "judge's own _perf_theorem_source form"},
        "references_not_inputs": {
            "f8_floor": F8_FLOOR, "f10_A_c0_INVALID": F10A_C0,
            "f10_A_c1_INVALID": F10A_C1, "f10_B_beta": F10_BETA,
            "f5b_empty_per_step": F5B_EMPTY_PER_STEP,
            "f5b_add1_per_step": F5B_ADD1_PER_STEP,
            "f5b_add_minus_empty": F5B_ADD_MINUS_EMPTY,
            "champion_slot": CHAMPION_SLOT},
        "preregistered": {
            "H10.1": "floor paid ONCE per declaration",
            "H10.2": "floor charged PER UNFOLD",
            "H10.4": "per-unfold cost is neither F5b's 99,648 nor F5's 121,247",
            "criteria": {
                "G1": "abort on failed cell", "G2": "spread > 5% -> re-measure",
                "G3": {"H10.1_reject_if_ratio_ge": H10_1_UPPER,
                       "H10.2_reject_if_ratio_lt": H10_2_LOWER,
                       "between": "UNRESOLVED, no blending (G7)"},
                "G4": "assert judge constructs present in every source",
                "G5": "void run if B drifts > 10% from F5b",
                "G6": "ratios only, never slot-to-slot with leaderboard",
                "G7": "negatives reported with the same detail",
                "G8": f"Series A VOID unless z(beta) > {G8_Z_MIN}",
                "G9": "A indistinguishable from C => probe defect"}},
        "verdicts": {"H10.1": h101, "H10.2": h102,
                     "G5_control": "DRIFTED" if drifted else "CONSISTENT",
                     "G8_series_A": "VOID" if a_void else "VALID"},
        "ladders": ladders,
        "fits": {s: {"alpha": fits[s][0], "beta_instr_per_step": fits[s][1],
                     "se_beta": fits[s][2], "worst_residual_pct": fits[s][3]}
                 for s in BODIES},
        "decisive": {"c0_A": c0, "c1_A": c1, "first_unfold_instr": first_unfold,
                     "first_unfold_over_c0": ratio, "z_A": zA,
                     "add_inside_step_instr": add_in_step, "g5_drift": drift,
                     "A_minus_C": deltas},
        "cells": cells,
    }
    out = outdir / "f10b_traversal_ladder.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        "F10b -- the traversal-corrected ladder (2026-10-05)",
        "",
        "SUPERSEDES F10 Series A, which was VOID: its body returned a constant, so",
        "the kernel matched once and stopped at every k. G8 now voids any flat ladder.",
        "",
        "metric: instructions inside KERNEL_TIMING, target-declaration-replay-v1",
        "scope : USER-SPACE only (LK_EXCLUDE_KERNEL=1) -- ratios only, G6",
        "",
        f"{'k':>4}{'C constant':>13}{'A recur-empty':>16}{'B add1':>13}"
        f"{'A - C':>11}{'B - A':>11}",
    ]
    for k in LADDER:
        c_, a_, b_ = C.get(k), A.get(k), B.get(k)
        lines.append(
            f"{k:>4}{(f'{c_:,.0f}' if c_ else 'FAILED'):>13}"
            f"{(f'{a_:,.0f}' if a_ else 'FAILED'):>16}"
            f"{(f'{b_:,.0f}' if b_ else 'FAILED'):>13}"
            f"{(f'{a_-c_:,.0f}' if (a_ and c_) else '-'):>11}"
            f"{(f'{b_-a_:,.0f}' if (b_ and a_) else '-'):>11}")
    lines += [
        "",
        f"fit A: {aA:,.0f} + ({bA:,.0f} +- {seA:,.0f})*k   z={zA:.2f}   "
        f"resid {residA:.1f}%",
        f"fit B: {fits['B'][0]:,.0f} + ({bB:,.0f} +- {seB:,.0f})*k   "
        f"resid {fits['B'][3]:.1f}%",
        f"fit C: {fits['C'][0]:,.0f} + ({fits['C'][1]:,.0f} +- {fits['C'][2]:,.0f})*k",
        "",
        f"DECISIVE: c(0)={c0:,.0f}  c(1)={c1:,.0f}  first unfold={first_unfold:,.0f}"
        f" = {ratio:.3f}x c(0)",
        "",
        "VERDICTS (pre-registered in scripts/f10b_traversal_ladder.py)",
    ] + [f"  {v}" for v in verdicts] + ["", f"wrote {out}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f10b_traversal_ladder.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())