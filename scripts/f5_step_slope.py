#!/usr/bin/env python3
"""F5 -- the MARGINAL cost of a kernel reduction step. Pre-registered 2026-10-05.

WHY THIS EXPERIMENT EXISTS
---------------------------
F2 (results/cost_model/) measured the cost of ONE `Nat.<op> a b = v` as a
function of the operand WIDTH, at a fixed number of operations. It found a
plateau of ~234k-248k instructions per replayed declaration and a +6.0% step at
63 bits.

It never varied the NUMBER of reduction steps. That is the quantity every
optimisation strategy in this competition implicitly assumes it knows: ca-rule110
was attributed to "structural recursion", primecount to "count recursing once
per prime found", partition to "the outer row rebuild". All three claims are
assertions about a slope that has never been measured.

There is also an unresolved contradiction on the board. F2 says a single theorem
replay costs ~234k. The partition leader's curveWork is 1,428,492 over 6 slots
= ~238k per slot, i.e. about ONE F2-sized theorem per slot. But the largest
scored partition input is n~36, and p(36)=17977 needs on the order of a
hundred additions under Euler's recurrence. If a single operation really cost
234k, the honest arithmetic would be tens of millions per slot. Either the
marginal cost per step is far below 234k -- in which case F2's plateau is
dominated by something that does not scale and every cost model here is
mis-calibrated -- or the leaderboard's top is not doing that arithmetic.

Both readings are actionable and neither needs judge quota. This experiment
settles which one is true.

PREREGISTRATION (fixed before any number is produced)
----------------------------------------------------
H5.1  c(k) = alpha + beta*k is LINEAR in the number of kernel reduction steps k.
      Supporting: nothing yet. This is the hypothesis under test.

H5.2  alpha (cost of a replayed declaration at k=0) DOMINATES: beta * k is a
      minority of the slot cost for any k the leaders actually run. F2's
      reading says alpha ~ 234k.

H5.3  The 63-bit step found by F2 is a property of the OPERAND LITERAL, not of
      the operation: at k=1 with tiny operands the cost drops to the k=0
      plateau. Control for H5.1's design -- if k=1 small-operand and k=1
      65-bit-operand cost the same, F2 was measuring literal reduction.

FALSIFICATION CRITERIA (declared up front, before any run)
----------------------------------------------------------
G1  A cell that fails to build, export, or complete the replay ABORTS the run.
    A failed cell is never written as a number. (Same rule as F2/F1: the
    previous table was invalidated by lean4export PANICking with rc=0.)
G2  If intra-cell spread > 5%, re-measure once; if it still exceeds 5%, report
    the cell WITH its spread rather than as a point value.
G3  H5.1 is REJECTED if beta's fit residual exceeds 5% of the value.
G4  H5.1 is reported as UNRESOLVED -- explicitly not as "linear" -- if beta is
    smaller than its own standard error. This is the criterion that stops a
    flat curve from being read as a zero slope with infinite headroom.
G5  H5.2 is REJECTED if beta*k exceeds alpha at the largest k measured.

MEASUREMENT DEFINITION
----------------------
`instructions` from the official timer's KERNEL_TIMING record, at the
`target-declaration-replay-v1` boundary -- the boundary the remote judge
scores. No subtraction, no baseline. Operand widths stay SMALL in the main
series so that the measured slope is attributable to step count alone.
"""
from __future__ import annotations

import json
import statistics
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from f2_harness import (COUNT_INSTRUCTIONS, TIMER_BIN, ProbeError,  # noqa: E402
                        build_and_export, problem_dir, replay)

# The reduction-step ladder. `iterAdd` walks k structural-recursion steps and
# does one trivial addition per step, so k is exactly the number of reduction
# steps the kernel must perform. Every operand stays in one machine word.
LADDER = [0, 1, 2, 5, 10, 25, 50, 100, 250, 500]
REPS = 3

ITER_ADD = """
def iterAdd : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => iterAdd n (acc + 1)
"""


def probe_source_steps(k: int, theorem: str) -> str:
    """A theorem whose LHS is exactly k structural-recursion reduction steps."""
    return f"""import Spec
import Lean
{ITER_ADD}
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp2 (Lean.mkConst ``iterAdd) (Lean.mkNatLit {k}) (Lean.mkNatLit 0)
  let rhs := Lean.mkNatLit {k}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def probe_source_lhs(app: str, value: int, theorem: str) -> str:
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := {app}
  let rhs := Lean.mkNatLit {value}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def fit_lin(points):
    """Least squares c = alpha + beta*k with the residual and the standard
    error of beta. The standard error is what G4 turns on: without it a flat
    curve and a small positive slope are indistinguishable."""
    xs = [float(x) for x, _ in points]
    ys = [float(y) for _, y in points]
    n = len(xs)
    if n < 3:
        raise ValueError(f"need >=3 points for a slope, got {n}")
    mx, my = statistics.mean(xs), statistics.mean(ys)
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    beta = sxy / sxx
    alpha = my - beta * mx
    resid = [y - (alpha + beta * x) for x, y in zip(xs, ys)]
    worst = max(abs(r) / y * 100 for r, y in zip(resid, ys))
    sse = sum(r * r for r in resid)
    if n > 2 and sxx > 0:
        s2 = sse / (n - 2)
        se_beta = (s2 / sxx) ** 0.5
    else:
        se_beta = float("inf")
    return alpha, beta, se_beta, worst


def main() -> int:
    pdir = problem_dir("partition")
    outdir = ROOT / "results" / "cost_model"
    outdir.mkdir(parents=True, exist_ok=True)
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f5-run"
    work.mkdir(parents=True, exist_ok=True)

    print(f"timer      : {TIMER_BIN}", flush=True)
    print(f"instructions metric: {COUNT_INSTRUCTIONS}", flush=True)
    print(f"ladder k={LADDER} reps={REPS}\n", flush=True)

    cells: dict[str, dict] = {}

    def record(key: str, src: str, theorem: str, extra: dict) -> bool:
        t0 = time.time()
        try:
            export = build_and_export(pdir, src, theorem, work, module="F5Probe")
            res = replay(pdir, export, theorem, REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if res["window_spread_pct"] and res["window_spread_pct"] > 5:
                res = replay(pdir, export, theorem, REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cells[key] = dict(
                extra,
                export_bytes=export.stat().st_size,
                window_instructions=res["window_instructions"],
                window_median=res["window_median"],
                window_min=res["window_min"],
                window_max=res["window_max"],
                window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                process_total=res["process_total"],
                seconds=round(time.time() - t0, 2),
                status="ok",
            )
            print(f"  {key:<26} {res['window_median']:>14,.0f} instr  "
                  f"spread={res['window_spread_pct']:.2f}%  "
                  f"({cells[key]['seconds']}s)", flush=True)
        except ProbeError as exc:
            cells[key] = dict(extra, status="failed", error=str(exc))
            print(f"  {key:<26} FAILED: {exc}", flush=True)
            out = outdir / "f5_step_slope.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": key,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"\nG1 TRIGGERED -- abort, diagnostic at {out}", flush=True)
            return False
        return True

    # --- Series A: the step ladder, operands all in one machine word. ---
    for k in LADDER:
        if not record(f"steps@{k}", probe_source_steps(k, "F5Probe.check"), "F5Probe.check",
                      {"series": "A", "kind": "reduction_steps", "k": k}):
            return 1

    # --- Series B: H5.3 control. Same single operation, three operand widths. ---
    widths = {
        "B-tiny": (4, 3, 7),
        "B-w64": (2 ** 64 - 1, 2 ** 64 - 1, 2 * (2 ** 64 - 1)),
        "B-w65": (2 ** 65 - 1, 2 ** 65 - 1, 2 * (2 ** 65 - 1)),
    }
    for key, (a, b, v) in widths.items():
        app = (f"Lean.mkApp2 (Lean.mkConst ``Nat.add) "
               f"(Lean.mkNatLit {a}) (Lean.mkNatLit {b})")
        if not record(key, probe_source_lhs(app, v, "F5Probe.check"), "F5Probe.check",
                      {"series": "B", "kind": "operand_width", "a": a, "b": b,
                       "expected": v}):
            return 1

    pts = sorted((c["k"], c["window_median"]) for c in cells.values()
                 if c.get("series") == "A" and c.get("status") == "ok")
    alpha, beta, se_beta, worst_resid = fit_lin(pts)
    spreads = [c["window_spread_pct"] for c in cells.values() if c.get("status") == "ok"]
    inst = max(spreads) if spreads else None
    kmax = pts[-1][0]
    cmax = pts[-1][1]

    # --- Verdicts, applying the pre-registered criteria literally. ---
    verdicts = []
    verdicts.append(
        f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
        f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}")
    if worst_resid <= 5:
        verdicts.append(f"G3 H5.1 linearity    : worst residual {worst_resid:.2f}% "
                        f"(threshold 5%) -> H5.1 NOT rejected")
    else:
        verdicts.append(f"G3 H5.1 linearity    : worst residual {worst_resid:.2f}% "
                        f"(threshold 5%) -> H5.1 REJECTED (cost is not linear in k)")
    z = beta / se_beta if se_beta else float("inf")
    if se_beta and se_beta > 0 and beta > se_beta:
        verdicts.append(f"G4 slope resolves    : beta = {beta:,.0f} +- {se_beta:,.0f} "
                        f"instr/step (z = {z:.1f}) -> slope MEASURED")
    else:
        verdicts.append(f"G4 slope resolves    : beta = {beta:,.0f} +- {se_beta:,.0f} "
                        f"instr/step (z = {z:.1f}) -> H5.1 UNRESOLVED, NOT 'zero': "
                        f"the data cannot distinguish a flat curve from a slope "
                        f"below its own noise. No headroom may be claimed from this.")
    if se_beta and beta * kmax <= alpha:
        verdicts.append(f"G5 H5.2 alpha dominates: beta*kmax = {beta*kmax:,.0f} <= "
                        f"alpha = {alpha:,.0f} -> H5.2 NOT rejected")
    else:
        verdicts.append(f"G5 H5.2 alpha dominates: beta*kmax = {beta*kmax:,.0f} > "
                        f"alpha = {alpha:,.0f} -> H5.2 REJECTED, steps dominate")

    payload = {
        "status": "ok",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "scope": "user-space only (LK_EXCLUDE_KERNEL=1)"},
        "preregistered": {
            "H5.1": "c(k) linear in reduction steps k",
            "H5.2": "alpha dominates: steps are a minority of the cost",
            "H5.3": "F2's 63-bit step belongs to the operand literal, not the op",
            "criteria": {"G1": "abort on failed cell", "G2": "spread > 5%",
                         "G3": "reject H5.1 if residual > 5%",
                         "G4": "unresolved if beta <= its standard error",
                         "G5": "reject H5.2 if beta*kmax > alpha"},
        },
        "fit": {"alpha": alpha, "beta_instr_per_step": beta, "se_beta": se_beta,
                "worst_residual_pct": worst_resid, "z": z},
        "ladder": pts,
        "cells": cells,
    }
    out = outdir / "f5_step_slope.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        "F5 -- marginal cost of a kernel reduction step (2026-10-05)",
        "",
        "metric: instructions inside KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "",
        f"{'k (steps)':>10} {'instructions':>16} {'delta vs k=0':>16} {'implied/step':>14}",
    ]
    base = pts[0][1]
    for k, c in pts:
        d = c - base
        lines.append(f"{k:>10} {c:>16,.0f} {d:>16,.0f} "
                     f"{(d / k if k else 0):>14,.0f}")
    lines += [
        "",
        f"fit: cost = {alpha:,.0f} + ({beta:,.0f} +- {se_beta:,.0f}) * k",
        f"     worst residual {worst_resid:.2f}%   z(beta) = {z:.1f}",
        "",
        "VERDICTS (criteria pre-registered in scripts/f5_step_slope.py)",
    ] + [f"  {v}" for v in verdicts] + [
        "",
        "H5.3 CONTROL (one Nat.add, three operand widths)",
    ]
    for key in widths:
        c = cells.get(key, {})
        lines.append(f"  {key:<10} {c.get('window_median', 0):>14,.0f} instr  "
                     f"(operands {'tiny' if key == 'B-tiny' else key.split('-')[1]} bits)")
    b1 = cells.get("B-tiny", {}).get("window_median")
    b3 = cells.get("B-w65", {}).get("window_median")
    if b1 and b3:
        lines.append(f"  65-bit vs tiny-operand add: {b3/b1:.2f}x")
        lines.append("  => F2's plateau was dominated by literal reduction, not by the"
                     if b3 / b1 > 1.3 else
                     "  => the operand literal does NOT explain the plateau")
    lines += [
        "",
        f"wrote {out}",
    ]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f5_step_slope.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())