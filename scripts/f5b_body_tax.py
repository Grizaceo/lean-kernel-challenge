#!/usr/bin/env python3
"""F5b -- is the per-step tax UNIVERSAL, or a property of iterAdd's body?

F5 measured the marginal cost of a kernel reduction step at
121,247 +- 79 instructions, using a structural recursion whose body is a
single `acc + 1`. Every optimisation conclusion in this repo rests on that
number, so it needs its own control before anyone acts on it.

Two competing readings of F5's slope:

  (A) UNIVERSAL TAX. ~121k is what the kernel charges to unfold one
      structural-recursion step, whatever the body does. Then the rule is
      "minimise the number of kernel reduction steps", full stop, and the
      cost of making each step cheaper is zero.

  (B) BODY-DEPENDENT. ~121k is what THIS body costs. Then a heavier or lighter
      body moves the slope, and the optimisation target is the body, not the
      step count.

These imply opposite engineering advice, so this must be settled by
measurement, not by plausibility. F5's own k-ladder cannot distinguish them:
it varies k and holds the body fixed.

DESIGN. Four bodies, identical step count (k = 100), identical result type,
each recursing structurally on Nat so the *number* of kernel unfoldings is the
same by construction:

  empty    `acc`                    -- returns its argument, does no work
  add1     `acc + 1`                -- F5's original body
  heavy    `acc + 1 + 2 + ... + 16` -- 16 additions per step
  xor1     `acc ^^^ 1`              -- a different op at the same width

If (A) holds all four sit within the instrument's spread. If (B) holds, `empty`
is much cheaper than `heavy` and the slope is a property of the body.

PRE-REGISTERED CRITERIA
-----------------------
G1  A cell that fails to build, export or complete the replay ABORTS the run.
G2  Intra-cell spread > 5% -> re-measure once, then report with its spread.
G3  Reading (A) is ADOPTED only if max/min across the four bodies is within
    5% -- i.e. the body makes no difference beyond the instrument's own noise.
    Reading (B) is adopted if the spread across bodies exceeds 5%.
G4  Either way, `empty` is the control that must come out CHEAPEST-or-equal.
    If `empty` costs more than `heavy`, the instrument is measuring something
    other than the body's work and no reading is adopted.

The empty body is also a positive control for the whole F5 design: it is the
one body whose per-step cost should be as close to pure unfolding as possible.
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

K = 100
REPS = 3

BODIES = {
    "empty": "acc",
    "add1": "acc + 1",
    "heavy": "acc + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16",
    "xor1": "acc ^^^ 1",
}

# Expected values are SIMULATED, never written by hand. The first run of this
# script aborted with a kernel declaration-type mismatch precisely because a
# hand-written literal for `empty` was wrong: the loop threads `acc` through
# unchanged, so `f5b k 0 = 0`, not `k`. That mismatch is the detector doing its
# job -- a wrong expected value fails the Eq.refl build instead of silently
# measuring something else -- but the fix is to not hand-compute at all.
import operator as _op  # noqa: E402

_PY = {
    "empty": lambda acc: acc,
    "add1": lambda acc: acc + 1,
    "heavy": lambda acc: acc + sum(range(1, 17)),
    "xor1": lambda acc: acc ^ 1,
}


def simulate(name: str, k: int) -> int:
    acc = 0
    for _ in range(k):
        acc = _PY[name](acc)
    return acc


EXPECTED = {name: simulate(name, K) for name in BODIES}

LOOP = """
def f5b : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => f5b n ({body})
"""


def probe_source(body: str, value: int, theorem: str) -> str:
    loop = LOOP.format(body=body)
    return f"""import Spec
import Lean
{loop}
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp2 (Lean.mkConst ``f5b) (Lean.mkNatLit {K}) (Lean.mkNatLit 0)
  let rhs := Lean.mkNatLit {value}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def main() -> int:
    pdir = problem_dir("partition")
    outdir = ROOT / "results" / "cost_model"
    outdir.mkdir(parents=True, exist_ok=True)
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f5b-run"
    work.mkdir(parents=True, exist_ok=True)

    print(f"timer: {TIMER_BIN}", flush=True)
    print(f"instructions metric: {COUNT_INSTRUCTIONS}", flush=True)
    print(f"k={K} for every body; reps={REPS}\n", flush=True)

    cells: dict[str, dict] = {}
    for name, body in BODIES.items():
        src = probe_source(body, EXPECTED[name], "F5Probe.check")
        t0 = time.time()
        try:
            export = build_and_export(pdir, src, "F5Probe.check", work, module="F5Probe")
            res = replay(pdir, export, "F5Probe.check", REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:
                res = replay(pdir, export, "F5Probe.check", REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cells[name] = {
                "body": body,
                "expected": EXPECTED[name],
                "k": K,
                "export_bytes": export.stat().st_size,
                "window_instructions": res["window_instructions"],
                "window_median": res["window_median"],
                "window_min": res["window_min"],
                "window_max": res["window_max"],
                "window_spread_pct": round(res["window_spread_pct"] or 0.0, 3),
                "process_total": res["process_total"],
                "seconds": round(time.time() - t0, 2),
                "status": "ok",
            }
            print(f"  {name:<7} {res['window_median']:>14,.0f} instr  "
                  f"spread={res['window_spread_pct']:.2f}%  "
                  f"({cells[name]['seconds']}s)", flush=True)
        except ProbeError as exc:
            cells[name] = {"body": body, "status": "failed", "error": str(exc)}
            print(f"  {name:<7} FAILED: {exc}", flush=True)
            out = outdir / "f5b_body_tax.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": name,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"\nG1 TRIGGERED -- abort, diagnostic at {out}", flush=True)
            return 1

    ok = {n: c for n, c in cells.items() if c.get("status") == "ok"}
    meds = {n: c["window_median"] for n, c in ok.items()}
    spreads = [c["window_spread_pct"] for c in ok.values()]
    inst = max(spreads)
    lo_name = min(meds, key=lambda n: meds[n])
    hi_name = max(meds, key=lambda n: meds[n])
    ratio = meds[hi_name] / meds[lo_name]

    verdicts = [
        f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
        f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}"
    ]
    if "empty" not in meds or "heavy" not in meds:
        verdicts.append("G4 control pair missing -> no reading adopted")
        adopted = "NONE"
    elif meds["empty"] > meds["heavy"]:
        verdicts.append(
            f"G4 control          : empty={meds['empty']:,.0f} > heavy={meds['heavy']:,.0f} "
            f"-> instrument is NOT measuring the body's work; no reading adopted")
        adopted = "NONE"
    else:
        verdicts.append(
            f"G4 control          : empty={meds['empty']:,.0f} <= heavy={meds['heavy']:,.0f} "
            f"-> control behaves as required")
        if ratio <= 1.05:
            adopted = "(A) UNIVERSAL TAX"
            verdicts.append(
                f"G3 body makes no difference: max/min = {hi_name}/{lo_name} = {ratio:.3f}x "
                f"(threshold 1.05) -> reading (A) ADOPTED")
        else:
            adopted = "(B) BODY-DEPENDENT"
            verdicts.append(
                f"G3 body matters: max/min = {hi_name}/{lo_name} = {ratio:.3f}x "
                f"(threshold 1.05) -> reading (B) ADOPTED")

    payload = {
        "status": "ok",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS, "k": K,
                       "scope": "user-space only (LK_EXCLUDE_KERNEL=1)"},
        "preregistered": {
            "question": "is the ~121k/step tax universal or a property of the body?",
            "criteria": {"G1": "abort on failed cell", "G2": "spread > 5%",
                         "G3": "(A) if body spread <= 5%, (B) if > 5%",
                         "G4": "empty must be <= heavy or nothing is adopted"},
        },
        "adopted": adopted,
        "body_ratio_max_over_min": ratio,
        "instrument_worst_spread_pct": inst,
        "cells": cells,
    }
    out = outdir / "f5b_body_tax.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        f"F5b -- is the per-step tax universal? (2026-10-05, k={K} for every body)",
        "",
        "metric: instructions inside KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "",
        f"{'body':<7} {'work per step':<18} {'instructions':>14} {'spread':>8}  per-step",
    ]
    work_desc = {"empty": "(none)", "add1": "1 addition", "heavy": "16 additions",
                 "xor1": "1 xor"}
    for name in ["empty", "add1", "xor1", "heavy"]:
        if name not in meds:
            continue
        lines.append(f"{name:<7} {work_desc[name]:<18} {meds[name]:>14,.0f} "
                     f"{ok[name]['window_spread_pct']:>7.2f}%  "
                     f"{(meds[name] - 459595) / K:>9,.0f}")
    lines += ["", "VERDICTS (criteria pre-registered in scripts/f5b_body_tax.py)"] \
        + [f"  {v}" for v in verdicts] + [
        "",
        f"ADOPTED: {adopted}",
        f"wrote {out}",
    ]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f5b_body_tax.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())