#!/usr/bin/env python3
"""F8 -- is the ~234k fixed cost attackable? Pre-registered 2026-10-05.

THE CONTRADICTION THAT FORCES THIS EXPERIMENT
----------------------------------------------
F7 measured a linear fit over packing width: `cost = 244,590 + 37.1 * lanes`.
The INTERCEPT (244,590) already exceeds a champion's whole per-slot budget
(238,082). `floor(238,082 / 234,175) = 1.02` -- a champion's slot buys exactly
ONE arithmetic operation, with 3,907 instructions (1.67%) left over.

That fixed ~234k is the whole ballgame now. It is paid by every single
primitive: `Nat.add` at 4 bits and at 16,384 bits both cost ~234k. F6/F7 showed
the cost is SUBLINEAR in operand width, which means ~234k is NOT the arithmetic
-- if it were, 4,096x the operand would cost proportionally more. It is a fixed
per-operation overhead somewhere in the kernel's call path.

So the only remaining question that matters for ranking is: WHAT IS THAT
OVERHEAD, and is it attackable? F7 answered "how much does one operation cost".
F8 asks "why", because a fixed cost that is an artifact of how the probe is
declared is removable, and one that is inherent to `Nat.add` is not.

FOUR CANDIDATE EXPLANATIONS, EACH WITH A DISTINCT PREDICTION
------------------------------------------------------------
E1  DECLARATION SHAPE. The ~234k is the cost of WHNF-normalising the theorem
    application itself (walking the `Eq`, instantiating the type, elaborating
    `mkEqRefl`), paid once per replayed declaration regardless of the operation.
    Prediction: the cost is ~the same for a trivial `Eq.refl` on ANY constant,
    including constants that do NO arithmetic at all. If so, the overhead is not
    about `Nat.add` and a different declaration shape could pay much less.

E2  GMP ALLOCATION. The ~234k is `Nat.add` constructing and freeing GMP
    integers. Prediction: a constant that does no arithmetic costs much less,
    and among arithmetic ops cost tracks whether a new bignum is allocated.

E3  KERNEL ENTRY. The ~234k is fixed per kernel entry (loading the environment,
    instantiating the well-known constants, the `Nat.add` code path). Prediction:
    cost is roughly flat across operations that all go through the same entry.

E4  INSTRUMENT BOUNDARY. The ~234k is an artifact of the measurement window
    itself -- e.g. the timer counts a fixed preamble before the target
    declaration. Prediction: the measured window for a declaration that should be
    nearly free still reports ~234k, and the floor is independent of content.

E1 and E4 are the important ones for us, because both predict a CHEAPER path
exists. E2 and E3 predict the overhead is intrinsic and the ~1-operation budget
is a hard floor.

PREREGISTERED HYPOTHESES
------------------------
H8.1  There EXISTS a declaration whose scored window is materially CHEAPER than
      234k. This is the actionable hypothesis: if any probe costs <150k, then
      the per-operation floor is avoidable and a candidate can fit more than one
      operation per slot.

H8.2  The fixed cost is NOT specific to `Nat.add`. Prediction: at least one
      no-arithmetic declaration costs <80% of the `Nat.add` cost.

FALSIFICATION CRITERIA (fixed before any number is produced)
----------------------------------------------------------
G1  A cell that fails to build, export or complete the replay ABORTS the run.
G2  Intra-cell spread > 5% -> re-measure once, then report with its spread.
G3  H8.1 is REJECTED if the MINIMUM cost over all cells is >= 90% of the
      `Nat.add` cost. (No cheaper path exists within this probe set.)
G4  H8.2 is REJECTED if every no-arithmetic cell is >= 95% of the `Nat.add`
      cost. (The overhead really is specific to arithmetic.)
G5  Report the CHEAPEST cell even if the result is negative, and report the
      spread. A negative result here is still a hard floor worth knowing.
G6  If some cell fails to compile for a Lean-API reason (not a measurement
      reason), record it as `failed` and CONTINUE with the remaining cells
      rather than aborting -- unlike F5b/F6, here a build failure is
      expected-and-informative, not a guard violation. This is the one
      experiment where G1 is deliberately relaxed, and it is recorded as such.

MEASUREMENT
-----------
`instructions` from the official timer's KERNEL_TIMING record at the
`target-declaration-replay-v1` boundary, identical harness to F7.
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

REPS = 3
# F7's measured 64-lane packed cost, used as the arithmetic reference.
NATADD_REF = 245053


def const_refl(theorem: str) -> str:
    """E1/E4 probe: a reflexive equation between two LITERALS. No arithmetic
    happens. If this costs ~234k, the overhead is about the declaration, not
    about `Nat.add`."""
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let ty ← mkEq (Lean.mkNatLit 7) (Lean.mkNatLit 7)
  let pf ← mkEqRefl (Lean.mkNatLit 7)
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def unit_fun_refl(theorem: str) -> str:
    """E3 probe: a call to a zero-argument constant. Cheapest possible kernel
    entry, no allocation, no arithmetic."""
    return f"""import Spec
import Lean
def zero : Nat := 0
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkConst ``zero
  let rhs := Lean.mkNatLit 0
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def nat_succ_refl(theorem: str) -> str:
    """E2 probe: `Nat.succ` on a literal. An arithmetic op, but a structurally
    recursive one that needs no GMP allocation for small values."""
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp1 (Lean.mkConst ``Nat.succ) (Lean.mkNatLit 6)
  let rhs := Lean.mkNatLit 7
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def nat_sub_refl(theorem: str) -> str:
    """E2/E3 probe: `Nat.sub`, the operation a packed DP would actually need
    for its recurrences. Is it more or less expensive than `Nat.add`?"""
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp2 (Lean.mkConst ``Nat.sub) (Lean.mkNatLit 9) (Lean.mkNatLit 2)
  let rhs := Lean.mkNatLit 7
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def id_refl_via_const(theorem: str) -> str:
    """E1 probe: the SAME total work as `const_refl`, but routed through a
    user-defined constant so the kernel must unfold it. Isolates 'unfolding a
    constant' from 'normalising an equation'."""
    return f"""import Spec
import Lean
def seven : Nat := 7
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkConst ``seven
  let rhs := Lean.mkNatLit 7
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


CELLS = [
    ("A-const-refl", const_refl, "E1/E4: reflexive eq between two literals, no arithmetic"),
    ("B-zero-const", unit_fun_refl, "E3: call a zero-argument constant"),
    ("C-nat-succ", nat_succ_refl, "E2: Nat.succ on a literal"),
    ("D-nat-sub", nat_sub_refl, "E2/E3: Nat.sub, what a packed DP needs"),
    ("E-const-unfold", id_refl_via_const, "E1: same total work, via a user constant"),
    ("F-nat-add-ref", lambda t: f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp2 (Lean.mkConst ``Nat.add) (Lean.mkNatLit 1) (Lean.mkNatLit 1)
  let rhs := Lean.mkNatLit 2
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{t},
    levelParams := [],
    type := ty,
    value := pf }})
""", "reference: Nat.add on 4-bit literals (F7's cheapest arithmetic)"),
]


def main() -> int:
    pdir = problem_dir("partition")
    outdir = ROOT / "results" / "cost_model"
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f8-run"
    work.mkdir(parents=True, exist_ok=True)

    print(f"timer: {TIMER_BIN}  reps={REPS}", flush=True)
    print(f"arithmetic reference (F7, 64 lanes): {NATADD_REF:,} instr\n", flush=True)
    print("G6 is RELAXED here: a build failure is informative, so the run\n"
          "continues instead of aborting. This is deliberate and recorded.\n", flush=True)

    cells: dict[str, dict] = {}

    for key, builder, note in CELLS:
        t0 = time.time()
        try:
            src = builder("F8Probe.check")
            export = build_and_export(pdir, src, "F8Probe.check", work, module="F8Probe")
            res = replay(pdir, export, "F8Probe.check", REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:
                res = replay(pdir, export, "F8Probe.check", REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cost = res["window_median"]
            cells[key] = dict(note=note, status="ok", window_median=cost,
                              window_min=res["window_min"],
                              window_max=res["window_max"],
                              window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                              vs_ref=round(cost / NATADD_REF, 4),
                              seconds=round(time.time() - t0, 2))
            print(f"  {key:<16} {cost:>10,.0f} instr  = {cost / NATADD_REF:.3f}x ref  "
                  f"spread={res['window_spread_pct']:.2f}%  ({cells[key]['seconds']}s)",
                  flush=True)
        except ProbeError as exc:
            cells[key] = dict(note=note, status="failed", error=str(exc))
            print(f"  {key:<16} FAILED: {str(exc)[:200]}", flush=True)

    ok = {k: c for k, c in cells.items() if c.get("status") == "ok"}
    verdicts: list[str] = []

    if ok:
        inst = max(c["window_spread_pct"] for c in ok.values())
        verdicts.append(
            f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
            f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}")

        # `min` over .items() yields (key, cell); take the key from the tuple and
        # the cost from the cell. Swapping these makes Pyright's `str < float`
        # complaint the only warning -- which is exactly what it flagged.
        ckey, ccell = min(ok.items(), key=lambda kv: kv[1]["window_median"])
        cval = ccell["window_median"]
        noarith = {k: v for k, v in ok.items()
                   if k in ("A-const-refl", "B-zero-const", "E-const-unfold")}

        # G3 -- is there any cheaper path at all?
        if cval < 0.90 * NATADD_REF:
            verdicts.append(
                f"G3 H8.1 cheaper path: cheapest = {ckey} at {cval:,.0f} instr = "
                f"{cval / NATADD_REF:.3f}x ref (< 0.90) -> H8.1 NOT rejected")
            h81 = "NOT rejected"
        else:
            verdicts.append(
                f"G3 H8.1 cheaper path: cheapest = {ckey} at {cval:,.0f} instr = "
                f"{cval / NATADD_REF:.3f}x ref (>= 0.90) -> H8.1 REJECTED, no cheaper "
                f"path in this probe set")
            h81 = "REJECTED"

        # G4 -- is the overhead arithmetic-specific?
        if noarith:
            wk, wv = max(((k, v["window_median"]) for k, v in noarith.items()),
                       key=lambda t: t[1])
            if wv < 0.95 * NATADD_REF:
                verdicts.append(
                    f"G4 H8.2 not arith   : most expensive no-arith cell {wk} = {wv:,.0f} = "
                    f"{wv / NATADD_REF:.3f}x ref (< 0.95) -> H8.2 NOT rejected, the "
                    f"overhead is not specific to arithmetic")
                h82 = "NOT rejected"
            else:
                verdicts.append(
                    f"G4 H8.2 not arith   : most expensive no-arith cell {wk} = {wv:,.0f} = "
                    f"{wv / NATADD_REF:.3f}x ref (>= 0.95) -> H8.2 REJECTED, the "
                    f"overhead really is arithmetic-specific")
                h82 = "REJECTED"
        else:
            verdicts.append("G4 H8.2 not arith   : no no-arithmetic cell compiled "
                            "-> UNRESOLVED")
            h82 = "UNRESOLVED"
    else:
        h81 = h82 = "UNRESOLVED"
        verdicts.append("G2/G3/G4          : no cell compiled -> UNRESOLVED")

    verdicts.append(
        "G5 report cheapest : "
        + (f"{min(ok.items(), key=lambda kv: kv[1]['window_median'])[0]} is the "
           "floor within this probe set" if ok else "no cell compiled"))

    payload = {
        "status": "ok",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "harness": "identical to F7: single mkAppN/mkApp2 mkEqRefl",
                       "G1_relaxed": "build failures recorded and the run CONTINUES; "
                                     "deliberate for this experiment only"},
        "arithmetic_reference": NATADD_REF,
        "preregistered": {
            "H8.1": "some declaration costs materially less than the Nat.add floor",
            "H8.2": "the fixed cost is not specific to Nat.add",
            "criteria": {"G1": "RELAXED here (deliberate)",
                         "G2": "spread > 5%",
                         "G3": "reject H8.1 if min >= 0.90x ref",
                         "G4": "reject H8.2 if every no-arith cell >= 0.95x ref",
                         "G5": "always report the cheapest cell",
                         "G6": "record build failures, continue"},
            "explanations": {
                "E1": "declaration shape / Eq normalisation -- overhead removable",
                "E2": "GMP allocation -- intrinsic to Nat.add",
                "E3": "kernel entry cost -- mostly intrinsic",
                "E4": "instrument boundary artifact -- removable, and a trap",
            },
        },
        "verdicts": {"H8.1": h81, "H8.2": h82},
        "cells": cells,
    }
    out = outdir / "f8_fixed_floor.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        "F8 -- is the ~234k fixed per-operation cost attackable? (2026-10-05)",
        "",
        "F7 found cost = 244,590 + 37.1*lanes, and the intercept EXCEEDS a",
        "champion's whole slot (238,082). So this asks WHY the fixed cost exists,",
        "not how big it is: a removable overhead means more than one op per slot.",
        "",
        f"{'cell':<18}{'instructions':>13}{'vs Nat.add ref':>17}  what it isolates",
    ]
    for key, _, note in CELLS:
        c = cells.get(key, {})
        if c.get("status") == "ok":
            lines.append(f"{key:<18}{c['window_median']:>13,.0f}"
                         f"{c['window_median'] / NATADD_REF:>16.3f}x  {note}")
        else:
            lines.append(f"{key:<18}{'FAILED':>13}{'':>17}  {note}")

    lines += ["", "VERDICTS (pre-registered in scripts/f8_fixed_floor.py)"] \
        + [f"  {v}" for v in verdicts] + ["", f"wrote {out}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f8_fixed_floor.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())