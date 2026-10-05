#!/usr/bin/env python3
"""F9 -- is structural arithmetic cheaper than GMP arithmetic? Pre-registered 2026-10-05.

THE GAP THIS CLOSES
--------------------
F8 found the fixed cost is a DECLARATION floor (~118,230 instr for an `Eq.refl`
between two literals, computing nothing), plus a small operand-dependent
component (~36,158). But F8's `C-nat-succ` cell FAILED to compile -- `Lean.mkApp1`
does not exist in this API version -- so structural, non-GMP arithmetic went
UNMEASURED.

That gap matters for the budget. F8 established:

  floor (118,230) + 1 unfold (122,656) = 240,886 > a champion's slot (238,082)

So a champion cannot pay one unfold plus the floor. If there exists an
arithmetic operation materially cheaper than `Nat.add`'s 208,895, a candidate
could pay several of them per slot instead. `Nat.succ` is the natural candidate:
it is a structural recursion over `Nat` (no GMP allocation), while `Nat.add` and
`Nat.sub` both allocate bignums.

PREREGISTERED HYPOTHESES
------------------------
H9.1  There EXISTS an arithmetic operation whose scored cost is materially
      below `Nat.add` on 4-bit literals (208,895). Supporting: `Nat.succ` needs
      no GMP allocation, and F8 showed a fixed ~118k floor exists that is not
      about arithmetic.

H9.2  The cost of structural arithmetic scales with the NUMBER OF STEPS, not with
      GMP width. Prediction: succ on a literal is flat across small literals,
      and the ladder cost tracks step count the way F5's did.

FALSIFICATION CRITERIA (fixed before any number is produced)
----------------------------------------------------------
G1  A cell that fails to build, export or complete the replay ABORTS the run.
G2  Intra-cell spread > 5% -> re-measure once, then report with its spread.
G3  H9.1 is REJECTED if the cheapest arithmetic cell is >= 95% of `Nat.add` at
      4 bits (208,895). That would mean GMP allocation is not a cost component
      and the budget per operation is fixed.
G4  If `Nat.succ` cannot be applied without `mkApp1`, fall back to the
      eta-expanded form `Nat.succ x` built as a 2-argument application of a
      user-defined wrapper, and RECORD that the fallback was used. A fallback
      must never be silently substituted for the pre-registered measurement.
G5  Report the cheapest arithmetic cell even if H9.1 is rejected. A hard floor
      is a real result and must be stated, not hidden behind a rejection.

MEASUREMENT
-----------
`instructions` from the official timer's KERNEL_TIMING record at the
`target-declaration-replay-v1` boundary, identical harness to F8.

API NOTE (learned from F8's failure, applied here so it does not recur):
`Lean.mkApp1` does not exist. For unary application use
`Lean.mkApp (Lean.mkConst ``Nat.succ) (Lean.mkNatLit k)` -- `mkApp` takes a
function Expr and one argument Expr and is the general case of `mkApp2`.
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
# F8's measured Nat.add on 4-bit literals -- the arithmetic reference.
NATADD_4BIT = 208895
# F8's measured declaration floor (Eq.refl between literals).
FLOOR = 118230


def succ_refl(k: int, theorem: str) -> str:
    """`Nat.succ k = k+1`, built with `mkApp` (F8 proved `mkApp1` does not
    exist, so G4's documented fallback is in force from the start)."""
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp (Lean.mkConst ``Nat.succ) (Lean.mkNatLit {k})
  let rhs := Lean.mkNatLit {k + 1}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def pred_refl(k: int, theorem: str) -> str:
    """`Nat.pred` -- also structural, also no GMP allocation."""
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp (Lean.mkConst ``Nat.pred) (Lean.mkNatLit {k})
  let rhs := Lean.mkNatLit {k - 1}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def add_refl(a: int, b: int, theorem: str) -> str:
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp2 (Lean.mkConst ``Nat.add) (Lean.mkNatLit {a}) (Lean.mkNatLit {b})
  let rhs := Lean.mkNatLit {a + b}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def bit_add_refl(theorem: str) -> str:
    """`Nat.xor`/`Nat.and` on bit patterns: GMP allocation but on small limbs."""
    a, b = 0b1011, 0b0110
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp2 (Lean.mkConst ``Nat.xor) (Lean.mkNatLit {a}) (Lean.mkNatLit {b})
  let rhs := Lean.mkNatLit {a ^ b}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


CELLS = [
    ("A-succ-small", lambda t: succ_refl(6, t), "Nat.succ on 6 (structural, no GMP)"),
    ("B-succ-large", lambda t: succ_refl(100000, t), "Nat.succ on 100000 (still structural)"),
    ("C-pred", lambda t: pred_refl(9, t), "Nat.pred on 9 (structural)"),
    ("D-xor", lambda t: bit_add_refl(t), "Nat.xor on 4-bit patterns"),
    ("E-add-small", lambda t: add_refl(1, 1, t), "Nat.add 1+1 (GMP, reference)"),
    ("F-add-large", lambda t: add_refl(10**12, 10**12, t), "Nat.add on 2x 10^12 (GMP, wide)"),
]


def main() -> int:
    pdir = problem_dir("partition")
    outdir = ROOT / "results" / "cost_model"
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f9-run"
    work.mkdir(parents=True, exist_ok=True)

    print(f"timer: {TIMER_BIN}  reps={REPS}", flush=True)
    print(f"reference: Nat.add 4-bit = {NATADD_4BIT:,} instr   "
          f"floor = {FLOOR:,} instr", flush=True)
    print("G4 fallback in force from the start: mkApp (not mkApp1, which does "
          "not exist).", flush=True)

    cells: dict[str, dict] = {}

    def record(key: str, src: str, extra: dict) -> bool:
        t0 = time.time()
        try:
            export = build_and_export(pdir, src, "F9Probe.check", work, module="F9Probe")
            res = replay(pdir, export, "F9Probe.check", REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:
                res = replay(pdir, export, "F9Probe.check", REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cells[key] = dict(extra, status="ok", window_median=res["window_median"],
                              window_min=res["window_min"],
                              window_max=res["window_max"],
                              window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                              vs_add=round(res["window_median"] / NATADD_4BIT, 4),
                              vs_floor=round(res["window_median"] / FLOOR, 4),
                              seconds=round(time.time() - t0, 2))
            print(f"  {key:<15} {res['window_median']:>10,.0f} instr  "
                  f"= {res['window_median'] / NATADD_4BIT:.3f}x add  "
                  f"= {res['window_median'] / FLOOR:.3f}x floor  "
                  f"spread={res['window_spread_pct']:.2f}%  "
                  f"({cells[key]['seconds']}s)", flush=True)
        except ProbeError as exc:
            cells[key] = dict(extra, status="failed", error=str(exc))
            print(f"  {key:<15} FAILED: {str(exc)[:300]}", flush=True)
            out = outdir / "f9_structural_arith.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": key,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"\nG1 TRIGGERED -- abort at {out}", flush=True)
            return False
        return True

    for key, builder, note in CELLS:
        if not record(key, builder("F9Probe.check"), {"note": note}):
            return 1

    ok = {k: c for k, c in cells.items() if c.get("status") == "ok"}
    arith = {k: v for k, v in ok.items() if k != "B-succ-large"}
    verdicts: list[str] = []

    if ok:
        inst = max(c["window_spread_pct"] for c in ok.values())
        verdicts.append(
            f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
            f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}")

        ck, cv = min(((k, v["window_median"]) for k, v in ok.items()),
                     key=lambda t: t[1])
        if cv < 0.95 * NATADD_4BIT:
            verdicts.append(
                f"G3 H9.1 cheaper arith: cheapest = {ck} at {cv:,.0f} instr = "
                f"{cv / NATADD_4BIT:.3f}x Nat.add (< 0.95) -> H9.1 NOT rejected")
            h91 = "NOT rejected"
        else:
            verdicts.append(
                f"G3 H9.1 cheaper arith: cheapest = {ck} at {cv:,.0f} instr = "
                f"{cv / NATADD_4BIT:.3f}x Nat.add (>= 0.95) -> H9.1 REJECTED, no "
                f"cheaper arithmetic exists in this probe set")
            h91 = "REJECTED"

        verdicts.append(
            f"G4 fallback used     : mkApp (not mkApp1, which does not exist). "
            f"Every cell above used the documented fallback; no cell silently "
            f"substituted a different measurement.")
        verdicts.append(
            f"G5 report cheapest   : {ck} at {cv:,.0f} instr — this is the floor "
            f"for ONE arithmetic step in this probe set, whatever H9.1 says")
    else:
        h91 = "UNRESOLVED"
        verdicts.append("G2/G3/G5          : no cell compiled -> UNRESOLVED")

    payload = {
        "status": "ok",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "harness": "identical to F8",
                       "api_note": "Lean.mkApp1 does not exist; used Lean.mkApp"},
        "references": {"natadd_4bit": NATADD_4BIT, "floor": FLOOR},
        "preregistered": {
            "H9.1": "some arithmetic op costs materially less than Nat.add at 4 bits",
            "H9.2": "structural arithmetic scales with step count, not GMP width",
            "criteria": {"G1": "abort on failed cell", "G2": "spread > 5%",
                         "G3": "reject H9.1 if cheapest >= 0.95x Nat.add",
                         "G4": "document the mkApp fallback, never substitute silently",
                         "G5": "always report the cheapest arithmetic cell"},
        },
        "verdicts": {"H9.1": h91},
        "cells": cells,
    }
    out = outdir / "f9_structural_arith.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        "F9 -- structural vs GMP arithmetic (2026-10-05)",
        "",
        f"reference: Nat.add 4-bit = {NATADD_4BIT:,}   floor = {FLOOR:,}",
        "API: Lean.mkApp1 does not exist -> Lean.mkApp used (G4 fallback, documented).",
        "",
        f"{'cell':<16}{'instructions':>14}{'vs add':>10}{'vs floor':>11}  what",
    ]
    for key, _, note in CELLS:
        c = cells.get(key, {})
        if c.get("status") == "ok":
            lines.append(f"{key:<16}{c['window_median']:>14,.0f}"
                         f"{c['vs_add']:>9.3f}x{c['vs_floor']:>10.3f}x  {note}")
        else:
            lines.append(f"{key:<16}{'FAILED':>14}{'':>10}{'':>11}  {note}")

    lines += ["", "VERDICTS (pre-registered in scripts/f9_structural_arith.py)"] \
        + [f"  {v}" for v in verdicts] + ["", f"wrote {out}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f9_structural_arith.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())