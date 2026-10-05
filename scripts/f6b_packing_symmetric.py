#!/usr/bin/env python3
"""F6b -- the packing margin WITHOUT the 4-argument helper confound.

WHY THIS CONTROL IS NECESSARY
------------------------------
F6 measured packed-vs-narrow and found a 22.4x margin at 64 lanes. But F6's
packed probe went through a 4-argument helper (`lanewise`), which cost a fixed
~113,566 instructions over a bare 2-argument `Nat.add` at the same operand
width -- a 39% overhead. A constant additive overhead cannot manufacture a
ratio (the narrow side grows linearly, the packed side ~not at all), so the
mechanism survived the check. But a 39% handicap on the treatment arm is still
bad experimental design: it understates the effect and it makes the absolute
numbers uninterpretable.

This re-runs the comparison with the SAME shape on both arms -- both are a
single call to a one-argument function -- so the only difference between them is
HOW MUCH WORK each call does.

  packed : one `Nat.add` over a (lanes x 65)-bit operand  -> work: 1 wide add
  narrow : one `Nat.add` per lane, folded by a recursion  -> work: lanes unfolds

Both cells are built with `mkApp2` on a 2-argument constant, exactly like F6
Series A, so they are directly comparable to each other AND to Series A.

PREREGISTERED
-------------
H6.4  The packing margin measured with a symmetric harness matches F6's
      direction and is not smaller than F6 reported. Supporting: F6's overhead
      was additive and constant; this removes it.

G1  A failed cell ABORTS the run; no failed cell is written as a number.
G2  Intra-cell spread > 5% -> re-measure once, then report with its spread.
G3  H6.4 is REJECTED if the symmetric-harness margin at 64 lanes is SMALLER
      than F6's 22.40x. That would mean F6's margin was an artefact of the
      asymmetric harness in the opposite direction, and the real effect is
      weaker than advertised.
G4  The packed arm must be CHEAPER than the narrow arm at every lane count
      tested. A crossover inside the tested range means packing has a floor
      below which it loses, and that floor must be reported.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.set_int_max_str_digits(200_000)

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from f2_harness import (COUNT_INSTRUCTIONS, TIMER_BIN, ProbeError,  # noqa: E402
                        build_and_export, problem_dir, replay)

REPS = 3
LANE_BITS = 64
LANES = [1, 4, 16, 64]
F6_REPORTED_RATIO_64 = 22.40


def packed_operands(lanes: int, lane_bits: int = LANE_BITS) -> tuple[int, int, int]:
    stride = lane_bits + 1
    mask = (1 << lane_bits) - 1
    x = sum(((i * 7 + 1) & mask) << (i * stride) for i in range(lanes))
    y = sum(((i * 13 + 5) & mask) << (i * stride) for i in range(lanes))
    return x, y, x + y


def narrow_sum(lanes: int) -> int:
    acc = 0
    for _ in range(lanes):
        acc = acc + 1
    return acc


def src_two_arg(a: int, b: int, v: int, theorem: str) -> str:
    """A single `Nat.add`, applied with mkApp2 -- byte-identical in shape to
    F6 Series A's probe, so all three series are mutually comparable."""
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp2 (Lean.mkConst ``Nat.add) (Lean.mkNatLit {a}) (Lean.mkNatLit {b})
  let rhs := Lean.mkNatLit {v}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def src_narrow(lanes: int, theorem: str) -> str:
    """`lanes` unfolds, one +1 each. Same mkApp2 shape as the packed arm."""
    return f"""import Spec
import Lean
def foldUp : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => foldUp n (acc + 1)
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp2 (Lean.mkConst ``foldUp) (Lean.mkNatLit {lanes}) (Lean.mkNatLit 0)
  let rhs := Lean.mkNatLit {narrow_sum(lanes)}
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
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f6b-run"
    work.mkdir(parents=True, exist_ok=True)

    print(f"timer: {TIMER_BIN}  reps={REPS}\n", flush=True)
    cells: dict[str, dict] = {}

    def record(key: str, src: str, extra: dict) -> bool:
        t0 = time.time()
        try:
            export = build_and_export(pdir, src, "F6bProbe.check", work, module="F6bProbe")
            res = replay(pdir, export, "F6bProbe.check", REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:
                res = replay(pdir, export, "F6bProbe.check", REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cells[key] = dict(
                extra, export_bytes=export.stat().st_size,
                window_median=res["window_median"],
                window_min=res["window_min"], window_max=res["window_max"],
                window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                seconds=round(time.time() - t0, 2), status="ok")
            print(f"  {key:<20} {res['window_median']:>14,.0f} instr  "
                  f"spread={res['window_spread_pct']:.2f}%  ({cells[key]['seconds']}s)",
                  flush=True)
        except ProbeError as exc:
            cells[key] = dict(extra, status="failed", error=str(exc))
            print(f"  {key:<20} FAILED: {exc}", flush=True)
            out = outdir / "f6b_packing_symmetric.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": key,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"\nG1 TRIGGERED -- abort at {out}", flush=True)
            return False
        return True

    print("packed arm -- ONE Nat.add over (lanes x 65) bits", flush=True)
    for lanes in LANES:
        x, y, z = packed_operands(lanes)
        if not record(f"packed{lanes}", src_two_arg(x, y, z, "F6bProbe.check"),
                      {"arm": "packed", "lanes": lanes,
                       "total_bits": (LANE_BITS + 1) * lanes}):
            return 1

    print("\nnarrow arm -- `lanes` unfolds, one +1 each", flush=True)
    for lanes in LANES:
        if not record(f"narrow{lanes}", src_narrow(lanes, "F6bProbe.check"),
                      {"arm": "narrow", "lanes": lanes}):
            return 1

    ok = {k: c for k, c in cells.items() if c.get("status") == "ok"}
    inst = max(c["window_spread_pct"] for c in ok.values())
    rows = []
    for lanes in LANES:
        p = ok.get(f"packed{lanes}", {}).get("window_median")
        n = ok.get(f"narrow{lanes}", {}).get("window_median")
        if p and n:
            rows.append((lanes, p, n, n / p))

    verdicts = [
        f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
        f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}",
    ]
    r64 = next((r[3] for r in rows if r[0] == 64), None)
    if r64 is None:
        verdicts.append("G3 H6.4            : no 64-lane cell -> UNRESOLVED")
        h64 = "UNRESOLVED"
    elif r64 < F6_REPORTED_RATIO_64:
        verdicts.append(
            f"G3 H6.4 margin      : symmetric 64-lane margin = {r64:.2f}x < "
            f"F6's {F6_REPORTED_RATIO_64:.2f}x -> H6.4 REJECTED, F6 overstated it")
        h64 = "REJECTED"
    else:
        verdicts.append(
            f"G3 H6.4 margin      : symmetric 64-lane margin = {r64:.2f}x >= "
            f"F6's {F6_REPORTED_RATIO_64:.2f}x -> H6.4 NOT rejected")
        h64 = "NOT rejected"

    losers = [r[0] for r in rows if r[3] < 1]
    if losers:
        verdicts.append(
            f"G4 packing cheaper  : NOT at lanes {losers} -> packing has a floor; "
            f"report it, do not quote the best cell alone")
    else:
        verdicts.append("G4 packing cheaper  : at every lane count tested -> PASS")

    payload = {
        "status": "ok",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "harness": "symmetric: both arms use mkApp2 on a 2-arg call"},
        "preregistered": {
            "H6.4": "symmetric harness reproduces (or beats) F6's margin",
            "criteria": {"G1": "abort on failed cell", "G2": "spread > 5%",
                         "G3": "reject H6.4 if margin < F6's 22.40x",
                         "G4": "report any lane count where packing loses"},
        },
        "verdicts": {"H6.4": h64},
        "rows": [{"lanes": l, "packed": p, "narrow": n, "ratio": r} for l, p, n, r in rows],
        "cells": cells,
    }
    out = outdir / "f6b_packing_symmetric.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        "F6b -- the packing margin, symmetric harness (2026-10-05)",
        "",
        "Both arms are a single mkApp2 call, so the only difference is how much",
        "work each call does. This removes F6's 39% four-argument overhead.",
        "",
        f"{'lanes':>7}{'packed':>14}{'narrow':>14}{'narrow/packed':>16}{'F6 said':>10}",
    ]
    f6 = {1: 1.68, 4: 2.66, 16: 6.67, 64: 22.40}
    for l, p, n, r in rows:
        lines.append(f"{l:>7}{p:>14,.0f}{n:>14,.0f}{r:>15.2f}x{f6[l]:>9.2f}x")
    lines += ["", "VERDICTS (pre-registered in scripts/f6b_packing_symmetric.py)"] \
        + [f"  {v}" for v in verdicts] + ["", f"wrote {out}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f6b_packing_symmetric.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())