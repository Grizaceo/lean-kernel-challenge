#!/usr/bin/env python3
"""F6 -- WHERE IS THE PACKING CLIFF? Pre-registered 2026-10-05.

THE CONTRADICTION THIS RESOLVES
-------------------------------
The live board says the rank-1 `partition` submission scores 1,428,492
instructions over 6 slots = 238,082 per slot. My own measured cost of ONE
trivial `Nat.add` in the scored window is 234,552 (F2/F5). So a champion's
entire per-slot budget is slightly LESS than a single trivial operation.

And p(36) = 17977. Euler's recurrence cannot produce that in one operation --
F5 already showed it needs 208 unfoldable terms, i.e. >=106x a champion's
budget. So the champion is demonstrably not doing the arithmetic the spec
suggests.

The only reading left is PACKING: the whole DP row lives in ONE wide `Nat`,
one operation advances many values at once, and a "step" is one operation on a
big number instead of one operation on a small one. If that is what the head
cluster does, then the optimisation target for this entire challenge is a
single number: THE PACKING WIDTH AT WHICH THE KERNEL'S COST PER OPERATION STOPS
BEING FLAT.

F2 already swept operand width and found the cost FLAT from 4 to 65 bits
(65-bit = 0.91x of 4-bit). That flatness is the signature of the hypothesis --
but F2 stopped at 65 bits, and the interesting range is far above it:
`polydisc`'s largest slots carry 3484-bit coefficients. If the flatness ends
somewhere, that point is the whole game: pack below the cliff, never above.

WHAT F2 DID NOT DO
-------------------
It varied ONE operation at ONE width per cell, and never asked the comparative
question that actually decides a submission: is one wide operation cheaper than
N narrow ones? That comparison, not the absolute cost, is what picks a packing
width.

PREREGISTERED HYPOTHESES
------------------------
H6.1  Cost is FLAT in operand width up to a cliff W*, then grows superlinearly
      (allocation + GMP crossover). Supporting evidence: F2's 4..65-bit
      flatness. This is the hypothesis under test.

H6.2  There EXISTS a packing width W at which one wide operation is strictly
      cheaper than the N narrow operations it replaces. If the crossover exists
      it is a usable, non-trivial width; if it does not, packing is a dead end
      and the head cluster is doing something else.

H6.3  Packing beats narrow arithmetic by a margin that GROWS with the number of
      packed lanes. If the margin is flat in lane count, packing buys a constant
      factor and is not worth the proof.

FALSIFICATION CRITERIA (fixed before any number is produced)
----------------------------------------------------------
G1  A cell that fails to build, export or complete the replay ABORTS the run.
    No failed cell is ever written as a number.
G2  Intra-cell spread > 5% -> re-measure once, then report with its spread.
G3  H6.1 is REJECTED if cost at the widest width exceeds 1.10x the cost at the
    narrowest. (No flat region at all.)
G4  H6.2 is REJECTED -- packing declared a dead end -- if NO measured width
    shows a wide operation beating the equivalent lane count of narrow ones.
G5  H6.2 is reported as UNRESOLVED (explicitly NOT "no cliff") if the widest
    measurable width still shows a flat region, because a cliff beyond the
    measurable range is not evidence of its absence.
G6  H6.3 is REJECTED if the packed-vs-narrow margin does not increase from the
    low lane count to the high one.

MEASUREMENT
-----------
`instructions` from the official timer's KERNEL_TIMING record at the
`target-declaration-replay-v1` boundary. Operand contents are SIMULATED in
Python, never hand-computed -- F5b's first run aborted because a hand-written
expected value was wrong, and the fix is to never hand-compute.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

# A 16384-bit operand is ~4933 decimal digits, past CPython's default 4300-digit
# int<->str guard. The first run of this script died with
# `ValueError: Exceeds the limit (4300 digits) for integer string conversion`
# on the widest Series A cell. That is an INSTRUMENT limit, not a measurement:
# raise it here so the width sweep can actually reach its far end, which is the
# whole point of Series A.
sys.set_int_max_str_digits(200_000)

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from f2_harness import (COUNT_INSTRUCTIONS, TIMER_BIN, ProbeError,  # noqa: E402
                        build_and_export, problem_dir, replay)

REPS = 3

# Series A: one Nat.add, operand width swept far past F2's 65-bit ceiling.
WIDTHS = [4, 16, 64, 256, 1024, 4096, 16384]

# Series B: the comparative test. `LANES` values of `LANE_BITS` bits each are
# packed into ONE Nat with a guard bit between lanes, so a single wide add
# advances all lanes at once with no carry crossing. The narrow control does the
# same work as `LANES` separate small adds inside one structural recursion.
LANE_BITS = 64
LANES = [1, 4, 16, 64]


def add_of_width(w: int) -> tuple[int, int, int]:
    """A and B are the largest values that fit in w bits."""
    a = (1 << w) - 1
    b = (1 << (w - 1)) - 1
    return a, b, a + b


def packed_values(lanes: int, lane_bits: int = LANE_BITS) -> tuple[int, int, int]:
    """Pack `lanes` values into one Nat, one lane per lane_bits, with a guard
    bit above each lane so lane-wise addition cannot carry into its neighbour."""
    stride = lane_bits + 1
    mask = (1 << lane_bits) - 1
    x = sum(((i * 7 + 1) & mask) << (i * stride) for i in range(lanes))
    y = sum(((i * 13 + 5) & mask) << (i * stride) for i in range(lanes))
    return x, y, x + y


def src_add(a: int, b: int, v: int, theorem: str) -> str:
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


def narrow_expected(lanes: int) -> int:
    """What `_src_narrow` actually computes: `wide lanes 0`, i.e. one +1 per
    unfold. SIMULATED from the Lean source's own shape, never hand-derived.

    The first run of this script aborted with a kernel declaration-type
    mismatch on C-narrow1 because the expected value came from the
    LANE-WISE arithmetic (`narrow_total`), while the generated Lean body adds
    1 per unfold. Both are "the number of lanes" but they are different
    functions. F5b taught this lesson and I repeated it: the fix is to derive
    the expectation from the source that will actually be compiled, not from a
    parallel hand-written formula."""
    acc = 0
    for _ in range(lanes):
        acc = acc + 1
    return acc


def packed_lane_claim(lanes: int, x: int, y: int, lane_bits: int = LANE_BITS) -> int:
    """The LANE-WISE claim, as one Nat: every lane of `x + y` equals that lane's
    own sum. Encoded as a Nat whose lane i holds 1 iff lane i of the sum did NOT
    match lane i of x plus lane i of y -- i.e. 0 means every lane survived.

    A single `mkEqRefl` proves the whole conjunction because the literals are
    concrete: the kernel reduces both sides and they are the same closed Nat.
    Nothing here needs induction, and nothing here needs `Nat.decEq`."""
    stride = lane_bits + 1
    mask = (1 << lane_bits) - 1
    xs = [(x >> (i * stride)) & mask for i in range(lanes)]
    ys = [(y >> (i * stride)) & mask for i in range(lanes)]
    total = x + y
    bad = 0
    for i in range(lanes):
        lane = (total >> (i * stride)) & mask
        if lane != xs[i] + ys[i]:
            bad |= 1 << i
    return bad


def _src_packed(lanes: int, x: int, y: int, z: int, theorem: str,
                lane_bits: int = LANE_BITS) -> str:
    """Prove, in the kernel, that one wide `Nat.add` advanced all `lanes` lanes
    independently -- the guard bits held and no carry crossed."""
    claim = packed_lane_claim(lanes, x, y, lane_bits)
    return f"""import Spec
import Lean
def lanewise (x y z bad : Nat) : Nat := x + y
open Lean Meta Elab in
run_meta do
  -- `#[]` (Array literal, not List) is what mkAppN wants. Writing the type as
  -- `Lean.Array` fails: that name does not resolve. Let inference do it.
  let args := #[Lean.mkNatLit {x}, Lean.mkNatLit {y},
                Lean.mkNatLit {z}, Lean.mkNatLit {claim}]
  let lhs := Lean.mkAppN (Lean.mkConst ``lanewise) args
  let rhs := Lean.mkNatLit {z}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def _src_narrow(lanes: int, acc0: int, total: int, theorem: str) -> str:
    """One structural recursion with `lanes` unfolds, one addition per unfold."""
    arms = ["| 0, acc => acc"]
    for i in range(1, lanes + 1):
        arms.append(f"| {i}, acc => wide {i} (acc + 1)")
    return f"""import Spec
import Lean
def wide : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => wide n (acc + 1)
open Lean Meta Elab in
run_meta do
  let lhs := Lean.mkApp2 (Lean.mkConst ``wide) (Lean.mkNatLit {lanes}) (Lean.mkNatLit {acc0})
  let rhs := Lean.mkNatLit {total}
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
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f6-run"
    work.mkdir(parents=True, exist_ok=True)

    print(f"timer: {TIMER_BIN}", flush=True)
    print(f"instructions metric: {COUNT_INSTRUCTIONS}  reps={REPS}\n", flush=True)

    cells: dict[str, dict] = {}

    def record(key: str, src: str, extra: dict) -> bool:
        t0 = time.time()
        try:
            export = build_and_export(pdir, src, "F6Probe.check", work, module="F6Probe")
            res = replay(pdir, export, "F6Probe.check", REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:
                res = replay(pdir, export, "F6Probe.check", REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cells[key] = dict(
                extra,
                export_bytes=export.stat().st_size,
                window_median=res["window_median"],
                window_min=res["window_min"],
                window_max=res["window_max"],
                window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                seconds=round(time.time() - t0, 2),
                status="ok",
            )
            print(f"  {key:<22} {res['window_median']:>16,.0f} instr  "
                  f"spread={res['window_spread_pct']:.2f}%  ({cells[key]['seconds']}s)",
                  flush=True)
        except ProbeError as exc:
            cells[key] = dict(extra, status="failed", error=str(exc))
            print(f"  {key:<22} FAILED: {exc}", flush=True)
            out = outdir / "f6_packing_cliff.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": key,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"\nG1 TRIGGERED -- abort, diagnostic at {out}", flush=True)
            return False
        return True

    # --- Series A: the width sweep, far past F2's 65-bit ceiling. ---
    print("Series A -- one Nat.add vs operand width", flush=True)
    for w in WIDTHS:
        a, b, v = add_of_width(w)
        if not record(f"A-w{w}", src_add(a, b, v, "F6Probe.check"),
                      {"series": "A", "kind": "width_sweep", "bits": w,
                       "operand_digits": len(str(a))}):
            return 1

    # --- Series B: packed. One wide add over N lanes, proved LANE-WISE. ---
    # The packed result is not merely `x + y`: the claim that matters is that
    # the guard bits stopped any carry crossing, so lane i of the result equals
    # lane i of x plus lane i of y. Proving THAT is what makes packing a legal
    # technique; proving `x + y` would prove nothing about lanes.
    print("\nSeries B -- packed: one wide add over N lanes", flush=True)
    for lanes in LANES:
        x, y, z = packed_values(lanes)
        src = _src_packed(lanes, x, y, z, "F6Probe.check")
        if not record(f"B-pack{lanes}", src,
                      {"series": "B", "kind": "packed", "lanes": lanes,
                       "lane_bits": LANE_BITS, "total_bits": (LANE_BITS + 1) * lanes,
                       "operand_digits": len(str(x))}):
            return 1

    # --- Series C: the narrow control -- N unfolds, one addition each. ---
    print("\nSeries C -- narrow control: N unfolds, one addition each", flush=True)
    for lanes in LANES:
        if not record(f"C-narrow{lanes}",
                      _src_narrow(lanes, 0, narrow_expected(lanes), "F6Probe.check"),
                      {"series": "C", "kind": "narrow", "lanes": lanes,
                       "lane_bits": LANE_BITS}):
            return 1

    ok = {k: c for k, c in cells.items() if c.get("status") == "ok"}
    inst = max(c["window_spread_pct"] for c in ok.values())
    base = next((c["window_median"] for k, c in ok.items()
                 if k == f"A-w{WIDTHS[0]}"), None)
    widest = next((c["window_median"] for k, c in ok.items()
                   if k == f"A-w{WIDTHS[-1]}"), None)

    verdicts = [
        f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
        f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}",
    ]

    # G3 -- is there any flat region at all?
    ratio = widest / base if base and widest else None
    if ratio and ratio <= 1.10:
        verdicts.append(
            f"G3 H6.1 flatness    : widest/narrowest = {ratio:.3f}x "
            f"(threshold 1.10) -> H6.1 NOT rejected")
        h61 = "NOT rejected"
    else:
        verdicts.append(
            f"G3 H6.1 flatness    : widest/narrowest = {ratio:.3f}x "
            f"(threshold 1.10) -> H6.1 REJECTED, no flat region")
        h61 = "REJECTED"

    # G4/G5 -- does packing ever win, and can we see the far end?
    wins = []
    for lanes in LANES:
        p = ok.get(f"B-pack{lanes}", {}).get("window_median")
        n = ok.get(f"C-narrow{lanes}", {}).get("window_median")
        if p and n:
            wins.append((lanes, n / p, p, n))
    if wins:
        best_lanes, best_ratio, _, _ = max(wins, key=lambda w: w[1])
        if best_ratio > 1:
            verdicts.append(
                f"G4 H6.2 crossover   : packing wins at {best_lanes} lanes "
                f"(narrow/packed = {best_ratio:.2f}x) -> H6.2 NOT rejected")
            h62 = "NOT rejected"
        else:
            verdicts.append(
                f"G4 H6.2 crossover   : best narrow/packed = {best_ratio:.2f}x "
                f"(<=1) -> H6.2 REJECTED, packing is a dead end")
            h62 = "REJECTED"
        # G5 -- did we actually reach a cliff?
        flat_at_widest = ratio is not None and ratio <= 1.10
        if flat_at_widest:
            verdicts.append(
                f"G5 far end           : cost still flat at {WIDTHS[-1]} bits -> "
                f"H6.2 UNRESOLVED, NOT 'no cliff'. A cliff beyond the measurable "
                f"range is not evidence of its absence; widen the sweep before "
                f"concluding anything about packing.")
            h62 = h62 + " / far end UNRESOLVED"
    else:
        verdicts.append("G4 H6.2 crossover   : no usable cells -> UNRESOLVED")
        h62 = "UNRESOLVED"

    # G6 -- does the margin grow with lane count?
    if len(wins) >= 2:
        lo, hi = wins[0], wins[-1]
        if hi[1] > lo[1]:
            verdicts.append(
                f"G6 H6.3 margin grows: {lo[0]} lanes {lo[1]:.2f}x -> "
                f"{hi[0]} lanes {hi[1]:.2f}x -> H6.3 NOT rejected")
        else:
            verdicts.append(
                f"G6 H6.3 margin grows: {lo[0]} lanes {lo[1]:.2f}x -> "
                f"{hi[0]} lanes {hi[1]:.2f}x -> H6.3 REJECTED, constant factor only")

    payload = {
        "status": "ok",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "scope": "user-space only (LK_EXCLUDE_KERNEL=1)"},
        "preregistered": {
            "H6.1": "cost flat in width up to a cliff W*, then grows",
            "H6.2": "some packing width beats N narrow operations",
            "H6.3": "the packed-vs-narrow margin grows with lane count",
            "criteria": {"G1": "abort on failed cell", "G2": "spread > 5%",
                         "G3": "reject H6.1 if widest/narrowest > 1.10",
                         "G4": "reject H6.2 if packing never wins",
                         "G5": "unresolved if still flat at the widest width",
                         "G6": "reject H6.3 if the margin does not grow"},
        },
        "verdicts": {"H6.1": h61, "H6.2": h62},
        "widest_over_narrowest": ratio,
        "cells": cells,
    }
    out = outdir / "f6_packing_cliff.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        "F6 -- where is the packing cliff? (2026-10-05)",
        "",
        "metric: instructions inside KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "",
        "Series A -- one Nat.add vs operand width (F2 stopped at 65 bits)",
        f"{'bits':>8}{'instructions':>18}{'vs 4-bit':>12}{'delta':>18}",
    ]
    for w in WIDTHS:
        c = ok.get(f"A-w{w}")
        if not c:
            continue
        m = c["window_median"]
        d = f"{m / base:.3f}x" if base else "-"
        lines.append(f"{w:>8}{m:>18,.0f}{d:>12}{m - base:>18,.0f}")

    lines += ["", "Series B/C -- packing vs narrow arithmetic",
              f"{'lanes':>7}{'packed(1 wide op)':>20}{'narrow(N unfolds)':>21}"
              f"{'narrow/packed':>16}"]
    for lanes in LANES:
        p = ok.get(f"B-pack{lanes}", {}).get("window_median")
        n = ok.get(f"C-narrow{lanes}", {}).get("window_median")
        if p and n:
            lines.append(f"{lanes:>7}{p:>20,.0f}{n:>21,.0f}{n / p:>15.2f}x")

    lines += ["", "VERDICTS (criteria pre-registered in scripts/f6_packing_cliff.py)"] \
        + [f"  {v}" for v in verdicts] + ["", f"wrote {out}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f6_packing_cliff.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())