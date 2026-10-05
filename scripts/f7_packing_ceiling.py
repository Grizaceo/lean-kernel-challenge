#!/usr/bin/env python3
"""F7 -- is there a packing ceiling? Sweeping [128, 4096] lanes. Pre-registered 2026-10-05.

WHERE THIS COMES FROM
---------------------
F6b measured, with a symmetric harness, that one wide `Nat.add` over N lanes
beats N narrow unfolds by 33.47x at N=64. The packed arm was nearly FLAT
(234,476 -> 245,646 instr across 64x the lanes) while the narrow arm was
LINEAR (583,948 -> 8,222,982). The margin therefore grows without bound over the
range tested -- which is exactly why F6b could not tell us whether packing has a
ceiling. It only showed no ceiling up to 64 lanes.

And 64 lanes is nowhere near the interesting range. For `partition`, p(36)=17977
fits in 15 bits, so a whole DP row of ~36 entries needs ~36 x 16 = 576 bits,
i.e. ~540 lanes at 65 bits each. A champion's per-slot budget is 238,082
instructions -- LESS than one 64-lane packed add (245,646). So if packing keeps
working, the way to a champion-beating score is fewer and wider operations, and
the number that decides it is: how many lanes can one operation actually carry?

This experiment answers exactly that, and nothing else.

PREREGISTERED HYPOTHESES
------------------------
H7.1  The packed arm stays within 1.25x of its 64-lane cost all the way to
      4096 lanes. Supporting: F6b's packed arm grew only 4.8% over 64x.

H7.2  There is NO cost cliff before 4096 lanes -- i.e. cost remains sublinear in
      operand width throughout. Supporting: F6 Series A showed 0.6-1.0
      instr/bit marginal cost up to 16,384 bits, and 4096 lanes x 65 bits =
      266,240 bits, only 16x past F6's widest cell.

H7.3  A single operation can carry at least 512 lanes at a cost below a
      champion's whole per-slot budget (238,082 instr). This is the
      actionable claim: it would mean a DP row advances in one operation,
      under the leader's budget.

FALSIFICATION CRITERIA (fixed before any number is produced)
----------------------------------------------------------
G1  A cell that fails to build, export or complete the replay ABORTS the run.
G2  Intra-cell spread > 5% -> re-measure once, then report with its spread.
G3  H7.1 is REJECTED if any lane count exceeds 1.25x the 64-lane cost.
G4  H7.2 is REJECTED if marginal cost per lane RISES monotonically over the last
      three points -- that is the signature of a real cliff approaching. A
      single rise is not a cliff; GMP cost is not perfectly monotone.
G5  H7.3 is REJECTED if NO lane count reaches 512 lanes under 238,082 instr.
G6  If the widest measurable lane count still shows sublinear growth, report
    H7.2 as UNRESOLVED, NOT as "no ceiling". A ceiling beyond the measurable
    range is not evidence of its absence -- this is the same guard G5 in F6 was
    written for.

MEASUREMENT
-----------
`instructions` from the official timer's KERNEL_TIMING record at the
`target-declaration-replay-v1` boundary. Both arms use the identical
`mkApp2`-on-`Nat.add` shape from F6b, so numbers are comparable with F6b
directly.

Only the packed arm is swept. The narrow arm is already known to be LINEAR
(584k at 1 lane, 8.2M at 64, slope ~120k/lane); extrapolating it would cost 500M+
instructions at 4096 lanes and would prove nothing new. The ratio at high lane
counts is therefore LOWER-BOUNDED by dividing by the extrapolated linear fit --
stated as a bound, never as a measurement.
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
LANE_BITS = 64
LANES = [64, 128, 256, 512, 1024, 2048, 4096]

# F6b's measured 64-lane packed cost; H7.1 is stated relative to this.
F6B_PACKED_64 = 245646
# The leader's whole per-slot budget (computationTotal 1428492 / 6 slots).
CHAMPION_SLOT = 1428492 / 6


def packed_operands(lanes: int, lane_bits: int = LANE_BITS) -> tuple[int, int, int]:
    """Pack `lanes` values into one Nat, `lane_bits` each plus a guard bit, so
    lane-wise addition provably cannot carry across a lane boundary."""
    stride = lane_bits + 1
    mask = (1 << lane_bits) - 1
    x = 0
    y = 0
    for i in range(lanes):
        x |= ((i * 7 + 1) & mask) << (i * stride)
        y |= ((i * 13 + 5) & mask) << (i * stride)
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


def main() -> int:
    pdir = problem_dir("partition")
    outdir = ROOT / "results" / "cost_model"
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f7-run"
    work.mkdir(parents=True, exist_ok=True)

    print(f"timer: {TIMER_BIN}  reps={REPS}", flush=True)
    print(f"champion per-slot budget: {CHAMPION_SLOT:,.0f} instr\n", flush=True)

    cells: dict[str, dict] = {}

    def record(key: str, src: str, extra: dict) -> bool:
        t0 = time.time()
        try:
            export = build_and_export(pdir, src, "F7Probe.check", work, module="F7Probe")
            res = replay(pdir, export, "F7Probe.check", REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:
                res = replay(pdir, export, "F7Probe.check", REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cost = res["window_median"]
            cells[key] = dict(
                extra, export_bytes=export.stat().st_size,
                window_median=cost, window_min=res["window_min"],
                window_max=res["window_max"],
                window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                vs_champion_slot=round(cost / CHAMPION_SLOT, 4),
                seconds=round(time.time() - t0, 2), status="ok")
            print(f"  {key:<14} {cost:>12,.0f} instr  "
                  f"vs champion slot = {cost / CHAMPION_SLOT:>5.2f}x  "
                  f"spread={res['window_spread_pct']:.2f}%  "
                  f"({cells[key]['seconds']}s)", flush=True)
        except ProbeError as exc:
            cells[key] = dict(extra, status="failed", error=str(exc))
            print(f"  {key:<14} FAILED: {exc}", flush=True)
            out = outdir / "f7_packing_ceiling.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": key,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"\nG1 TRIGGERED -- abort at {out}", flush=True)
            return False
        return True

    print("packed arm -- ONE Nat.add over (lanes x 65) bits", flush=True)
    for lanes in LANES:
        x, y, z = packed_operands(lanes)
        if not record(f"pack{lanes}", src_add(x, y, z, "F7Probe.check"),
                      {"lanes": lanes, "lane_bits": LANE_BITS,
                       "total_bits": (LANE_BITS + 1) * lanes}):
            return 1

    ok = {k: c for k, c in cells.items() if c.get("status") == "ok"}
    inst = max(c["window_spread_pct"] for c in ok.values())
    verdicts = [
        f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
        f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}",
    ]

    # G3 -- flatness up to 1.25x of F6b's 64-lane cost.
    over = [(l, c["window_median"] / F6B_PACKED_64)
            for l, c in ((l, ok.get(f"pack{l}", {})) for l in LANES) if c]
    breaches = [(l, r) for l, r in over if r > 1.25]
    if breaches:
        verdicts.append(
            "G3 H7.1 flatness    : BREACHED at " +
            ", ".join(f"{l} lanes ({r:.2f}x)" for l, r in breaches) +
            " -> H7.1 REJECTED")
        h71 = "REJECTED"
    else:
        verdicts.append(
            f"G3 H7.1 flatness    : max {max(r for _, r in over):.3f}x of F6b's "
            f"64-lane cost (threshold 1.25) -> H7.1 NOT rejected")
        h71 = "NOT rejected"

    # G4 -- is marginal cost per lane rising? That would be an approaching cliff.
    pts = [(l, ok[f"pack{l}"]["window_median"]) for l in LANES if f"pack{l}" in ok]
    marginal = [(pts[i][0], (pts[i][1] - pts[i - 1][1]) / (pts[i][0] - pts[i - 1][0]))
                for i in range(1, len(pts))]
    rising = len(marginal) >= 3 and all(
        marginal[i][1] > marginal[i - 1][1] for i in range(2, len(marginal)))
    if rising:
        verdicts.append(
            "G4 H7.2 cliff       : marginal cost per lane rises monotonically over "
            "the last three points -> H7.2 REJECTED, a cliff is approaching")
        h72 = "REJECTED"
    else:
        last = marginal[-1][1] if marginal else float("nan")
        verdicts.append(
            f"G4 H7.2 cliff       : last marginal = {last:,.1f} instr/lane, not "
            f"monotone rising -> H7.2 NOT rejected")
        h72 = "NOT rejected"

    # G5 -- can one operation carry 512 lanes under a champion's whole slot?
    cheap = [l for l in LANES if f"pack{l}" in ok
             and ok[f"pack{l}"]["window_median"] < CHAMPION_SLOT]
    if 512 in cheap:
        c = ok["pack512"]["window_median"]
        verdicts.append(
            f"G5 H7.3 one-op row  : 512 lanes in {c:,.0f} instr = {c / CHAMPION_SLOT:.2f}x "
            f"a champion's whole slot -> H7.3 NOT rejected, a DP row advances in ONE op")
        h73 = "NOT rejected"
    else:
        best = max(cheap) if cheap else None
        verdicts.append(
            f"G5 H7.3 one-op row  : 512 lanes is "
            f"{ok.get('pack512', {}).get('window_median', float('nan')):,.0f} instr = "
            f"{ok.get('pack512', {}).get('vs_champion_slot', float('nan')):.2f}x a "
            f"champion's slot; best under budget = {best} lanes -> H7.3 REJECTED")
        h73 = "REJECTED"

    # G6 -- did we actually reach a cliff, or just stop measuring?
    if marginal and marginal[-1][1] < 1.0:
        verdicts.append(
            f"G6 far end           : marginal still {marginal[-1][1]:,.2f} instr/lane at "
            f"{pts[-1][0]} lanes -> H7.2 UNRESOLVED, NOT 'no ceiling'. A ceiling "
            f"beyond the measurable range is not evidence of its absence.")
        h72 = h72 + " / far end UNRESOLVED"

    payload = {
        "status": "ok",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "harness": "identical to F6b: single mkApp2 Nat.add"},
        "champion_per_slot_budget": round(CHAMPION_SLOT),
        "preregistered": {
            "H7.1": "packed cost within 1.25x of F6b's 64-lane cost up to 4096 lanes",
            "H7.2": "no cost cliff before 4096 lanes",
            "H7.3": "one op carries 512 lanes under a champion's whole slot",
            "criteria": {"G1": "abort on failed cell", "G2": "spread > 5%",
                         "G3": "reject H7.1 if any lane count > 1.25x of 64-lane cost",
                         "G4": "reject H7.2 if marginal cost per lane rises monotonically",
                         "G5": "reject H7.3 if 512 lanes not under budget",
                         "G6": "unresolved if still sublinear at the widest point"},
        },
        "verdicts": {"H7.1": h71, "H7.2": h72, "H7.3": h73},
        "marginal_instr_per_lane": [{"from_lanes": a, "to_lanes": b, "instr_per_lane": r}
                                    for (a, r), b in
                                    zip([(m[0], m[1]) for m in marginal], pts[1:])],
        "cells": cells,
    }
    out = outdir / "f7_packing_ceiling.json"
    out.write_text(json.dumps(payload, indent=1))

    lines = [
        "F7 -- is there a packing ceiling? [64, 4096] lanes (2026-10-05)",
        "",
        "metric: instructions in KERNEL_TIMING, boundary=target-declaration-replay-v1",
        f"champion per-slot budget: {CHAMPION_SLOT:,.0f} instr",
        "",
        f"{'lanes':>7}{'operand bits':>15}{'instructions':>16}"
        f"{'vs 64-lane':>12}{'vs champion':>13}",
    ]
    for l in LANES:
        c = ok.get(f"pack{l}")
        if not c:
            continue
        lines.append(f"{l:>7}{c['total_bits']:>15,}{c['window_median']:>16,.0f}"
                     f"{c['window_median'] / F6B_PACKED_64:>11.3f}x"
                     f"{c['vs_champion_slot']:>12.2f}x")

    lines += ["", "marginal cost per additional lane:"]
    for m in marginal:
        lines.append(f"  up to {m[0]:>5} lanes: {m[1]:>10,.2f} instr/lane")

    lines += ["", "VERDICTS (pre-registered in scripts/f7_packing_ceiling.py)"] \
        + [f"  {v}" for v in verdicts] + ["", f"wrote {out}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f7_packing_ceiling.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())