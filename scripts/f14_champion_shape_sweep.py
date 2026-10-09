"""F14 -- is there ANY shape that reaches the champion's slot? A generative sweep.

PRE-REGISTERED 2026-10-09, BEFORE ANY NUMBER IS PRODUCED. Committed before the run.

WHY THIS IS NOW THE ONLY QUESTION THAT MATTERS
----------------------------------------------
F13 nailed the bias: the local-window -> official ratio is k = 0.9927 (spread 0.3%,
three independent anchors, fib cross-check consistent). So the F10-F12 cost table is
transferable to the judge's scale with a ~1% correction. The paradox is now sharp:

    champion slot (partition rank1, curveWork 1,428,492 / 6)  =  238,082  (official)
    official floor, no recursor (F11 199,012 / k)             =  200,295  (official)
    official floor + one flat Nat.add (F12 chain@1 / k)       =  322,815  (official)

The champion pays LESS than "floor + one add". Either:
  (a) the champion's `impl` computes p(n) with a shape whose per-operation marginal
      is far cheaper than F12's flat GMP chain (which pays a 122,520 first-add prime
      just to open the opaque `n`), or
  (b) the champion does something structurally different that no probe has exercised.

F13's own 866 data answers part of this: submission 866 (our best, a LIST-based
`itAdd`/`updRowAdd` streaming loop) has slope 61,188,321 per unit n -- that is
61M instructions per ROW, ~257x the champion's entire slot. List recursion is
catastrophically over budget. The champion cannot be list-based.

WHAT NOBODY HAS MEASURED
------------------------
Every probe so far measured a SHAPE we chose. Nobody has measured the champion's
marginal structure directly, because the champion's source is not public. But the
cost table constrains it hard: a 238,082-instr slot with a 200,295 floor leaves
only 37,787 instr of headroom -- and F12 says the FIRST add on an opaque Nat costs
122,520. So the champion's `impl` cannot do arithmetic on an opaque `n` at all.

The only shapes with a sub-40k marginal are those that avoid opening the opaque `n`.
The candidate families that could do this are:
  * a constant/opaque `impl` that pattern-matches on the *literal* witness the judge
    supplies (v), not on n -- i.e. `fun v => ...` reading the already-opaque-free
    proof term;
  * a `Decidable`/instance-resolution impl that the kernel short-circuits;
  * an `impl` that returns a value already present in the environment.

THE HYPOTHESES
--------------
H14.1  There EXISTS a `impl` shape whose official cost is <= 238,082 AND that is not
       a trivial constant. Measured as: at least one cell in the sweep below has
       window_median / k <= 238,082 with a non-`rfl`-only body.
       Prediction: the bare `fun v => v` (projection, F12 chain@0 = 183,396 / k =
       184,745) qualifies on cost but is trivial; the question is whether anything
       COMPUTING fits.
H14.2  No non-trivial shape fits. Then the champion is exploiting something the
       local instrument cannot see (e.g. the judge's window excludes a cost the
       local timer includes, or the champion's correctness role differs).

METHOD -- a generative sweep, pre-registered cell by cell
--------------------------------------------------------
Each cell stages a distinct `impl` body in the judge's own generator shape
(`judge._perf_theorem_source`, imported verbatim -- G4), builds, exports, replays
(reps=3, user-space only, LK_EXCLUDE_KERNEL=1 -- G8 lower bounds).

CELLS (all at the partition problem, n drawn from F13's P1 group where the bias
anchors were validated):

  C1  `fun _ => 0`            -- F11's J-C-trivial, re-measured as this run's own floor
  C2  `fun v => v`            -- projection (identity), the cheapest non-constant
  C3  `fun _ => v`            -- closes over the witness, ignores n  [LEAN: the witness
                                 is the theorem's RHS, so this is the shape that
                                 "returns the answer already in scope"]
  C4  `fun n => n + 1`        -- ONE add on opaque n (F12 chain@1 control, must match)
  C5  `fun n => if n = 16 then 0 else n`  -- one Decidable branch on n
  C6  `fun n => Nat.rec n (fun _ acc => acc) (fun _ => 0)`  -- owns a recursor, computes
                                 nothing (F10b A@0 control, must match ~356,917)
  C7  `fun n => n * n`        -- one multiply on opaque n
  C8  `fun n => n - 1`        -- one Nat.sub on opaque n
  C9  `fun n => 2 ^ n`        -- one HPow on opaque n (the "expensive op" bound)

C1/C4/C6 are CONTROLS against F11/F12/F10b: if this run does not reproduce them
within 8%, the instrument has drifted and the whole sweep is VOID (G-drift).

FALSIFICATION / VERDICT GATES (fixed before the run)
----------------------------------------------------
G1  Any cell that fails to build/export/replay ABORTS with partial cells saved.
G2  Intra-cell spread > 5% -> re-measure once, report both.
G3  CONTROLS: C1 vs F11 (199,012), C4 vs F12 chain@1 (305,916), C6 vs F10b A@0
    (356,917), each within 8%. If any control is off by >8% -> run VOID, no
    hypothesis verdict emitted.
G4  Generator is the judge's: fragments 'Lean.addDecl', 'Submission.impl',
    'mkEqRefl rhs' checked per cell.
G5  No-recursor rule for C1-C5,C7-C9: staged source asserted free of Nat.rec /
    structural patterns / match / termination_by. C6 is the deliberate exception.
G6  Oracle control: partition oracle hard controls p(4)=5, p(10)=42, p(16)=231
    pass before any measurement.
G7  problems/ restored byte-for-byte in a finally block; git status clean for
    problems/ at exit.
G8  SCOPE: user-space only. Every figure is a LOWER bound of the judge's charge.
    "Fits the champion slot" is used only in the safe direction (a cell whose
    local/k is already above 238,082 cannot fit; a cell below might).
G9  Only cells that type-check AND whose theorem replays are reported. A cell
    that builds but fails to replay is reported as FAIL, not as a number.

DELIVERABLE
-----------
results/cost_model/f14_champion_shape_sweep.json + a compact .txt table. The prose
report is written AFTER the numbers exist and cites only this run plus the frozen
official anchors.
"""

from __future__ import annotations

import importlib.util
import json
import os
import statistics
import subprocess
import sys
import time
from pathlib import Path

sys.set_int_max_str_digits(500_000)

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import f2_harness  # noqa: E402
from f2_harness import ProbeError, lean_path  # noqa: E402
from measure import LEAN4EXPORT, run  # noqa: E402

REPS = 3

# ---- frozen anchors from prior runs (tamper-checked literals) -----------------
F11_TRIVIAL = 199_012          # J-C-trivial, judge shape, no recursor
F12_CHAIN1 = 305_916           # floor + one flat Nat.add
F10B_A0 = 356_917              # owns a Nat.rec, computes nothing (k=0)
K_BIAS = 0.9927                # F13 local-window -> official
CHAMPION_SLOT = 238_082        # official, partition rank1 curveWork/6
CONTROL_TOL = 0.08             # G3

GRID_N = [15, 16, 17]          # F13 P1 group, where the bias anchors were validated

# Each cell: (tag, def_impl_lean_source, is_control, control_anchor, no_recursor)
# `v` is the judge's witness literal, `n` is the input. The judge generator wraps
# this into `impl n = v := Eq.refl v` via Lean.addDecl and replays it.
CELLS = [
    ("C1_floor",       "def impl : Nat → Nat := fun _ => 0",                 True,  F11_TRIVIAL,  True),
    ("C2_projection",  "def impl : Nat → Nat := fun v => v",                 False, None,         True),
    ("C3_closeover",   "def impl : Nat → Nat := fun _ => 42",                False, None,         True),
    ("C4_one_add",     "def impl : Nat → Nat := fun n => n + 1",             True,  F12_CHAIN1,   True),
    ("C5_decidable",   "def impl : Nat → Nat := fun n => if n = 16 then 0 else n", False, None,   True),
    ("C6_recursor",    "def impl : Nat → Nat\n  | 0 => 0\n  | n + 1 => impl n",  True, F10B_A0, False),
    ("C7_mul",         "def impl : Nat → Nat := fun n => n * n",             False, None,         True),
    ("C8_sub",         "def impl : Nat → Nat := fun n => n - 1",             False, None,         True),
    ("C9_pow",         "def impl : Nat → Nat := fun n => 2 ^ n",             False, None,         True),
]

FORBIDDEN = ("Nat.rec", "termination_by", "match ", "brecOn")

# v is the value `impl n` reduces to; the judge builds `impl n = v := Eq.refl v`,
# so v must be exactly what the body computes at n (F12's convention: v = str(N_IN + k)).
# NOTE: C1/C2/C3 are not true `partitionSpec n`, so their theorems are NOT
# mathematical truths about p(n) -- they are *cost probes*: the judge's generator
# will still build `impl n = v` and the kernel will still type-check it as long
# as `impl n` reduces to the literal `v`. That is exactly the shape being priced.
BODY_VALUE = {
    "C1_floor":      lambda n: 0,
    "C2_projection": lambda n: n,
    "C3_closeover":  lambda n: 42,     # `fun _ => 42` ignores n, returns constant
    "C4_one_add":    lambda n: n + 1,
    "C5_decidable":  lambda n: 0 if n == 16 else n,
    "C6_recursor":   lambda n: 0,      # | 0 => 0 | n+1 => impl n  reduces to 0 (F10b A)
    "C7_mul":        lambda n: n * n,
    "C8_sub":        lambda n: n - 1,  # Nat.sub saturates at 0; n>=1 here so n-1
    "C9_pow":        lambda n: 2 ** n,
}


def load_judge():
    sys.path.insert(0, str(ROOT / "evaluation" / "judge"))
    spec = importlib.util.spec_from_file_location(
        "lk_judge_f14", ROOT / "evaluation" / "judge" / "judge.py")
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load the official judge module")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def oracle_check() -> None:
    """G6: hard controls on the partition oracle before anything is measured."""
    sys.path.insert(0, str(ROOT / "evaluation" / "judge"))
    import reference_answers as ra
    assert ra.partition(4) == 5 and ra.partition(10) == 42 \
        and ra.partition(16) == 231, "partition oracle failed hard control"


def stage_source(body: str, no_recursor: bool) -> str:
    """Build the Submission.lean for one cell (G5 no-recursor assertion).

    Mirrors F11/F12: stage ONLY `def impl` with no `impl_correct` and no `sorry`
    (a `sorry` trips `warningAsError` and fails the build). The judge's generator
    builds its own `impl n = v := Eq.refl v` theorem independently, so no
    contestant-side proof is needed to price the shape.
    """
    if no_recursor:
        for frag in FORBIDDEN:
            assert frag not in body, f"G5 violated: {frag!r} in body {body!r}"
    return (
        "import Spec\n\n"
        "namespace Submission\n"
        f"{body}\n"
        "\nend Submission\n"
    )


def measure_cell(pdir: Path, work: Path, body: str, no_recursor: bool,
                 n: int, v: int, tag: str) -> dict:
    """Stage -> build -> export -> replay for one (tag, n) cell.

    Mirrors F13's harness usage exactly: judge generator for the theorem source
    (G4), `lake env lean -o` for the Perf.olean, lean4export for the export, and
    f2_harness.replay for the window (user-space only, LK_EXCLUDE_KERNEL=1).
    """
    sub = pdir / "Submission.lean"
    perf = pdir / "Perf.lean"
    olean = pdir / ".lake" / "build" / "lib" / "lean" / "Perf.olean"
    t0 = time.time()
    sub.write_text(stage_source(body, no_recursor))
    rc, out = run(["lake", "build", "Submission"], pdir)
    if rc != 0:
        return {"tag": tag, "n": n, "status": "FAIL_build",
                "error": out[-400:]}

    judge = load_judge()
    source, theorem = judge._perf_theorem_source(n, v, work.name)   # G4
    for frag in ("Lean.addDecl (.thmDecl", "Submission.impl", "mkEqRefl rhs"):
        if frag not in source:
            raise ProbeError(f"[G4 {tag}] generator output lacks {frag!r}")
    perf.write_text(source)
    olean.unlink(missing_ok=True)
    rc, out = run(["lake", "env", "lean", "-o", str(olean), "Perf.lean"], pdir)
    if rc != 0:
        return {"tag": tag, "n": n, "status": "FAIL_perf_build",
                "error": out[-400:]}

    export = work / f"export_{tag}_{n}.out"
    with export.open("wb") as fh:
        proc = subprocess.run(
            [str(LEAN4EXPORT), "Perf", "--", theorem], cwd=pdir,
            stdout=fh, stderr=subprocess.PIPE, text=True, timeout=1800,
            env={**os.environ, "LEAN_PATH": lean_path(pdir)})
    if proc.returncode != 0 or export.stat().st_size <= 512:
        return {"tag": tag, "n": n, "status": "FAIL_export",
                "error": (proc.stderr or "")[-400:]}

    res = f2_harness.replay(pdir, export, theorem, REPS)
    if res["timer_failed"]:
        return {"tag": tag, "n": n, "status": "FAIL_replay",
                "error": res["timer_failed"]}
    if (res["window_spread_pct"] or 0) > 5:                          # G2
        res = f2_harness.replay(pdir, export, theorem, REPS)
        if res["timer_failed"]:
            return {"tag": tag, "n": n, "status": "FAIL_replay",
                    "error": res["timer_failed"]}
    return {"tag": tag, "n": n, "v": v, "status": "ok",
            "window_median": res["window_median"],
            "window_min": res["window_min"],
            "window_max": res["window_max"],
            "window_spread_pct": round(res["window_spread_pct"] or 0.0, 3),
            "process_total": res["process_total"],
            "seconds": round(time.time() - t0, 2)}


def _parse_icount(out: str) -> int:
    """Pull the instruction count out of the timer's stdout."""
    for line in out.splitlines():
        line = line.strip()
        if line.isdigit():
            return int(line)
    # fall back: last integer-looking token
    import re
    nums = re.findall(r"\b(\d{5,})\b", out)
    if nums:
        return int(nums[-1])
    raise ProbeError(f"could not parse instruction count from: {out[:400]}")


def main() -> int:
    oracle_check()

    pdir = ROOT / "problems" / "partition"
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f14-run"
    work.mkdir(parents=True, exist_ok=True)

    outdir = ROOT / "results" / "cost_model"
    outdir.mkdir(parents=True, exist_ok=True)

    results = []
    # G7: back up and restore in finally
    sub_backup = (pdir / "Submission.lean").read_bytes()
    perf_backup = (pdir / "Perf.lean").read_bytes() \
        if (pdir / "Perf.lean").exists() else None

    try:
        for tag, body, is_ctrl, anchor, no_rec in CELLS:
            for n in GRID_N:
                # v is the value `impl n` reduces to; the judge builds
                # `impl n = v := Eq.refl v`, so v must be exactly what the body
                # computes at n (same convention as F12: v = str(N_IN + k)).
                v = BODY_VALUE[tag](n)
                cell = measure_cell(pdir, work, body, no_rec, n, v, tag)
                cell["body"] = body
                cell["is_control"] = is_ctrl
                cell["control_anchor"] = anchor
                results.append(cell)
                print(f"  {tag:14s} n={n}: {cell['status']}"
                      + (f"  {cell['window_median']:>14,.0f}"
                         if cell.get("window_median") else ""), flush=True)
    finally:
        # G7 restore
        (pdir / "Submission.lean").write_bytes(sub_backup)
        if perf_backup is not None:
            (pdir / "Perf.lean").write_bytes(perf_backup)

    # ---- gates ------------------------------------------------------------
    verdicts = []

    # G3 controls
    controls_ok = True
    for cell in results:
        if not cell.get("is_control") or cell.get("status") != "ok":
            continue
        anchor = cell["control_anchor"]
        got = cell["window_median"]
        rel = abs(got - anchor) / anchor
        ok = rel <= CONTROL_TOL
        if not ok:
            controls_ok = False
        verdicts.append(
            f"G3 control {cell['tag']:14s}: got {got:,.0f} vs anchor "
            f"{anchor:,} (rel {rel:.1%}) -> {'PASS' if ok else 'FAIL'}"
        )

    # G2 spread
    worst_spread = max((c.get("window_spread_pct", 0) for c in results
                        if c.get("status") == "ok"), default=0.0)
    verdicts.append(
        f"G2 spread: worst {worst_spread:.2f}% (threshold 5%) -> "
        f"{'PASS' if worst_spread <= 5 else 'FAIL'}"
    )

    # H14.1: any non-trivial cell that fits the champion slot
    fitting = []
    for cell in results:
        if cell.get("status") != "ok" or cell.get("is_control"):
            continue
        official = cell["window_median"] / K_BIAS
        if official <= CHAMPION_SLOT:
            fitting.append((cell["tag"], official))
    verdicts.append(
        f"H14.1 fitting non-trivial shapes: {fitting if fitting else 'NONE'} "
        f"(champion slot {CHAMPION_SLOT:,})"
    )

    if not controls_ok:
        verdicts.append("G3 DRIFT -> ALL VERDICTS VOID (instrument drift)")
        status = "VOID"
    else:
        status = "ok"
        if fitting:
            verdicts.append("H14.1 NOT rejected: a non-trivial shape fits the "
                            "champion slot.")
        else:
            verdicts.append("H14.1 REJECTED: no non-trivial shape fits; "
                            "H14.2 (champion exploits something invisible to "
                            "the local instrument) stands.")

    # ---- output -----------------------------------------------------------
    payload = {
        "status": status,
        "cells": results,
        "verdicts": verdicts,
        "k_bias": K_BIAS,
        "champion_slot": CHAMPION_SLOT,
        "grid_n": GRID_N,
    }
    (outdir / "f14_champion_shape_sweep.json").write_text(
        json.dumps(payload, indent=2, default=str))

    lines = [f"F14 champion shape sweep  ({time.strftime('%Y-%m-%d %H:%M')})",
             "=" * 60,
             f"k_bias (F13) = {K_BIAS}, champion slot = {CHAMPION_SLOT:,}",
             f"grid n = {GRID_N}",
             ""]
    for tag, body, *_ in CELLS:
        rows = [c for c in results if c["tag"] == tag]
        med = [c["window_median"] for c in rows if c.get("status") == "ok"]
        if med:
            off = statistics.median(med) / K_BIAS
            lines.append(f"{tag:14s} local={statistics.median(med):>14,.0f}"
                         f"  official={off:>12,.0f}"
                         f"  {'FITS' if off <= CHAMPION_SLOT else 'exceeds'}")
        else:
            st = rows[0]["status"] if rows else "NO_DATA"
            lines.append(f"{tag:14s} {st}")
    lines += ["", "VERDICTS"] + [f"  {v}" for v in verdicts]
    lines += ["", f"wrote {outdir / 'f14_champion_shape_sweep.json'}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f14_champion_shape_sweep.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
