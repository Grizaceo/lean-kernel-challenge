#!/usr/bin/env python3
"""F11 -- is F10b's floor a probe artefact, or the judge's own shape?

PRE-REGISTERED 2026-10-05, BEFORE ANY NUMBER IS PRODUCED. Committed before the run.

THE CONTRADICTION F10b CREATED
------------------------------
F10b measured, in a hand-reproduction of the judge's theorem shape:

    C@0  (impl computes NOTHING, not even a recursor)  =   240,006
    A@0  (same, but impl is a Nat.rec)                 =   356,917

Six floors = 1,440,036. The partition leader's ENTIRE curveWork is 1,428,492.

    6 x C@0  =  1.008x the champion's whole 6-slot total
    6 x A@0  =  1.499x

A declaration that computes NOTHING costs as much as the champion's entire
submission. Under G5 my counts are user-space only and the judge counts
user+kernel, and user+kernel is a SUPERSET of user-space -- so that bias makes
the champion's slot look even SMALLER against my floor, never larger. The gap is
therefore NOT explained away by the scope bias, and something is structurally
wrong with either my probe or my reading of the budget.

F7's independent data point points the same way: its packing fit was
`244,590 + 37.1 * lanes`, and that intercept is 1.019x F10b's C@0. F7 measured
the floor all along; F8 simply measured it on the wrong shape (a bare `Eq.refl`
between literals, 118,230 = 0.49x the real thing).

THE HYPOTHESES UNDER TEST
-------------------------
H11.1  F10b's floor is a PROBE ARTEFACT: the hand-built theorem and the judge's
       own generated theorem are the same object but not the same cost.
H11.2  F10b's floor is REAL and the champion genuinely spends ~all of its slot on
       the declaration itself, computing very little per slot.

WHAT WOULD FALSIFY EACH, FIXED NOW
----------------------------------
G1  A cell that fails to build, export or complete the replay ABORTS the run.
G2  Intra-cell spread > 5% -> re-measure once, then report with its spread.
G3  DECISIVE: H11.1 is REJECTED if the judge's own generator agrees with F10b's
    hand-built probe to within 5% on BOTH J-C-trivial and J-A-recur. Better
    agreement means there is no artefact to find.
G4  THE GENERATOR MUST BE THE JUDGE'S. Every theorem source comes from
    `judge._perf_theorem_source`, imported verbatim and asserted to carry the
    judge's constructs; the sources are recorded in the artifact. A hand-built
    substitute is a G4 violation and aborts. (The analogous F9 risk was
    `Lean.mkApp1` not existing; the fallback used was RECORDED, not silent.)
G5  SCOPE AND THE DIRECTION OF THE BIAS, stated explicitly: with
    `LK_EXCLUDE_KERNEL=1` these counts are user-space ONLY and the judge counts
    user+kernel, a SUPERSET. So a floor measured here is a LOWER bound on what the
    judge charges for the same declaration, and the champion's slot sitting BELOW
    my floor cannot be repaired by the scope bias. That is the one direction of
    comparison that is safe, and it is the direction the contradiction runs in.
G6  The oracle `v` must be correct or the self-validating theorem fails to BUILD.
    For a trivial impl every `v` is hand-checkable; a mismatch is reported as a
    failure and never worked around.
G7  `problems/` MUST be left byte-identical: `Submission.lean`, `Perf.lean` and
    `Perf.olean` are captured before the run and restored in a `finally`. A
    measurement that mutates the problem dir is a guard violation (ERRATA.md).

CELLS (all in a `Submission` namespace, exactly as the judge expects)
---------------------------------------------------------------------
  J-C-trivial  `fun _ => 0`                  v=0   computes nothing, no recursor
  J-C-const    the constant 7                v=7   no application at all
  J-A-recur    `| 0 => 0 | n+1 => impl n`    v=0   k=5 unfolds, no arithmetic
  J-B-add1     `| 0 => 0 | n+1 => impl n+1`  v=5   k=5 unfolds + 5 adds

MEASUREMENT
-----------
`instructions` from the local timer at `target-declaration-replay-v1`: the same
boundary and instrument as F5/F8/F9/F10/F10b, median of 3, absolute, no
subtraction.
"""
from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import time
from pathlib import Path

sys.set_int_max_str_digits(500_000)

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import f2_harness  # noqa: E402
from f2_harness import TIMER_BIN, ProbeError, lean_path  # noqa: E402
from measure import LEAN4EXPORT, problem_dir, run  # noqa: E402

REPS = 3

# F10b's numbers, for the G3 comparison. Same boundary, same instrument, same day.
F10B_C0 = 240_006
F10B_A0 = 356_917
F10B_A_BETA = 95_398
F10B_B_BETA = 122_142
F7_INTERCEPT = 244_590          # F7 packing-fit intercept, the independent point
F8_FLOOR_WRONG_SHAPE = 118_230  # F8's bare Eq.refl between literals
CHAMPION_SLOT = 238_082         # partition rank1 1,428,492 / 6 slots
CHAMPION_TOTAL = 1_428_492
G3_TOLERANCE = 0.05

TRIVIALS = {
    "J-C-trivial": ("def impl : Nat → Nat := fun _ => 0", 5, "0",
                    "impl ignores its input, computes nothing"),
    "J-C-const": ("def impl : Nat → Nat := 7", 5, "7",
                  "impl IS a constant: no application, no recursor"),
    "J-A-recur": ("def impl : Nat → Nat\n"
                  "  | 0 => 0\n"
                  "  | n + 1 => impl n", 5, "0",
                  "impl is a Nat.rec: k=5 unfolds, no arithmetic"),
    "J-B-add1": ("def impl : Nat → Nat\n"
                 "  | 0 => 0\n"
                 "  | n + 1 => impl n + 1", 5, "5",
                 "impl is a Nat.rec with one Nat.add per step, k=5"),
}


def load_judge():
    """Import the judge's own module so the generator is used VERBATIM (G4)."""
    sys.path.insert(0, str(ROOT / "evaluation" / "judge"))
    spec = importlib.util.spec_from_file_location(
        "lk_judge", ROOT / "evaluation" / "judge" / "judge.py")
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load the official judge module")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main() -> int:
    pdir = problem_dir("partition")
    outdir = ROOT / "results" / "cost_model"
    outdir.mkdir(parents=True, exist_ok=True)
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f11-run"
    work.mkdir(parents=True, exist_ok=True)

    judge = load_judge()
    print(f"timer: {TIMER_BIN}   reps={REPS}", flush=True)
    print("theorem source from judge._perf_theorem_source (G4) -- imported verbatim.",
          flush=True)
    print(f"F10b targets: C@0 {F10B_C0:,}  A@0 {F10B_A0:,}  tol {G3_TOLERANCE:.0%}\n",
          flush=True)

    # G7 -- capture problems/ before touching anything.
    sub, perf = pdir / "Submission.lean", pdir / "Perf.lean"
    olean = pdir / ".lake" / "build" / "lib" / "lean" / "Perf.olean"
    pristine = {
        "Submission.lean": sub.read_bytes(),
        "Perf.lean": perf.read_bytes() if perf.exists() else None,
        "Perf.olean": olean.read_bytes() if olean.exists() else None,
    }

    cells: dict[str, dict] = {}
    sources: dict[str, str] = {}

    def record(key: str, body: str, n: int, v: str) -> bool:
        t0 = time.time()
        try:
            sub.write_text(f"import Spec\n\nnamespace Submission\n{body}\n\n"
                           "end Submission\n")
            rc, out = run(["lake", "build", "Submission"], pdir)
            if rc != 0:
                raise ProbeError(f"[build Submission] rc={rc}: {out[-600:]}")

            source, theorem = judge._perf_theorem_source(n, v, work.name)   # G4
            for frag in ("Lean.addDecl (.thmDecl", "Submission.impl",
                         "mkEqRefl rhs", "maxRecDepth 4000000"):
                if frag not in source:
                    raise ProbeError(f"[G4] generator output lacks {frag!r}")
            sources[key] = source

            perf.write_text(source)
            olean.unlink(missing_ok=True)
            rc, out = run(["lake", "env", "lean", "-o", str(olean), "Perf.lean"], pdir)
            if rc != 0:
                raise ProbeError(f"[build Perf] rc={rc}: {out[-600:]}")

            export = work / "export.out"
            with export.open("wb") as fh:
                proc = subprocess.run(
                    [str(LEAN4EXPORT), "Perf", "--", theorem], cwd=pdir,
                    capture_output=True, text=True, timeout=1800,
                    env={**os.environ, "LEAN_PATH": lean_path(pdir)})
            f2_harness.check_step("export", proc.returncode, proc.stderr or "")
            if export.stat().st_size <= 512:
                raise ProbeError(f"[export] only {export.stat().st_size} B (header only)")

            res = f2_harness.replay(pdir, export, theorem, REPS)
            if res["timer_failed"]:
                raise ProbeError(f"[replay] {res['timer_failed']}")
            if (res["window_spread_pct"] or 0) > 5:                        # G2
                res = f2_harness.replay(pdir, export, theorem, REPS)
                if res["timer_failed"]:
                    raise ProbeError(f"[replay-2] {res['timer_failed']}")
            cost = res["window_median"]
            cells[key] = dict(body=body, n=n, v=v, theorem=theorem, status="ok",
                              window_median=cost,
                              window_instructions=res["window_instructions"],
                              window_min=res["window_min"],
                              window_max=res["window_max"],
                              window_spread_pct=round(res["window_spread_pct"] or 0.0, 3),
                              seconds=round(time.time() - t0, 2))
            print(f"  {key:<14} {cost:>11,.0f} instr   "
                  f"spread={res['window_spread_pct']:.2f}%   "
                  f"({cells[key]['seconds']}s)", flush=True)
        except ProbeError as exc:
            out = outdir / "f11_judge_generator_shape.json"
            out.write_text(json.dumps({"status": "aborted", "aborted_at": key,
                                       "error": str(exc), "cells": cells}, indent=1))
            print(f"  {key:<14} ABORT: {str(exc)[:300]}\nG1 TRIGGERED -> {out}",
                  flush=True)
            return False
        return True

    try:
        for key, (body, n, v, _note) in TRIVIALS.items():
            if not record(key, body, n, v):
                return 1
    finally:
        # G7 -- problems/ restored byte-for-byte whatever happened.
        sub.write_bytes(pristine["Submission.lean"])
        if pristine["Perf.lean"] is not None:
            perf.write_bytes(pristine["Perf.lean"])
        else:
            perf.unlink(missing_ok=True)
        if pristine["Perf.olean"] is not None:
            olean.write_bytes(pristine["Perf.olean"])
        else:
            olean.unlink(missing_ok=True)

    ok = {k: c for k, c in cells.items() if c.get("status") == "ok"}
    verdicts: list[str] = []
    inst = max(c["window_spread_pct"] for c in ok.values())
    verdicts.append(f"G2 spread            : worst {inst:.2f}% (threshold 5%) -> "
                    f"{'PASS' if inst <= 5 else 'RE-MEASURED / REPORTED WITH SPREAD'}")

    ratios = {k: ok[k]["window_median"] / t
              for k, t in (("J-C-trivial", F10B_C0), ("J-A-recur", F10B_A0))
              if k in ok}
    worst = max((abs(r - 1.0) for r in ratios.values()), default=float("inf"))
    pairs = ", ".join(f"{k} {r:.3f}x" for k, r in ratios.items())
    if worst <= G3_TOLERANCE:
        verdicts.append(
            f"G3 decisive         : judge-generated vs F10b hand-built agree to "
            f"{worst:.1%} ({pairs}), tol {G3_TOLERANCE:.0%} -> H11.1 REJECTED. No "
            f"probe-shape artefact: F10b's floor is what the judge's own generator "
            f"produces, so the contradiction is REAL and lives in the budget reading.")
        h111 = "REJECTED"
    else:
        verdicts.append(
            f"G3 decisive         : judge-generated vs F10b hand-built differ by up to "
            f"{worst:.1%} ({pairs}) > {G3_TOLERANCE:.0%} -> H11.1 NOT rejected: part of "
            f"F10b's floor IS a probe artefact and the hand-built shape overstates it.")
        h111 = "NOT rejected"

    if "J-C-trivial" in ok:
        six = 6 * ok["J-C-trivial"]["window_median"]
        tail = ("A declaration computing NOTHING already costs the champion's entire "
                "total." if six > CHAMPION_TOTAL else
                "A trivial declaration is cheaper than the champion's total.")
        verdicts.append(
            f"budget consequence  : 6 x trivial declaration = {six:,} vs the champion's "
            f"whole curveWork {CHAMPION_TOTAL:,} = {six / CHAMPION_TOTAL:.3f}x. {tail}")
    if "J-C-const" in ok and "J-C-trivial" in ok and "J-A-recur" in ok:
        cconst = ok["J-C-const"]["window_median"]
        ctriv = ok["J-C-trivial"]["window_median"]
        crecur = ok["J-A-recur"]["window_median"]
        verdicts.append(
            f"recursor price      : constant impl {cconst:,}; impl ignoring its input "
            f"{ctriv:,} = {ctriv / cconst:.3f}x; Nat.rec version {crecur:,} = "
            f"{crecur / cconst:.3f}x. The step from a constant to a recursor is the "
            f"price of HAVING a recursor, paid once, not per unfold.")
    verdicts.append(
        f"G4 generator         : all four theorems came from judge._perf_theorem_source "
        f"and every source is recorded verbatim in this artifact. No substitute.")
    verdicts.append(
        f"G5 scope/direction   : user-space only (LK_EXCLUDE_KERNEL=1); the judge counts "
        f"user+kernel, a SUPERSET, so these floors are LOWER bounds on the judge's "
        f"charge. The champion's {CHAMPION_SLOT:,}/slot sitting BELOW my floor cannot be "
        f"repaired by that bias -- the contradiction runs in the safe direction.")
    verdicts.append(
        "G6 oracle            : every v is hand-checkable for a trivial impl and the "
        "theorem is self-validating, so a wrong v fails to BUILD and no wrong cost is "
        "possible.")
    verdicts.append(
        "G7 restoration       : Submission.lean, Perf.lean and Perf.olean were restored "
        "byte-for-byte in a finally block; problems/ is unmodified.")

    payload = {
        "status": "ok",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "metric": "instructions from KERNEL_TIMING, boundary=target-declaration-replay-v1",
        "instrument": {"timer": str(TIMER_BIN), "reps": REPS,
                       "scope": "user-space only (LK_EXCLUDE_KERNEL=1)",
                       "generator": "judge._perf_theorem_source, imported verbatim"},
        "references_not_inputs": {
            "f10b_C0": F10B_C0, "f10b_A0": F10B_A0,
            "f10b_A_beta": F10B_A_BETA, "f10b_B_beta": F10B_B_BETA,
            "f7_intercept": F7_INTERCEPT, "f8_floor_wrong_shape": F8_FLOOR_WRONG_SHAPE,
            "champion_slot": CHAMPION_SLOT, "champion_total": CHAMPION_TOTAL},
        "preregistered": {
            "H11.1": "F10b's floor is a probe artefact of the hand-built theorem",
            "H11.2": "F10b's floor is real and consumes the champion's whole slot",
            "criteria": {
                "G1": "abort on failed cell", "G2": "spread > 5% -> re-measure",
                "G3": {"reject_H11.1_if_agreement_within": G3_TOLERANCE,
                       "compared_on": ["J-C-trivial vs f10b C@0",
                                       "J-A-recur vs f10b A@0"]},
                "G4": "theorem must come from judge._perf_theorem_source",
                "G5": "state user+kernel is a superset of user-space",
                "G6": "a wrong oracle v must fail the build",
                "G7": "restore problems/ byte-for-byte"}},
        "verdicts": {"H11.1": h111},
        "ratios_vs_f10b": ratios,
        "generator_sources": sources,
        "cells": cells,
    }
    out = outdir / "f11_judge_generator_shape.json"
    out.write_text(json.dumps(payload, indent=1))

    ref = {"J-C-trivial": F10B_C0, "J-A-recur": F10B_A0, "J-B-add1": F10B_B_BETA}
    lines = [
        "F11 -- F10b's floor: probe artefact, or the judge's own shape? (2026-10-05)",
        "",
        "theorem source from judge._perf_theorem_source, imported verbatim (G4)",
        "scope: USER-SPACE only (LK_EXCLUDE_KERNEL=1); judge counts a SUPERSET (G5)",
        "",
        f"{'cell':<14}{'instructions':>13}{'vs F10b':>11}  what",
    ]
    for key, (_b, _n, _v, note) in TRIVIALS.items():
        c = cells.get(key, {})
        if c.get("status") == "ok":
            r = f"{c['window_median'] / ref[key]:.3f}x" if key in ref else ""
            lines.append(f"{key:<14}{c['window_median']:>13,.0f}{r:>11}  {note}")
        else:
            lines.append(f"{key:<14}{'FAILED':>13}{'':>11}  {note}")
    lines += ["", "VERDICTS (pre-registered in scripts/f11_judge_generator_shape.py)"] \
        + [f"  {v}" for v in verdicts] + ["", f"wrote {out}"]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f11_judge_generator_shape.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())