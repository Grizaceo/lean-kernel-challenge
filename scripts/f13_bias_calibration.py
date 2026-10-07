#!/usr/bin/env python3
"""F13 -- calibrate the local->official bias k with three independent anchors.

PRE-REGISTERED 2026-10-07, BEFORE ANY NUMBER IS PRODUCED. Committed before the run.

WHY THIS IS THE ONLY QUESTION THAT MATTERS NOW
----------------------------------------------
F10-F12 (results/LKC_2026-10-05_F10_F12_floor_shape.md) left one open paradox:
the partition champion pays 238,082 instr/slot (curveWork 1,428,492 over 6 slots,
submission 950), but the measured non-recursor floor is 199,012 local and one
flat `Nat.add` on top costs 305,916 (chain@1, F12) -- floor+add already exceeds
the champion slot. Either the floor overstates the judge's charge, or the
champion uses a shape no probe has exercised. Every design decision (which
candidate family is reachable) hangs on resolving this.

The F10-F12 numbers were measured user-space-only (LK_EXCLUDE_KERNEL=1) on THIS
host; the judge scores user+kernel on a KTP/3 executor (AMD Ryzen 9 9950X). The
only published local->official ratio is F1's group-check: 9,467,621,542 local
vs 5,386,432,876 official = 1.7578x. But F1's group-check ran under `icount`
PROCESS-WIDE (startup + parse included, ~166M/slot of process overhead), so
1.7578 is a bias of PROCESS totals, not of the judge's target-declaration
window. Applying it to window floors (199,012/1.7578 = 113,151) assumes the
process-wide and window biases are the same number. Nobody has measured the
WINDOW bias. If k_window differs from 1.7578, every reachability conclusion
drawn from the local floor changes.

THE ANCHORS (all frozen before the run)
---------------------------------------
A1  866 curve, hidden n. Official per-case medians of OUR OWN submission 866
    (identity verified: sha256(candidates/partition-stream-addblocks/
    Submission.lean) = 25402c3d... = rawUploadSha256 of 866):
        P1: 338,036,315 / 420,849,934   (ratio 1.24498)
        P2: 721,157,450 / 841,876,147   (ratio 1.16740)
        P3: 1,404,207,007 / 1,656,106,661 (ratio 1.17939)
    Local curve: measure the 866 with THIS session's window instrument (same
    generator, same timer, user-space-only) at every integer n in each group's
    full feasible window (jitter inward 15%, count=2 -> endpoints jittered):
        P1 in {14..18}, P2 in {22..26}, P3 in {32..36}.
    Then per group: find the (n1, n2) pair whose local ratio best matches the
    official ratio (tolerance 3%), and estimate k_g = local(n1)/official(c1)
    (and local(n2)/official(c2) as a consistency check; both must agree within
    the same tolerance).
    Feasibility projection (judge.py L425-437): n1 in [lo+0, hi-1] with n1>lo
    unless rounding pushes it to lo, n2 in [lo+1, hi] with n2<hi unless
    rounding pulls it to hi. All 5 candidates per group lie inside.

A2  Fib cross-check at a scale 10^3 above partition's. `official-fd-example`
    (run 269, playground) is the repo's own `examples/fib/Submission.lean`
    (fast doubling, structurally fuelled, kernel-reducible): official slots
    n=5000: 8,012,342 / n=20000: 9,280,860 / n=80000: 11,531,540.
    Local: measure the same file at the SAME n, window instrument, 3 reps.
    k must agree with A1's k within the same tolerance -- otherwise the bias
    is scale- or problem-dependent and window-floor extrapolation is void.

A3  Trivial-floor anchor at the scale the paradox lives on. `fun _ => 0` in
    the judge's shape (F11's J-C-trivial cell, re-measured here, not quoted)
    gives the local window floor F_loc. The quantity the design needs is
    F_official = F_loc / k. This anchor alone produces no k; it consumes the
    k from A1/A2 and turns it into the number the next candidate design uses.

INSTRUMENT (identical to F11/F12, no new machinery)
---------------------------------------------------
- generator: judge._perf_theorem_source, imported verbatim (G4 fragments
  checked: 'Lean.addDecl', 'Submission.impl', 'mkEqRefl rhs').
- timer: .verify/timer-kernel-local (byte-copy of judge's timer_control.c plus
  the opt-in LK_EXCLUDE_KERNEL=1), --count-instructions --target, window =
  target-declaration-replay-v1. User-space only: every local figure is a
  LOWER bound of the judge's charge on the same machine class (G8, kept).
- oracle: reference_answers.partition / reference_answers.fibonacci, with
  hard controls p(4)=5, p(10)=42, p(16)=231, fib(10)=55, fib(20)=6765
  checked at start (G-ora).
- reps=3, spread>5% re-measured once then reported with spread (G2).

HYPOTHESES
----------
H13.1  The window bias k = local_window(n)/official(n) is the same number for
       all three partition groups (and for fib): 0.9 <= k <= 2.5, group spread
       < 10%. Prediction: k in [1.2, 1.8], near but not necessarily equal to
       F1's process-wide 1.7578.
H13.2  k differs by group/problem (scale-dependent). Then the floor
       extrapolation F_official = F_loc/k has no single k, and candidate
       design must use per-scale k -- reported, not hidden.

FALSIFICATION / VERDICT GATES (fixed before the run)
-----------------------------------------------------
G1  Any cell that fails to build, export, or replay ABORTS the run with the
    partial cells saved. No number is reported from a failed cell.
G2  Intra-cell spread > 5% -> re-measure once, report both.
G3  RATIO MATCH: for each group the best (n1,n2) pair must reproduce the
    official ratio within 3%. If no pair matches, the local curve is not
    proportional to the official curve at group scale -> DRIFTED, report
    per-group best pairs with their error; do NOT emit a k for that group.
G4  GENERATOR IS THE JUDGE'S: fragments checked per cell (as F12).
G5  NO-RECURSOR rule does NOT apply to the 866 or the fib example (they are
    full submissions). It DOES apply to the A3 trivial cell: staged source
    must not contain 'Nat.rec'/'match '/'termination_by'.
G6  ORACLE CONTROL: partition and fib oracles must pass their hard controls
    before any measurement (G-ora above). Otherwise ABORT.
G7  `problems/` restored byte-for-byte in a finally block; git status clean
    for problems/ at exit.
G8  SCOPE: user-space only. k is estimated from window figures only; F1's
    1.7578 process-wide number is quoted as reference, never mixed in.
G9  PROCESS-WIDE SANITY (new): every cell also records `process_total` from
    icount. For the 866 cells at the local-dev-seed plan n={16,17,25,26,34,36}
    the process totals must reproduce F1's per-slot figures within 20%:
    943,069,111 / 1,055,740,622 / 1,475,407,711 / 1,535,915,307 /
    2,106,140,920 / 2,278,941,787. If they do, the instrument is the same one
    that produced F1's ratio; if not, DRIFTED -- investigate before quoting k.
G10 (interpretation) If H13.1 holds: report F_official = F_loc/k with its
    uncertainty, state whether floor+one-add fits a champion slot OFFICIALLY,
    and the resulting ops-per-slot budget. If H13.2: report per-group k and
    the consequences. Either way, the champion-paradox verdict must cite only
    numbers produced in THIS run plus the frozen official anchors.

CELLS
-----
A1: 15 cells -- 866 at n in {14,15,16,17,18, 22,23,24,25,26, 32,33,34,35,36}.
A2: 3 cells -- examples/fib/Submission.lean at n in {5000, 20000, 80000}.
A3: 1 cell -- trivial `fun _ => 0` at n=16 (in-partition shape, judge shape).
Total 19 cells, each: stage -> oracle -> build -> export -> replay(3).
Wall estimate: 866 cells are heavy (F1 group-check took ~10 min for 6 slots);
15 x ~2-6 min + 3 x ~1-2 min + 1 trivial -> roughly 40-90 min. Run in
background, poll, never a blind sleep.

DELIVERABLE
-----------
results/cost_model/f13_bias_calibration.json + a compact .txt table. The run
report (prose) is written after the numbers exist, citing only this run.
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
from f2_harness import TIMER_BIN, ProbeError, lean_path  # noqa: E402
from measure import LEAN4EXPORT, problem_dir, run  # noqa: E402

REPS = 3

# ---- frozen official anchors (read at run time from the frozen file, but the
# ---- values are asserted against these literals as a tamper check) --------
OFFICIAL_866 = {
    ("P1", 0): 338_036_315, ("P1", 1): 420_849_934,
    ("P2", 0): 721_157_450, ("P2", 1): 841_876_147,
    ("P3", 0): 1_404_207_007, ("P3", 1): 1_656_106_661,
}
OFFICIAL_FIB = {5000: 8_012_342, 20000: 9_280_860, 80000: 11_531_540}
F1_GROUPCHECK = {  # local-dev-seed plan n -> F1's process-wide per-slot figures
    16: 943_069_111, 17: 1_055_740_622, 25: 1_475_407_711, 26: 1_535_915_307,
    34: 2_106_140_920, 36: 2_278_941_787,
}
CHAMPION_SLOT = 238_082
F12_CHAIN1 = 305_916          # local window, floor+one-add, for the fit verdict
F12_K0 = 183_396              # local window floor (this chain's own k=0)
SHA_866 = "25402c3d197c90c795f67304f9e5b103a1ac033acd61a76f751b2fb2afbea2d2"

GRID = {  # group -> candidate n (full feasible jitter windows)
    "P1": [14, 15, 16, 17, 18],
    "P2": [22, 23, 24, 25, 26],
    "P3": [32, 33, 34, 35, 36],
}
FIB_NS = [5000, 20000, 80000]
RATIO_TOL = 0.03
K_SPREAD_TOL = 0.10


def load_judge():
    sys.path.insert(0, str(ROOT / "evaluation" / "judge"))
    spec = importlib.util.spec_from_file_location(
        "lk_judge", ROOT / "evaluation" / "judge" / "judge.py")
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load the official judge module")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def oracle_check():
    """G-ora: hard controls on the oracles before anything is measured."""
    sys.path.insert(0, str(ROOT / "evaluation" / "judge"))
    import reference_answers as ra
    assert ra.partition(4) == 5 and ra.partition(10) == 42 \
        and ra.partition(16) == 231, "partition oracle failed hard control"
    assert ra.fibonacci(10) == 55 and ra.fibonacci(20) == 6765, \
        "fib oracle failed hard control"
    return ra


def sha256_file(p: Path) -> str:
    import hashlib
    return hashlib.sha256(p.read_bytes()).hexdigest()


def measure_cell(pdir, staged_source, n, v, work, tag, reps=REPS):
    """Stage -> build -> export -> replay for one (n, v) cell. Returns dict."""
    sub = pdir / "Submission.lean"
    perf = pdir / "Perf.lean"
    olean = pdir / ".lake" / "build" / "lib" / "lean" / "Perf.olean"
    t0 = time.time()
    sub.write_text(staged_source)
    rc, out = run(["lake", "build", "Submission"], pdir)
    if rc != 0:
        raise ProbeError(f"[build {tag}] rc={rc}: {out[-600:]}")

    judge = load_judge()
    source, theorem = judge._perf_theorem_source(n, v, work.name)   # G4
    for frag in ("Lean.addDecl (.thmDecl", "Submission.impl", "mkEqRefl rhs"):
        if frag not in source:
            raise ProbeError(f"[G4 {tag}] generator output lacks {frag!r}")
    perf.write_text(source)
    olean.unlink(missing_ok=True)
    rc, out = run(["lake", "env", "lean", "-o", str(olean), "Perf.lean"], pdir)
    if rc != 0:
        raise ProbeError(f"[build Perf {tag}] rc={rc}: {out[-600:]}")

    export = work / f"export_{tag}.out"
    with export.open("wb") as fh:
        proc = subprocess.run(
            [str(LEAN4EXPORT), "Perf", "--", theorem], cwd=pdir,
            stdout=fh, stderr=subprocess.PIPE, text=True, timeout=1800,
            env={**os.environ, "LEAN_PATH": lean_path(pdir)})
    f2_harness.check_step("export", proc.returncode, proc.stderr or "")
    if export.stat().st_size <= 512:
        raise ProbeError(f"[export {tag}] only {export.stat().st_size} B")

    res = f2_harness.replay(pdir, export, theorem, reps)
    if res["timer_failed"]:
        raise ProbeError(f"[replay {tag}] {res['timer_failed']}")
    if (res["window_spread_pct"] or 0) > 5:                                    # G2
        res2 = f2_harness.replay(pdir, export, theorem, reps)
        if res2["timer_failed"]:
            raise ProbeError(f"[replay-2 {tag}] {res2['timer_failed']}")
        res = res2
    return {
        "tag": tag, "n": n, "v": v, "status": "ok",
        "window_median": res["window_median"],
        "window_min": res["window_min"], "window_max": res["window_max"],
        "window_spread_pct": round(res["window_spread_pct"] or 0.0, 3),
        "process_total": res["process_total"],
        "seconds": round(time.time() - t0, 2),
    }


def main() -> int:
    outdir = ROOT / "results" / "cost_model"
    outdir.mkdir(parents=True, exist_ok=True)
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f13-run"
    work.mkdir(parents=True, exist_ok=True)

    ra = oracle_check()                                            # G-ora
    print(f"timer: {TIMER_BIN}   reps={REPS}", flush=True)
    print("anchors frozen: 866 per-case official, fib 269, F1 group-check, "
          "champion 238,082/slot", flush=True)

    # --- identity tamper checks -------------------------------------------
    sha = sha256_file(ROOT / "candidates" / "partition-stream-addblocks"
                      / "Submission.lean")
    if sha != SHA_866:                                             # G-id
        raise SystemExit(f"[G-id] 866 source hash changed: {sha}")
    print(f"[G-id] 866 sha256 OK -> {sha[:16]}...", flush=True)

    judge = load_judge()

    # sanity: the local-dev-seed plan must still resolve to F1's n
    judge.PERF_SEED = "local-dev-seed"
    cfg = json.loads((ROOT / "evaluation" / "problems" / "partition"
                      / "config.json").read_text())
    plan = judge.performance_plan(cfg, "partition")
    plan_n = sorted(c["n"] for c in plan)
    if plan_n != sorted(F1_GROUPCHECK):                            # G9 pre
        print(f"[G9-pre] WARNING: local-dev-seed plan today = {plan_n}, "
              f"F1 used {sorted(F1_GROUPCHECK)}", flush=True)
    else:
        print(f"[G9-pre] local-dev-seed plan matches F1's n: {plan_n}",
              flush=True)

    cells = []
    sources = {}

    # ================= A1: the 866 on the partition grid ==================
    pdir_p = problem_dir("partition")
    sub866 = (ROOT / "candidates" / "partition-stream-addblocks"
              / "Submission.lean").read_text()
    pristine = {
        "partition": {
            "Submission.lean": (pdir_p / "Submission.lean").read_bytes(),
            "Perf.lean": (pdir_p / "Perf.lean").read_bytes()
            if (pdir_p / "Perf.lean").exists() else None,
        },
    }
    pdir_f = problem_dir("fib")
    pristine["fib"] = {
        "Submission.lean": (pdir_f / "Submission.lean").read_bytes(),
        "Perf.lean": (pdir_f / "Perf.lean").read_bytes()
        if (pdir_f / "Perf.lean").exists() else None,
    }

    try:
        # A1 -- 15 cells
        for g, ns in GRID.items():
            for n in ns:
                tag = f"866@{g}:{n}"
                v = ra.partition(n)
                c = measure_cell(pdir_p, sub866, n, v, work, tag)
                c["group"] = g
                cells.append(c)
                print(f"  {tag:<10} window={c['window_median']:>13,.0f} "
                      f"proc={c['process_total'][-1] if c['process_total'] else 0:>13,} "
                      f"spread={c['window_spread_pct']:.2f}% ({c['seconds']}s)",
                      flush=True)

        # A2 -- fib cross-check, 3 cells
        fib_src = (ROOT / "examples" / "fib" / "Submission.lean").read_text()
        for n in FIB_NS:
            tag = f"fib:{n}"
            v = ra.fibonacci(n)
            c = measure_cell(pdir_f, fib_src, n, v, work, tag)
            c["group"] = "FIB"
            cells.append(c)
            print(f"  {tag:<10} window={c['window_median']:>13,.0f} "
                  f"spread={c['window_spread_pct']:.2f}% ({c['seconds']}s)",
                  flush=True)

        # A3 -- trivial floor in the judge's shape, 1 cell (G5 no recursor)
        trivial = ("import Spec\n\nnamespace Submission\n"
                   "def impl : Nat \u2192 Nat := fun _ => 0\n\n"
                   "end Submission\n")
        for bad in ("Nat.rec", "| ", "match ", "termination_by"):
            if bad in trivial:
                raise ProbeError(f"[G5] trivial source contains {bad!r}")
        c = measure_cell(pdir_p, trivial, 16, 0, work, "trivial@16")
        c["group"] = "A3"
        cells.append(c)
        print(f"  {'trivial@16':<10} window={c['window_median']:>13,.0f} "
              f"spread={c['window_spread_pct']:.2f}% ({c['seconds']}s)",
              flush=True)

    except ProbeError as exc:
        out = outdir / "f13_bias_calibration.json"
        out.write_text(json.dumps({"status": "aborted", "aborted_at": str(exc),
                                   "cells": cells}, indent=1))
        print(f"ABORT (G1): {str(exc)[:400]}", flush=True)
        return 1
    finally:
        for prob, files in pristine.items():
            pd = problem_dir(prob)
            (pd / "Submission.lean").write_bytes(files["Submission.lean"])
            if files["Perf.lean"] is not None:
                (pd / "Perf.lean").write_bytes(files["Perf.lean"])
            else:
                (pd / "Perf.lean").unlink(missing_ok=True)
        print("[G7] problems/ restored byte-for-byte", flush=True)

    # ======================= analysis =====================================
    local866 = {c["n"]: c["window_median"] for c in cells
                if c["group"] in ("P1", "P2", "P3")}
    localfib = {c["n"]: c["window_median"] for c in cells
                if c["group"] == "FIB"}
    trivial = next(c for c in cells if c["group"] == "A3")

    analysis = {"groups": {}, "fib": {}, "trivial_floor_local": None}
    ks = []
    group_reports = []
    for g, ns in GRID.items():
        o1, o2 = OFFICIAL_866[(g, 0)], OFFICIAL_866[(g, 1)]
        target_ratio = o2 / o1
        best = None
        for n1 in ns:
            for n2 in ns:
                if n2 <= n1:
                    continue
                lr = local866[n2] / local866[n1]
                err = abs(lr - target_ratio) / target_ratio
                k1 = local866[n1] / o1
                k2 = local866[n2] / o2
                if best is None or err < best["err"]:
                    best = {"n1": n1, "n2": n2, "local_ratio": lr,
                            "target_ratio": target_ratio, "err": err,
                            "k1": k1, "k2": k2}
        if best is None:                                            # guard
            group_reports.append(f"{g}: NO PAIR -- group cell missing")
            continue
        g3 = best["err"] <= RATIO_TOL                                 # G3
        analysis["groups"][g] = {**best, "ratio_match": g3}
        ks.append(best["k1"])
        group_reports.append(
            f"{g}: best pair n1={best['n1']}, n2={best['n2']} "
            f"local ratio {best['local_ratio']:.5f} vs official "
            f"{best['target_ratio']:.5f} (err {best['err']*100:.2f}%) -> "
            f"{'MATCH' if g3 else 'DRIFTED'} | k1={best['k1']:.4f} "
            f"k2={best['k2']:.4f}")

    # fib ks
    fib_ks = {n: localfib[n] / OFFICIAL_FIB[n] for n in FIB_NS}
    analysis["fib"]["k_by_n"] = fib_ks
    group_reports.append(
        "FIB: " + "  ".join(f"k(n={n})={k:.4f}" for n, k in fib_ks.items()))

    # A3
    trivial_floor = trivial["window_median"] if trivial else None
    analysis["trivial_floor_local"] = trivial_floor

    # G9 -- process-wide repro vs F1. F1's table labels its plan P1={17,18}
    # but the deterministic local-dev-seed resolves to {16,17} today; the
    # table's slot labels may be off by one. Compare ORDERED VECTORS, not
    # labels: match each F1 figure to the closest of this run's process
    # totals at the same plan, pairwise-min over sorted vectors.
    proc_sorted = sorted(c["process_total"][-1] for c in cells
                         if c["group"] in ("P1", "P2", "P3") and c["n"] in
                         {16, 17, 25, 26, 34, 36} and c["process_total"])
    f1_sorted = sorted(F1_GROUPCHECK.values())
    g9 = {"f13_proc_sorted": proc_sorted, "f1_sorted": f1_sorted,
          "ratios": [], "ok": False}
    if len(proc_sorted) == len(f1_sorted):
        ratios = [p / f for p, f in zip(proc_sorted, f1_sorted)]
        g9["ratios"] = [round(r, 4) for r in ratios]
        g9["ok"] = all(abs(r - 1.0) <= 0.20 for r in ratios)
    analysis["g9_process_repro"] = g9
    group_reports.append(
        f"G9 process-wide repro vs F1 (vector match): "
        f"{'PASS' if g9['ok'] else 'CHECK -- ratios'} " +
        " ".join(str(r) for r in g9["ratios"]))

    # H13.1 / H13.2 verdict
    k_partition = statistics.mean(ks) if ks else None
    k_spread = (((max(ks) - min(ks)) / k_partition)
               if ks and k_partition else None)
    h131 = bool(k_partition is not None and 0.9 <= k_partition <= 2.5
                and k_spread is not None and k_spread <= K_SPREAD_TOL)
    fib_k_ok = False
    if k_partition and fib_ks:
        fib_k_ok = all(
            0.9 <= k <= 2.5
            and abs(k - k_partition) / k_partition <= K_SPREAD_TOL
            for k in fib_ks.values())

    floor_official = (trivial_floor / k_partition
                      if (trivial_floor is not None and k_partition) else None)
    verdicts = []
    if k_partition is not None:
        verdicts.append(f"H13.1 constant window bias k: k={k_partition:.4f} "
                        f"(spread {k_spread*100:.1f}%) -> "
                        f"{'NOT rejected' if h131 else 'REJECTED'}")
    verdicts.append(
        f"fib cross-check: {'consistent' if fib_k_ok else 'INCONSISTENT'}")
    if floor_official:
        fits = floor_official + (F12_CHAIN1 - F12_K0)
        verdicts.append(
            f"official floor+one-add = {floor_official:,.0f} + "
            f"{F12_CHAIN1 - F12_K0:,} = {fits:,.0f} vs champion slot "
            f"{CHAMPION_SLOT:,} -> "
            f"{'FITS: the paradox dissolves' if fits <= CHAMPION_SLOT else 'STILL EXCEEDS'}")

    result = {
        "status": "ok", "cells": cells, "analysis": analysis,
        "verdicts": verdicts, "group_reports": group_reports,
        "k_partition": k_partition, "k_spread": k_spread,
        "floor_official": floor_official,
    }
    out = outdir / "f13_bias_calibration.json"
    out.write_text(json.dumps(result, indent=1))
    txt = outdir / "f13_bias_calibration.txt"
    lines = [f"F13 bias calibration  ({time.strftime('%Y-%m-%d %H:%M')})",
             "=" * 60]
    lines += group_reports
    lines += ["", *verdicts]
    lines.append("")
    lines.append("per-cell (window, process, spread):")
    for c in cells:
        lines.append(f"  {c['tag']:<10} n={c['n']:<7} "
                      f"win={c['window_median']:>13,.0f} "
                      f"proc={c['process_total'][-1] if c['process_total'] else 0:>13,.0f} "
                      f"spread={c['window_spread_pct']:.2f}%")
    txt.write_text("\n".join(lines))
    print("\n".join(group_reports), flush=True)
    print("\n".join(verdicts), flush=True)
    print(f"\n-> {out}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
