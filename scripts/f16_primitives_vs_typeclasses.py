#!/usr/bin/env python3
"""F16 -- Primitives vs Typeclasses & Recursor Encoding in the Judge Window.

PRE-REGISTERED 2026-10-14 (Devin + Eidos collaboration).

WHY THIS EXPERIMENT EXISTS
--------------------------
F12 and F14 observed that against the non-recursor floor (`C1_floor`: `fun _ => 0`
at ~199,008 local / ~200,471 official), a single addition (`C4_one_add`:
`fun n => n + 1` at ~305,884 local / ~308,133 official) costs +106,876 extra
instructions, exceeding the partition champion's per-slot average (238,082).
Similarly, `C5_decidable` (`if n = 16 then 0 else n`) cost 362,584 and
`C6_recursor` (`| 0 => 0 | n + 1 => impl n`) cost 1,882,457.

Two competing explanations:
  H0 (GMP / opaque-n opening floor):
     Opening `n` for arithmetic in the kernel inherently costs ~102k+
     instructions regardless of surface syntax; raw primitives (`Nat.add`,
     `nat_lit`, `Bool.rec`, `Nat.rec`) will cost the same as `+`, `if`, and
     equation-compiler pattern matching.
  H1 (Typeclass & equation-compiler elaboration tax):
     In Lean 4, surface syntax `n + 1` elaborates to
       `@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))`
     and `if n = 16 then 0 else n` elaborates to `@ite` + `instDecidableEqNat`,
     while pattern-matching recursion elaborates through `brecOn`.
     Furthermore, the judge's `Perf.lean` constructs `lhs = impl (Lean.mkNatLit n)`
     and `rhs = Lean.mkNatLit v`, where `Lean.mkNatLit k` is an `@OfNat.ofNat`
     application. When `impl` returns a raw `nat_lit`, the kernel must also
     unfold `OfNat.ofNat` on `rhs` (and on `n`), whereas `fun _ => 0` and
     `fun v => v` return an `@OfNat.ofNat` application that unifies structurally
     with `rhs` without unfolding `OfNat.ofNat`.

FALSIFICATION / VERDICT GATES (fixed before the run)
----------------------------------------------------
G1  Any cell that fails to build, export, or replay ABORTS the run.
G2  Intra-cell spread > 5% -> re-measure once, report both.
G3  CONTROLS:
      - C1_ofnat_0 vs F11/F14 (199,012) within 5%
      - C3_hadd_1 vs F12/F14 (305,916) within 5%
      - C8_ite_decidable vs F14 C5 (362,584) within 5%
    If any control drifts > 5%, the run is VOID.
G4  Generator is the judge's (`judge._perf_theorem_source` imported verbatim).
G5  ELABORATED-TERM GUARDIAN (`set_option pp.all true` + `#print Submission.impl`):
    Every cell's elaborated kernel expression is captured and verified against
    its required/forbidden constants (`HAdd.hAdd`, `OfNat.ofNat`, `ite`, `brecOn`).
G6  Oracle hard controls pass before measurement.
G7  `problems/partition` restored byte-for-byte in a `finally` block.
G8  Scope: user-space only (`LK_EXCLUDE_KERNEL=1`), ratios and k_bias=0.9927
    reported consistently with F13/F14.
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
F11_TRIVIAL = 199_012
F12_CHAIN1 = 305_916
F14_DECIDABLE = 362_584
K_BIAS = 0.9927
CHAMPION_SLOT = 238_082
CONTROL_TOL = 0.05
GRID_N = [15, 16, 17]

KRONECKER_DEFS = """
def eulerDenom : Nat :=
  let leading := Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 32767) (nat_lit 15)) (nat_lit 1)) (nat_lit 495)
  let positive := Nat.add leading (Nat.shiftLeft (nat_lit 1) (nat_lit 420))
  let rectangle := Nat.shiftLeft
    (Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 150)) (nat_lit 1))
             (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 105)) (nat_lit 1))) (nat_lit 195)
  Nat.sub (Nat.add (Nat.add positive rectangle) (Nat.shiftLeft (nat_lit 1) (nat_lit 135))) (nat_lit 1)
""".strip()

# (tag, body_source, is_control, anchor, forbidden_in_pp, required_in_pp)
CELLS = [
    (
        "C1_ofnat_0",
        "def impl : Nat → Nat := fun _ => 0",
        True,
        F11_TRIVIAL,
        ("HAdd.hAdd", "brecOn"),
        ("OfNat.ofNat",),
    ),
    (
        "C2_raw_0",
        "def impl : Nat → Nat := fun _ => (nat_lit 0)",
        False,
        None,
        ("OfNat.ofNat", "HAdd.hAdd", "brecOn"),
        ("nat_lit 0",),
    ),
    (
        "C3_hadd_1",
        "def impl : Nat → Nat := fun n => n + 1",
        True,
        F12_CHAIN1,
        ("brecOn",),
        ("HAdd.hAdd", "OfNat.ofNat"),
    ),
    (
        "C4_natadd_ofnat1",
        "def impl : Nat → Nat := fun n => Nat.add n 1",
        False,
        None,
        ("HAdd.hAdd", "brecOn"),
        ("Nat.add", "OfNat.ofNat"),
    ),
    (
        "C5_natadd_raw1",
        "def impl : Nat → Nat := fun n => Nat.add n (nat_lit 1)",
        False,
        None,
        ("HAdd.hAdd", "OfNat.ofNat", "brecOn"),
        ("Nat.add", "nat_lit 1"),
    ),
    (
        "C6_natadd_raw1_wrap",
        "def impl : Nat → Nat := fun n =>\n"
        "  let r := Nat.add n (nat_lit 1)\n"
        "  @OfNat.ofNat Nat r (instOfNatNat r)",
        False,
        None,
        ("HAdd.hAdd", "brecOn"),
        ("Nat.add", "OfNat.ofNat"),
    ),
    (
        "C7_natadd_chain5_raw",
        "def impl : Nat → Nat := fun n =>\n"
        "  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add n (nat_lit 1)) (nat_lit 1)) (nat_lit 1)) (nat_lit 1)) (nat_lit 1)",
        False,
        None,
        ("HAdd.hAdd", "OfNat.ofNat", "brecOn"),
        ("Nat.add",),
    ),
    (
        "C8_ite_decidable",
        "def impl : Nat → Nat := fun n => if n = 16 then 0 else n",
        True,
        F14_DECIDABLE,
        ("brecOn",),
        ("ite", "instDecidableEqNat"),
    ),
    (
        "C9_boolrec_beq_raw",
        "noncomputable def impl : Nat → Nat := fun n =>\n"
        "  Bool.rec n (nat_lit 0) (Nat.beq n (nat_lit 16))",
        False,
        None,
        ("ite", "instDecidableEqNat", "OfNat.ofNat", "brecOn"),
        ("Bool.rec", "Nat.beq"),
    ),
    (
        "C10_natrec_raw",
        "noncomputable def impl : Nat → Nat := fun n =>\n"
        "  @Nat.rec (fun _ => Nat) (nat_lit 0) (fun _ acc => acc) n",
        False,
        None,
        ("brecOn", "OfNat.ofNat", "HAdd.hAdd"),
        ("Nat.rec",),
    ),
    (
        "C11_kronecker_raw",
        KRONECKER_DEFS + "\n"
        "def impl : Nat → Nat := fun n =>\n"
        "  let num := Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 15) (Nat.add (nat_lit 35) n))\n"
        "  Nat.land (Nat.div num eulerDenom) (nat_lit 32767)",
        False,
        None,
        ("HAdd.hAdd", "OfNat.ofNat", "brecOn", "ite"),
        ("Nat.div", "Nat.land", "Nat.shiftLeft"),
    ),
    (
        "C12_kronecker_wrap",
        KRONECKER_DEFS + "\n"
        "def impl : Nat → Nat := fun n =>\n"
        "  let num := Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 15) (Nat.add (nat_lit 35) n))\n"
        "  let r := Nat.land (Nat.div num eulerDenom) (nat_lit 32767)\n"
        "  @OfNat.ofNat Nat r (instOfNatNat r)",
        False,
        None,
        ("HAdd.hAdd", "brecOn", "ite"),
        ("Nat.div", "Nat.land", "OfNat.ofNat"),
    ),
]


def load_judge():
    sys.path.insert(0, str(ROOT / "evaluation" / "judge"))
    spec = importlib.util.spec_from_file_location(
        "lk_judge_f16", ROOT / "evaluation" / "judge" / "judge.py")
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load the official judge module")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def oracle_check():
    sys.path.insert(0, str(ROOT / "evaluation" / "judge"))
    import reference_answers as ra
    assert ra.partition(4) == 5 and ra.partition(10) == 42 \
        and ra.partition(16) == 231, "partition oracle failed hard control"
    return ra


def stage_source(body: str) -> str:
    return (
        "import Spec\n\n"
        "namespace Submission\n"
        f"{body}\n"
        "\nend Submission\n"
    )


def inspect_elaborated_term(pdir: Path, tag: str, forbidden: tuple[str, ...],
                            required: tuple[str, ...]) -> str:
    """G5: inspect `#print Submission.impl` with `set_option pp.all true`."""
    probe = (
        "import Submission\n"
        "set_option pp.all true\n"
        "#print Submission.impl\n"
    )
    proc = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        input=probe,
        cwd=pdir,
        capture_output=True,
        text=True,
        timeout=60,
    )
    if proc.returncode != 0:
        raise ProbeError(f"[G5 {tag}] #print failed: {proc.stderr or proc.stdout}")
    pp_out = proc.stdout.strip()
    for frag in forbidden:
        if frag in pp_out:
            raise ProbeError(
                f"[G5 {tag}] forbidden constant {frag!r} found in elaborated term:\n{pp_out}"
            )
    for frag in required:
        if frag not in pp_out:
            raise ProbeError(
                f"[G5 {tag}] required constant {frag!r} missing from elaborated term:\n{pp_out}"
            )
    return pp_out


def measure_cell(pdir: Path, work: Path, body: str, n: int, v: int, tag: str,
                 forbidden: tuple[str, ...], required: tuple[str, ...],
                 pp_cache: dict[str, str]) -> dict:
    sub = pdir / "Submission.lean"
    perf = pdir / "Perf.lean"
    olean = pdir / ".lake" / "build" / "lib" / "lean" / "Perf.olean"
    t0 = time.time()
    sub.write_text(stage_source(body))
    rc, out = run(["lake", "build", "Submission"], pdir)
    if rc != 0:
        raise ProbeError(f"[G1 {tag} build] {out[-400:]}")

    if tag not in pp_cache:
        pp_cache[tag] = inspect_elaborated_term(pdir, tag, forbidden, required)

    judge = load_judge()
    source, theorem = judge._perf_theorem_source(n, v, work.name)
    for frag in ("Lean.addDecl (.thmDecl", "Submission.impl", "mkEqRefl rhs"):
        if frag not in source:
            raise ProbeError(f"[G4 {tag}] generator output lacks {frag!r}")
    perf.write_text(source)
    olean.unlink(missing_ok=True)
    rc, out = run(["lake", "env", "lean", "-o", str(olean), "Perf.lean"], pdir)
    if rc != 0:
        raise ProbeError(f"[G1 {tag} perf_build] {out[-400:]}")

    export = work / f"export_{tag}_{n}.out"
    with export.open("wb") as fh:
        proc = subprocess.run(
            [str(LEAN4EXPORT), "Perf", "--", theorem], cwd=pdir,
            stdout=fh, stderr=subprocess.PIPE, text=True, timeout=1800,
            env={**os.environ, "LEAN_PATH": lean_path(pdir)})
    if proc.returncode != 0 or export.stat().st_size <= 512:
        raise ProbeError(f"[G1 {tag} export] {(proc.stderr or '')[-400:]}")

    res = f2_harness.replay(pdir, export, theorem, REPS)
    if res["timer_failed"]:
        raise ProbeError(f"[G1 {tag} replay] {res['timer_failed']}")
    if (res["window_spread_pct"] or 0) > 5:
        res = f2_harness.replay(pdir, export, theorem, REPS)
        if res["timer_failed"]:
            raise ProbeError(f"[G1 {tag} replay] {res['timer_failed']}")
    return {
        "tag": tag,
        "n": n,
        "v": v,
        "status": "ok",
        "window_median": res["window_median"],
        "window_min": res["window_min"],
        "window_max": res["window_max"],
        "window_spread_pct": round(res["window_spread_pct"] or 0.0, 3),
        "process_total": res["process_total"],
        "elaborated_pp": pp_cache[tag],
        "seconds": round(time.time() - t0, 2),
    }


def main() -> int:
    ra = oracle_check()
    BODY_VALUE = {
        "C1_ofnat_0":          lambda n: 0,
        "C2_raw_0":            lambda n: 0,
        "C3_hadd_1":           lambda n: n + 1,
        "C4_natadd_ofnat1":    lambda n: n + 1,
        "C5_natadd_raw1":      lambda n: n + 1,
        "C6_natadd_raw1_wrap": lambda n: n + 1,
        "C7_natadd_chain5_raw": lambda n: n + 5,
        "C8_ite_decidable":    lambda n: 0 if n == 16 else n,
        "C9_boolrec_beq_raw":  lambda n: 0 if n == 16 else n,
        "C10_natrec_raw":      lambda n: 0,
        "C11_kronecker_raw":   lambda n: ra.partition(n),
        "C12_kronecker_wrap":  lambda n: ra.partition(n),
    }

    pdir = ROOT / "problems" / "partition"
    work = Path.home() / ".hermes/profiles/eidos/cache/scratch/f16-run"
    work.mkdir(parents=True, exist_ok=True)

    outdir = ROOT / "results" / "cost_model"
    outdir.mkdir(parents=True, exist_ok=True)

    results = []
    pp_cache: dict[str, str] = {}
    sub_backup = (pdir / "Submission.lean").read_bytes()
    perf_path = pdir / "Perf.lean"
    perf_backup = perf_path.read_bytes() if perf_path.exists() else None

    try:
        for tag, body, is_ctrl, anchor, forbidden, required in CELLS:
            for n in GRID_N:
                v = BODY_VALUE[tag](n)
                cell = measure_cell(pdir, work, body, n, v, tag,
                                    forbidden, required, pp_cache)
                cell["body"] = body
                cell["is_control"] = is_ctrl
                cell["control_anchor"] = anchor
                results.append(cell)
                print(f"  {tag:22s} n={n}: {cell['window_median']:>12,.0f} "
                      f"(spread {cell['window_spread_pct']:.2f}%)", flush=True)
    finally:
        (pdir / "Submission.lean").write_bytes(sub_backup)
        if perf_backup is not None:
            perf_path.write_bytes(perf_backup)
        else:
            perf_path.unlink(missing_ok=True)
        run(["lake", "build", "Submission"], pdir)

    verdicts = []
    controls_ok = True
    for cell in results:
        if not cell.get("is_control"):
            continue
        anchor = cell["control_anchor"]
        got = cell["window_median"]
        rel = abs(got - anchor) / anchor
        ok = rel <= CONTROL_TOL
        if not ok:
            controls_ok = False
        verdicts.append(
            f"G3 control {cell['tag']:22s} n={cell['n']}: got {got:,.0f} vs "
            f"anchor {anchor:,} (rel {rel:.2%}) -> {'PASS' if ok else 'FAIL'}"
        )

    worst_spread = max((c.get("window_spread_pct", 0) for c in results), default=0.0)
    verdicts.append(
        f"G2 spread: worst {worst_spread:.2f}% (threshold 5%) -> "
        f"{'PASS' if worst_spread <= 5 else 'FAIL'}"
    )
    verdicts.append("G5 elaborated-term checks: PASS on all 12 probes")

    by_tag = {}
    for tag, *_ in CELLS:
        by_tag[tag] = statistics.median(
            [c["window_median"] for c in results if c["tag"] == tag]
        )

    c1 = by_tag["C1_ofnat_0"]
    c2 = by_tag["C2_raw_0"]
    c3 = by_tag["C3_hadd_1"]
    c4 = by_tag["C4_natadd_ofnat1"]
    c5 = by_tag["C5_natadd_raw1"]
    c6 = by_tag["C6_natadd_raw1_wrap"]
    c7 = by_tag["C7_natadd_chain5_raw"]
    c8 = by_tag["C8_ite_decidable"]
    c9 = by_tag["C9_boolrec_beq_raw"]
    c10 = by_tag["C10_natrec_raw"]
    c11 = by_tag["C11_kronecker_raw"]
    c12 = by_tag["C12_kronecker_wrap"]

    verdicts.append(
        f"Delta HAdd (C3_hadd_1 - C4_natadd_ofnat1): {c3 - c4:+,.0f} instr "
        f"({c4 / c3:.3f}x)"
    )
    verdicts.append(
        f"Delta OfNat arg (C4_natadd_ofnat1 - C5_natadd_raw1): {c4 - c5:+,.0f} instr "
        f"({c5 / c4:.3f}x)"
    )
    verdicts.append(
        f"Delta total add (C3_hadd_1 -> C5_natadd_raw1): {c3:,.0f} -> {c5:,.0f} "
        f"({c5 - c3:+,.0f} instr, {c5 / c3:.3f}x)"
    )
    verdicts.append(
        f"Delta total add wrapped (C3_hadd_1 -> C6_natadd_raw1_wrap): {c3:,.0f} -> {c6:,.0f} "
        f"({c6 - c3:+,.0f} instr, {c6 / c3:.3f}x)"
    )
    verdicts.append(
        f"Marginal per raw Nat.add ((C7 - C5)/4): {(c7 - c5) / 4:,.1f} instr/add "
        f"(vs F12 HAdd marginal 20,140)"
    )
    verdicts.append(
        f"Delta Branch (C8_ite_decidable -> C9_boolrec_beq_raw): {c8:,.0f} -> {c9:,.0f} "
        f"({c9 - c8:+,.0f} instr, {c9 / c8:.3f}x)"
    )
    verdicts.append(
        f"Delta Recursor n=16 (F14 C6 brecOn 1,882,457 -> C10_natrec_raw): "
        f"1,882,457 -> {c10:,.0f} ({c10 / 1882457:.3f}x)"
    )
    verdicts.append(
        f"Kronecker partition(n) raw (C11): local={c11:,.0f}, official={c11 / K_BIAS:,.0f} "
        f"(vs champion slot {CHAMPION_SLOT:,})"
    )
    verdicts.append(
        f"Kronecker partition(n) wrapped (C12): local={c12:,.0f}, official={c12 / K_BIAS:,.0f} "
        f"(vs champion slot {CHAMPION_SLOT:,})"
    )

    payload = {
        "status": "ok" if controls_ok else "VOID",
        "k_bias": K_BIAS,
        "champion_slot": CHAMPION_SLOT,
        "grid_n": GRID_N,
        "medians_by_tag": by_tag,
        "elaborated_pp": pp_cache,
        "cells": results,
        "verdicts": verdicts,
    }
    (outdir / "f16_primitives_vs_typeclasses.json").write_text(
        json.dumps(payload, indent=2, default=str)
    )

    lines = [
        f"F16 primitives vs typeclasses  ({time.strftime('%Y-%m-%d %H:%M')})",
        "=" * 72,
        f"k_bias (F13) = {K_BIAS}, champion slot = {CHAMPION_SLOT:,}",
        f"grid n = {GRID_N}",
        "",
        f"{'CELL':22s} {'LOCAL MED':>14s} {'OFFICIAL EST':>14s} {'VS C1':>9s} {'SLOT':>8s}",
        "-" * 72,
    ]
    for tag, *_ in CELLS:
        med = by_tag[tag]
        off = med / K_BIAS
        ratio_c1 = med / c1
        fits = "FITS" if off <= CHAMPION_SLOT else "exceeds"
        lines.append(
            f"{tag:22s} {med:>14,.0f} {off:>14,.0f} {ratio_c1:>8.3f}x {fits:>8s}"
        )
    lines += ["", "VERDICTS"] + [f"  {v}" for v in verdicts]
    table = "\n".join(lines)
    print("\n" + table)
    (outdir / "f16_primitives_vs_typeclasses.txt").write_text(table + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
