#!/usr/bin/env python3
"""F2 harness, hardened. Every failure mode that silently produced a number in
the 2026-09-30 F2 run is now a hard error:

  1. exit codes are captured from the process itself, never through a pipe.
  2. stderr containing `PANIC` / `error:` fails the step. lean4export PANICs
     with **rc=0**, which is how every F2 cell recorded an empty 173-byte
     export as if it had been measured.
  3. the export must be larger than a header and must mention the target
     theorem name.
  4. the timer run must emit KERNEL_TIMING with phase=complete; icount's
     INSTR_TOTAL is meaningless unless the child actually finished the replay.

The point of the instrument: `--count-instructions` makes the official timer
open its OWN counter around the replay window only, which is exactly what the
remote judge scores. Without it we only get a process-wide count whose
~162M startup floor swamps a ~10^4 signal.
"""
from __future__ import annotations

import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from measure import ICOUNT, TIMER, problem_dir, run  # noqa: E402

LEAN4EXPORT = ROOT.parent / "repro/lean4export/.lake/build/bin/lean4export"
PROBLEM = os.environ.get("F2_PROBLEM", "partition")

# The official timer cannot open its counter on this host: `timer_control.c`
# requests user+kernel and perf_event_paranoid=2 denies it. `.verify/
# timer-kernel-local` is a byte-copy of it plus an opt-in
# LK_EXCLUDE_KERNEL=1 that restricts the count to user space -- the same scope
# `scripts/icount.c` already used -- so the in-window number becomes obtainable.
# With the variable unset the binary behaves exactly like the judge's; the
# control run in results/cost_model/README.md records that check.
LOCAL_TIMER = ROOT / ".verify/timer-kernel-local/.lake/build/bin/kernel"
# Prefer the local timer, but only because it can measure. Fall back to the
# judge's binary (wall_time only) rather than crash, so the harness is usable
# on a host with a working PMU and no local build.
TIMER_BIN = LOCAL_TIMER if LOCAL_TIMER.exists() else TIMER
COUNT_INSTRUCTIONS = LOCAL_TIMER.exists()


class ProbeError(RuntimeError):
    pass


def _fail(step: str, detail: str) -> ProbeError:
    return ProbeError(f"[{step}] {detail}")


def check_step(step: str, rc: int, out: str, *, panic_is_fatal: bool = True) -> str:
    """Raise if a subprocess signalled trouble, whatever its exit code.

    The diagnostic is captured as a BLOCK, not as its first matching line.
    Taking only the first line truncated Lean errors mid-sentence -- a real
    `mkAppN` arity error reads "Application type mismatch: The argument" and
    the actual cause ("has type List Expr but is expected to have type
    Array Expr") is on the following lines. That cost three blind iterations
    in F6 before I compiled the probe by hand to see the whole message.
    """
    if panic_is_fatal and re.search(r"PANIC|error:|uncaught exception", out):
        lines = out.splitlines()
        idx = next((i for i, ln in enumerate(lines)
                    if re.search(r"PANIC|error:|uncaught exception", ln)), None)
        if idx is None:
            raise _fail(step, "diagnostic not captured")
        # Lean's error spans from the `error:`/`PANIC` line up to the next blank
        # line; the notes after it (Hints) are noise for the caller.
        block = [lines[idx]]
        for ln in lines[idx + 1:]:
            if not ln.strip():
                break
            block.append(ln)
        text = "\n".join(block).strip()
        raise _fail(step, text[:1200] or "diagnostic not captured")
    if rc != 0:
        raise _fail(step, f"rc={rc}: {out.strip()[-400:]}")
    return out


def lean_path(pdir: Path) -> str:
    artifact_lib = pdir / ".lake" / "build" / "lib" / "lean"
    pkg_libs = sorted(d for d in (pdir / ".lake" / "packages").glob("*/.lake/build/lib/lean")
                      if d.is_dir())
    return os.pathsep.join([str(artifact_lib), *(str(d) for d in pkg_libs),
                            str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.1/lib/lean")])


def probe_source(op: str, a: int, b: int, value: int, theorem: str) -> str:
    """A probe that reproduces the judge's own construction of the target theorem.

    A source-level `theorem check : ... := rfl` does NOT reach the exported
    environment (verified 2026-09-30: the module imports fine but
    `F2Probe.check` is an unknown identifier, so lean4export PANICs with
    `Constant ... not found` while still exiting 0). The judge instead declares
    the theorem through `Lean.addDecl`, which is what we do here: the kernel
    alone then has to reduce `Nat.<op> a b` to `value`, exactly as it does when
    scoring a real submission.

    Operands go in as literals, never as `2^k`: `exponentiation.threshold`
    leaves large powers unevaluated by the elaborator, which is a second way to
    measure a theorem that does not exist.
    """
    if b is None:
        app = f"Lean.mkApp (Lean.mkConst ``{op}) (Lean.mkNatLit {a})"
    else:
        app = (f"Lean.mkApp2 (Lean.mkConst ``{op}) "
               f"(Lean.mkNatLit {a}) (Lean.mkNatLit {b})")
    return f"""import Spec
import Lean
open Lean Meta Elab in
run_meta do
  let lhs := {app}
  let rhs := Lean.mkNatLit {value}
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  Lean.addDecl (.thmDecl {{
    name := `{theorem},
    levelParams := [],
    type := ty,
    value := pf }})
"""


def build_and_export(pdir: Path, source: str, theorem: str, work: Path,
                     module: str = "F2Probe") -> Path:
    """Compile `source` as `module` inside the problem dir and export `theorem`.

    The probe is staged into the problem directory so its `import Spec` resolves
    against the problem's own build, then removed again.
    """
    staged = pdir / f"{module}.lean"
    olean = pdir / ".lake" / "build" / "lib" / "lean" / f"{module}.olean"
    try:
        staged.write_text(source)
        olean.unlink(missing_ok=True)
        rc, out = run(["lake", "env", "lean", "-o", str(olean), f"{module}.lean"], pdir)
        check_step("build", rc, out)
        export = work / "export.out"
        env = {**os.environ, "LEAN_PATH": lean_path(pdir)}
        with export.open("wb") as fh:
            proc = subprocess.run([str(LEAN4EXPORT), module, "--", theorem],
                                  cwd=pdir, env=env, stdout=fh,
                                  stderr=subprocess.PIPE, text=True, timeout=1800)
        # lean4export PANICs with rc=0: the exit code cannot be trusted.
        check_step("export", proc.returncode, proc.stderr or "")
        # The export is JSON-lines with names interned one string at a time, so
        # the theorem's dotted name never appears verbatim in it -- grepping for
        # it is a false test (it rejected a perfectly good 26 kB export). The
        # header alone is 173 B, so the size floor rejects an empty export, and
        # the real semantic check is downstream: the timer must resolve the
        # target and report phase=complete for exactly this theorem name.
        if export.stat().st_size <= 512:
            raise _fail("export", f"export is {export.stat().st_size} B (header only)")
        return export
    finally:
        staged.unlink(missing_ok=True)


def replay(pdir: Path, export: Path, theorem: str, reps: int,
           count_instructions: bool | None = None) -> dict:
    """Replay the target `reps` times and return the judge's own in-window count.

    `instructions` in the KERNEL_TIMING record is measured by the timer around
    `measureReplay` alone -- the exact `target-declaration-replay-v1` boundary
    the remote judge scores. It is the primary number. `INSTR_TOTAL` from icount
    is process-wide (startup + parse included) and is kept only as a sanity
    bound; there is no longer a `--parse-only` window to subtract, because the
    floor was never inside the scored interval to begin with (ERRATA.md) -- it
    was an artefact of counting the whole process.
    """
    if count_instructions is None:
        count_instructions = COUNT_INSTRUCTIONS
    window: list[int] = []
    process: list[int] = []
    timer_failed: str | None = None

    for _ in range(reps):
        cmd = [str(TIMER_BIN)]
        if count_instructions:
            cmd.append("--count-instructions")
        cmd += ["--target", theorem, str(export)]
        wrapped = [str(ICOUNT)] + cmd if ICOUNT.exists() else cmd
        rc, out = run(wrapped, pdir, env_extra={"LK_EXCLUDE_KERNEL": "1"})
        m = re.search(r"INSTR_TOTAL=(\d+)", out)
        if m:
            process.append(int(m.group(1)))
        rec = next((ln for ln in out.splitlines() if ln.startswith("KERNEL_TIMING=")), None)
        if rec is None:
            # The timer never completed the replay. An icount number here is the
            # cost of a process that died, not the cost of the replay.
            timer_failed = next((ln for ln in out.splitlines()
                                 if re.search(r"PANIC|error|exception|absent", ln)),
                                "no KERNEL_TIMING record")
            break
        data = json.loads(rec[len("KERNEL_TIMING="):])
        if data.get("phase") != "complete":
            timer_failed = f"phase={data.get('phase')!r}"
            break
        if data.get("target") != theorem:
            # The timer resolved a different declaration than we asked for. This
            # is how a wrong-but-present export passes silently.
            timer_failed = f"timer scored target={data.get('target')!r}, wanted {theorem!r}"
            break
        if data.get("instructions") is None:
            timer_failed = "timer reported instructions=null (no PMU access)"
            break
        window.append(int(data["instructions"]))

    med = statistics.median(window) if window else None
    return {
        "window_instructions": window,
        "window_median": med,
        "window_min": min(window) if window else None,
        "window_max": max(window) if window else None,
        "window_spread_pct": (100.0 * (max(window) - min(window)) / med) if med else None,
        "process_total": process,
        "timer_failed": timer_failed,
    }
