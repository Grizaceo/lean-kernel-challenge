#!/usr/bin/env python3
"""Rebuild the local F2 instrument: a copy of the judge's timer that can count.

Why this exists
---------------
`evaluation/judge/timer-kernel/timer_control.c` opens its instruction counter
with `exclude_hv=1` and the default `exclude_kernel=0`, i.e. it asks for
user+kernel. On this host `perf_event_paranoid=2` denies exactly that, so
`kernel --count-instructions` dies with:

    uncaught exception: cannot open kernel timing PMU events: Permission denied

The judge itself is fine -- it runs where the counter opens. The local copy is
what gets patched, so the judge's source tree is never mutated.

Three edits, each asserted to match exactly once. If the judge's source ever
drifts, this script aborts instead of silently producing a differently
instrumented binary:

  1. opt-in `LK_EXCLUDE_KERNEL=1` -> count user space only (the same scope
     `scripts/icount.c` already used). Unset, behaviour is byte-identical to
     the judge's; the control run in results/cost_model/README.md records it.
  2. `#include <stdlib.h>` for getenv.
  3. hand-rolled parse of /proc/self/status VmHWM instead of sscanf. glibc >= 2.38
     routes sscanf through __isoc23_sscanf, which does not resolve against this
     host's libc when the object is linked into the Lean executable.

Usage:  python3 scripts/f2_build_local_timer.py
"""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "evaluation" / "judge" / "timer-kernel"
DST = ROOT / ".verify" / "timer-kernel-local"

EDITS: list[tuple[str, str, str]] = [
    (
        "#include <stdio.h>\n#include <string.h>",
        "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>",
        "add <stdlib.h> for getenv",
    ),
    (
        "    attr.exclude_hv = 1;    /* full user+kernel scope, matching the sealed contract */",
        """    attr.exclude_hv = 1;    /* full user+kernel scope, matching the sealed contract */
    /* LOCAL INSTRUMENTATION (2026-09-30, not part of the official judge).
     * The sealed judge counts user+kernel. On a host with perf_event_paranoid=2
     * that open() is denied outright, so the official timer cannot measure
     * anything here. Setting LK_EXCLUDE_KERNEL=1 counts user-space only --
     * exactly the scope scripts/icount.c already uses -- which makes the
     * in-window instruction count obtainable locally. Unset, this binary
     * behaves identically to the judge's. */
    {
        const char *ek = getenv("LK_EXCLUDE_KERNEL");
        if (ek != NULL && ek[0] == '1') {
            attr.exclude_kernel = 1;
        }
    }""",
        "add the LK_EXCLUDE_KERNEL opt-in",
    ),
    (
        '        if (sscanf(line, "VmHWM: %llu", &peak_kb) == 1) {',
        """        /* Hand-rolled parse of "VmHWM:\\t<digits> kB". glibc >= 2.38 routes
         * sscanf through __isoc23_sscanf, which does not resolve against this
         * host's libc when the object is linked into the Lean executable. */
        if (strncmp(line, "VmHWM:", 6) != 0) {
            continue;
        }
        const char *p = line + 6;
        while (*p == ' ' || *p == '\\t') {
            p++;
        }
        if (*p < '0' || *p > '9') {
            continue;
        }
        while (*p >= '0' && *p <= '9') {
            peak_kb = peak_kb * 10ULL + (unsigned long long)(*p - '0');
            p++;
        }
        {""",
        "replace sscanf on VmHWM",
    ),
]


def main() -> int:
    if not (SRC / "timer_control.c").is_file():
        print(f"judge timer source not found at {SRC}", file=sys.stderr)
        return 1

    text = (SRC / "timer_control.c").read_text()
    for old, new, what in EDITS:
        n = text.count(old)
        if n != 1:
            print(f"ABORT: pattern for '{what}' matched {n} times, expected 1.\n"
                  f"The judge's timer_control.c has drifted; re-read it and update\n"
                  f"this script rather than loosening the check.", file=sys.stderr)
            return 1
        text = text.replace(old, new)

    if "LK_EXCLUDE_KERNEL" not in text:
        print("ABORT: patch did not take", file=sys.stderr)
        return 1

    DST.parent.mkdir(parents=True, exist_ok=True)
    if DST.exists():
        shutil.rmtree(DST)
    shutil.copytree(SRC, DST)
    # The copy inherits a stale object file from the judge's build; it must be
    # recompiled for this host's libc or the link fails on __isoc23_sscanf.
    stale = DST / ".lake" / "build" / "c" / "timer_control.o"
    if stale.exists():
        stale.unlink()
    (DST / "timer_control.c").write_text(text)

    print(f"patched copy at {DST}")
    proc = subprocess.run(["lake", "build", "kernel"], cwd=DST,
                          capture_output=True, text=True, timeout=1800)
    if proc.returncode != 0:
        print(proc.stdout[-2000:])
        print(proc.stderr[-2000:], file=sys.stderr)
        print(f"ABORT: lake build failed (rc={proc.returncode})", file=sys.stderr)
        return 1

    binary = DST / ".lake" / "build" / "bin" / "kernel"
    print(f"built {binary} ({binary.stat().st_size:,} bytes)")
    print("\nControl, required before trusting any number from this binary:")
    print("  without LK_EXCLUDE_KERNEL=1 it must fail exactly like the judge:")
    print("    cannot open kernel timing PMU events: Permission denied")
    print("  with it, it must emit KERNEL_TIMING with a non-null 'instructions'.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
