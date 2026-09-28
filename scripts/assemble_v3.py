#!/usr/bin/env python3
"""Assemble candidates/ca-rule110-v3/Submission.lean from v2 + the unrolled init.

v3 keeps v2's proven bit-parallel `bstep` kernel and its `step_eq` / `iter_eq`
bridge verbatim, and replaces ONLY the initial-word computation and its proof:

  * v2:  `initBitsAux` — a structurally recursive accumulator, plus ~85 lines
          of simultaneous `testBit` induction to prove it right.
  * v3:  `initBits` — the spec's own `encodeRow` foldr, unrolled to 256 terms
          (no recursion at all), proved right in four lines.

Why the swap is sound and cheaper: measured with scripts/icount.c, the
recursive init costs 2,769M instructions against a ~612M process floor, while
the unrolled one costs 265M — 10.4x less. The local instruction counter also
says the saving is the recursion, not the arithmetic: two variants that only
cheapen the arithmetic (incremental mix argument, 32-bit byte lanes) moved the
total 0.8% and 0.5%.

The splice is mechanical and therefore checkable: lines 1..95 and 200..242 of v2
are copied byte-for-byte, so a diff against v2 shows exactly what was removed.

    python3 scripts/assemble_v3.py
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
V2 = ROOT / "candidates/ca-rule110-v2/Submission.lean"
OUT = ROOT / "candidates/ca-rule110-v3/Submission.lean"

K = 0x9e3779b9
W = 256

# v2 section boundaries, 1-indexed and inclusive.
KEEP_HEAD = (1, 95)    # import Spec .. end of biter
KEEP_TAIL = (200, 242) # bridge to the spec .. end Submission


def bit_term(c: int) -> str:
    """Nat value of cell `c`, in the shape `encodeRow`'s foldr builds."""
    if c == 0:
        return "1"
    if c == 1:
        return "0"
    return "(if (caMix32 (seed + %d * 0x%09x)).testBit 31 then 1 else 0)" % (c + 1, K)


def cell_bool(c: int) -> str:
    """The `List Bool` element the spec's `initRowFor` produces for cell `c`."""
    if c == 0:
        return "true"
    if c == 1:
        return "false"
    return "(caMix32 (seed + %d * 0x%09x)).testBit 31" % (c + 1, K)


def unrolled_block() -> str:
    out = []
    w = out.append
    w("/-! ### Unrolled initial word — v3")
    w("")
    w("The v2 header measured steps 2/4/8 at 358.5M/359.5M/361.4M instructions and")
    w("read the ~357M gap to the leaderboard as a *list* cost. It is not. Measured")
    w("with the local instruction counter (scripts/icount.c), an isolated `caMix32`")
    w("call costs nothing, so 254 of them cannot be the cost either: the recursive")
    w("`initBitsAux` costs 2,769M and the *same value* unrolled costs 265M. The cost")
    w("was Lean's structural Nat recursion — `brecOn`/`Nat.rec` instantiated and")
    w("type-checked by the kernel on every one of 254 iterations. Cheaper arithmetic")
    w("does nothing: an incremental mix argument gives 0.8%, 32-bit byte lanes 0.5%.")
    w("")
    w("So v3 emits the spec's own `encodeRow` foldr with the recursion removed. Cell")
    w("`i` sits at bit `i`; cells 0 and 1 are the spec's fixed head, never mixed. The")
    w("base is `2 * 0 + b255` because `foldr g 0` bottoms out there, not at `b255` —")
    w("matching it literally is what makes the proof syntactic rather than merely")
    w("extensional.")
    w("-/")
    w("")
    w("-- 256 levels of nesting by construction.")
    w("set_option maxRecDepth 1000000")
    w("set_option maxHeartbeats 0")
    w("")
    w("def initBits (seed : Nat) : Nat :=")
    term = "2 * 0 + %s" % bit_term(W - 1)
    for c in range(W - 2, -1, -1):
        term = "2 * (%s) + %s" % (term, bit_term(c))
    line, depth = "  ", 0
    for tok in term.split(" "):
        if len(line) + len(tok) > 74:
            w(line.rstrip())
            line = "  " + "  " * depth
        line += tok + " "
    if line.strip():
        w(line.rstrip())
    w("")
    w("/-! ### Correctness of the unrolled initialization")
    w("")
    w("Four lines, replacing v2's ~85-line simultaneous `testBit` induction. The spec")
    w("builds the row with `(List.range 256).map`, which `rfl` unfolds to a literal")
    w("list; `encodeRow` then reduces over that literal to exactly the nested term")
    w("above. -/")
    w("")
    bterms = ",\n  ".join(cell_bool(c) for c in range(W))
    w("theorem rowLit (seed : Nat) : initRowFor seed = [")
    w("  " + bterms)
    w("] := by rfl")
    w("")
    w("theorem initBits_eq (seed : Nat) :")
    w("    initBits seed = encodeRow (initRowFor seed) := by")
    w("  rw [rowLit seed]")
    w("  simp only [encodeRow, List.foldr_cons, List.foldr_nil, reduceIte]")
    w("  rfl")
    w("")
    return "\n".join(out)


def main() -> int:
    lines = V2.read_text().splitlines()
    head = lines[KEEP_HEAD[0] - 1:KEEP_HEAD[1]]
    tail = lines[KEEP_TAIL[0] - 1:KEEP_TAIL[1]]
    text = "\n".join(head) + "\n\n" + unrolled_block() + "\n" + "\n".join(tail) + "\n"
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text)

    # Report what was dropped, so the diff is auditable rather than asserted.
    dropped = lines[KEEP_HEAD[1]:KEEP_TAIL[0] - 1]
    names = [re.sub(r"\s*:.*", "", ln).strip()
             for ln in dropped if re.match(r"^(theorem|def) ", ln)]
    print(f"wrote {OUT} ({len(text.splitlines())} lines)")
    print(f"kept  v2 lines {KEEP_HEAD[0]}-{KEEP_HEAD[1]} and "
          f"{KEEP_TAIL[0]}-{KEEP_TAIL[1]} byte-for-byte")
    print(f"dropped {len(dropped)} lines of v2 (init + its testBit induction):")
    for n in names:
        print(f"  - {n}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
