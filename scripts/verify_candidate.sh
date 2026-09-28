#!/usr/bin/env bash
# Full local gate for a Lean Kernel candidate: compile under the problem's real
# options (warningAsError=true) + print the axiom closure of impl_correct.
#
# Usage: scripts/verify_candidate.sh <problem> <source.lean> [<lemma.name>]
#
# Why this shape (all three points cost real cycles on 2026-09-26..27):
#  1. lean_check.sh copies the source to problems/<p>/<basename>.lean and deletes
#     it on exit. Every candidate is called Submission.lean, which collides with
#     the problem's own Submission.lean and once destroyed it. So we copy to a
#     unique basename first.
#  2. `lake env lean` on a loose file does NOT see warningAsError (that lives in
#     the lakefile and is applied by `lake build`), so the compile gate is
#     `lake build` and `-v` is only for reading error text.
#  3. `#print axioms` needs the module to exist; appending it to the candidate
#     itself (rather than a separate importing file) is what actually works.
#
# Exit 0 = compiled clean AND impl_correct depends on no sorryAx.

set -uo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

PROBLEM="${1:?usage: verify_candidate.sh <problem> <source.lean> [<lemma>]}"
SOURCE="${2:?usage: verify_candidate.sh <problem> <source.lean> [<lemma>]}"
LEMMA="${3:-impl_correct}"

PROBLEM_DIR="$REPO/problems/$PROBLEM"
[ -d "$PROBLEM_DIR" ] || { echo "FATAL: no problem dir $PROBLEM_DIR" >&2; exit 2; }
[ -f "$SOURCE" ] || { echo "FATAL: no source $SOURCE" >&2; exit 2; }

# unique basename: problem + candidate stem, sanitized
STEM="$(basename "$(dirname "$SOURCE")")"
SAFE="$(printf '%s_%s' "$PROBLEM" "$STEM" | tr -c 'A-Za-z0-9_' '_')"
VERIFY_DIR="$REPO/.verify"
mkdir -p "$VERIFY_DIR"
VERIFY_SRC="$VERIFY_DIR/${SAFE}.lean"
# the file must live INSIDE the problem dir for `import Spec` to resolve
PROB_SRC="$PROBLEM_DIR/${SAFE}_verify.lean"

# 1. static scan with COMMENTS STRIPPED (a docstring documenting the no-sorry
#    policy is a raw-grep false positive; we need the code-only count)
STRIPPED="$VERIFY_DIR/${SAFE}.stripped"
awk '/\/[-!]/{b=1} /-\//{b=0;next} /^[[:space:]]*--/{next} !b{print}' "$SOURCE" > "$STRIPPED"
BAD="$(grep -cE 'sorry|sorryAx|native_decide|admit|unsafe ' "$STRIPPED" || true)"
echo "### static scan (code only): $BAD suspicious lines"
if [ "$BAD" != "0" ]; then
  echo "--- offending lines ---"
  grep -nE 'sorry|sorryAx|native_decide|admit|unsafe ' "$STRIPPED" | head -20
  echo "GATE: FAIL (static)"
  exit 1
fi

# 2. build under the problem's real options
cp "$SOURCE" "$VERIFY_SRC"
cp "$SOURCE" "$PROB_SRC"
printf '\n#print axioms Submission.%s\n' "$LEMMA" >> "$PROB_SRC"
cleanup() { rm -f "$PROB_SRC" "$VERIFY_SRC" "$STRIPPED"; }
trap cleanup EXIT

BUILD_LOG="$VERIFY_DIR/${SAFE}.build.log"
# `lake build` compiles the problem's own modules under its real options
# (warningAsError lives in the lakefile, so only lake build sees it)
( cd "$PROBLEM_DIR" && lake build ) > "$BUILD_LOG" 2>&1
RC=$?
# then check the candidate in-place with full error text (incl. unsolved goals)
( cd "$PROBLEM_DIR" && lake env lean "${SAFE}_verify.lean" ) >> "$BUILD_LOG" 2>&1
RC2=$?

echo "### build rc=$RC   lean-verify rc=$RC2   (log: $BUILD_LOG)"
if [ "$RC" != "0" ] || [ "$RC2" != "0" ]; then
  echo "--- last 40 log lines ---"
  tail -40 "$BUILD_LOG"
  echo "GATE: FAIL (build)"
  exit 1
fi

# 3. axiom closure
#    real output format: 'Submission.impl_correct' depends on axioms: [propext, Quot.sound]
#    (no quotes around the bracket -- a quoted pattern silently matches nothing)
AX="$(grep -oE 'depends on axioms: \[[^]]*\]' "$BUILD_LOG" | tail -1)"
echo "### axioms $LEMMA: ${AX:-<no closure line found>}"
case "$AX" in
  *sorryAx*) echo "GATE: FAIL (sorryAx in closure)"; exit 1 ;;
  "")        echo "GATE: FAIL (could not read axiom closure)"; exit 1 ;;
  *)         echo "GATE: PASS" ;;
esac
cleanup
exit 0
