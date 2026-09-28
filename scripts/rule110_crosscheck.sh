#!/usr/bin/env bash
# Executable cross-check for the ca-rule110 candidate.
#
# This problem's harness predates scripts/sieve_crosscheck.sh and uses its own
# module names (CrossCheck.lean / CrossCheckMain.lean -> CrossCheckMain exe),
# so the generic script's hardcoded `Main.lean` does not apply here. Kept as a
# separate script rather than parameterising the generic one, so the four
# problems that already work through it are not disturbed.
#
# Correctness is checked by comparing `impl` against `caSpecN` on the judge's
# own inputs -- no theorems. That matters here: impl_correct is already proven
# (commit 575674c), so this is an *independent* check of the same claim by a
# different route, not a substitute for the proof.
#
# Usage: scripts/rule110_crosscheck.sh [candidate-dir]   (default: candidates/ca-rule110-v2)

set -uo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CAND="${1:-$REPO/candidates/ca-rule110-v2}"
PROBLEM_DIR="$REPO/problems/ca-rule110"
CC_DIR="$REPO/candidates/ca-rule110-crosscheck"

[ -f "$CAND/Submission.lean" ] || { echo "no candidate at $CAND/Submission.lean" >&2; exit 2; }
[ -f "$CC_DIR/CrossCheckMain.lean" ] || { echo "missing harness" >&2; exit 2; }

LAKEFILE="$PROBLEM_DIR/lakefile.toml"
BACKUP="$(mktemp)"
cp "$LAKEFILE" "$BACKUP"
# drop any pre-existing entries so re-runs are idempotent after an interrupted run
python3 - "$LAKEFILE" <<'PY'
import re, sys
p = sys.argv[1]
t = open(p).read()
for kind, name in (("lean_lib", "Rule110V2"), ("lean_lib", "CrossCheck"), ("lean_exe", "r110check")):
    t = re.sub(r"\n\[\[%s\]\]\n(?:[^\[]*)name = \"%s\"\n" % (kind, name), "\n", t)
open(p, "w").write(t)
PY
cleanup() {
  cp "$BACKUP" "$LAKEFILE"; rm -f "$BACKUP"
  rm -f "$PROBLEM_DIR/Rule110V2.lean" "$PROBLEM_DIR/CrossCheckMain.lean" "$PROBLEM_DIR/CrossCheck.lean"
}
trap cleanup EXIT

cp "$CAND/Submission.lean" "$PROBLEM_DIR/Rule110V2.lean"
# CrossCheckMain imports CrossCheck, and CrossCheck.lean wraps the candidate's
# impl; both are needed for the exe to link (the linker errors on
# lp_track2ca_CrossCheck_* otherwise)
cp "$CC_DIR/CrossCheck.lean" "$PROBLEM_DIR/CrossCheck.lean"
cp "$CC_DIR/CrossCheckMain.lean" "$PROBLEM_DIR/CrossCheckMain.lean"
printf '\n[[lean_lib]]\nname = "Rule110V2"\n\n[[lean_lib]]\nname = "CrossCheck"\n\n[[lean_exe]]\nname = "r110check"\nroot = "CrossCheckMain"\n' >> "$LAKEFILE"

cd "$PROBLEM_DIR"
echo "== building r110check =="
lake build r110check || { echo "BUILD FAILED"; exit 1; }
echo "== running r110check =="
# capture WITHOUT a pipe: `bin | tail` would report tail's exit code and hide
# the IO.Process.exit 1 that the harness uses to signal a mismatch
out=$(./.lake/build/bin/r110check 2>&1); rc=$?
echo "$out"
echo "CROSSCHECK_RC=$rc"
exit $rc
