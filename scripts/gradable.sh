#!/usr/bin/env bash
# Is this candidate gradeable at all, before spending a quota slot on it?
#
# `#eval` succeeding is NOT sufficient. The evaluator runs on the VM, but the
# judge builds its perf theorem with `addDecl`, which makes the KERNEL check
# `Submission.impl n = <literal>` definitionally. An implementation that the VM
# evaluates fine can still be stuck in the kernel -- mertens-sieve reduces to
# `match if ((forIn ...))` at n=300 -- and the judge then reports a type
# mismatch that reads exactly like being wrong.
#
# So: pull the expected value with #eval, then demand `rfl` against the
# literal. A failure here is a hard stop, not a warning.
set -uo pipefail
# Absolute, because the script cd's into the problem dir and the EXIT trap must
# still be able to restore the tracked Submission.lean from there. With
# relative paths the trap silently failed to restore and left a candidate staged
# into evaluation/problems/<p>/Submission.lean.
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

PROBLEM="$1"; CAND="$2"; N="${3:?largest judge input}"
TYPE="${4:-Nat}"

PDIR="$ROOT/evaluation/problems/$PROBLEM"
TDIR="$(mktemp -d)"
BACKUP=""
cleanup() {
  if [ -n "$BACKUP" ] && [ -f "$BACKUP" ]; then
    cp -a "$BACKUP" "$PDIR/Submission.lean"
  fi
  rm -f "$PDIR/Probe.lean" "$PDIR/Probe.olean" 2>/dev/null
  rm -rf "$TDIR"
}
trap cleanup EXIT

[ -d "$PDIR" ] || { echo "no such problem: $PROBLEM" >&2; exit 2; }
cp "$PDIR/Submission.lean" "$TDIR/orig.lean"
BACKUP="$TDIR/orig.lean"
cp "$CAND" "$PDIR/Submission.lean"

cd "$PDIR" || exit 2
for lib in Spec Submission; do
  if ! lake build "$lib" >/dev/null 2>&1; then
    echo "UNGRADEABLE  $PROBLEM  $CAND  ($lib does not build)"
    exit 2
  fi
done

# Step 1: the value, from the VM.
cat > Probe.lean <<EOF
import Submission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
#eval show $TYPE from Submission.impl $N
EOF
V="$(lake env lean Probe.lean 2>/dev/null | grep -oE '\-?[0-9]+' | head -1)"
if [ -z "$V" ]; then
  echo "UNGRADEABLE  $PROBLEM  $CAND  (#eval produced no literal at n=$N)"
  exit 1
fi

# Step 2: the same equality, demanded of the kernel via rfl.
cat > Probe.lean <<EOF
import Submission
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
example : Submission.impl $N = ($V : $TYPE) := rfl
EOF
if lake env lean Probe.lean >"$TDIR/out" 2>&1; then
  echo "GRADEABLE    $PROBLEM  $CAND  (n=$N, impl n kernel-defeq to $V)"
  exit 0
fi
echo "UNGRADEABLE  $PROBLEM  $CAND  (n=$N, VM gives $V but the kernel cannot)"
grep -m2 -E 'error' "$TDIR/out" | sed 's/^/               /'
exit 1
