#!/usr/bin/env bash
# Re-run the executable cross-check for a sieve candidate.
#
# Why this script exists: the cross-check must run against the *exact* bytes
# that get uploaded, so it copies the candidate into the problem dir under a
# different module name, adds a temporary lean_exe target, builds, runs, and
# then removes the scaffolding. Everything it touches is restored afterwards.
#
# Usage: scripts/sieve_crosscheck.sh <problem> <candidate-dir> <module> <exe-root>
#   scripts/sieve_crosscheck.sh primecount candidates/primecount-sieve Sieve pccheck
#   scripts/sieve_crosscheck.sh mertens    candidates/mertens-sieve    Mertens mtcheck
#   scripts/sieve_crosscheck.sh partition  candidates/partition-euler  Part   ptcheck
#
# (Named for its origin in the sieve candidates, but it works for any
# candidate whose correctness can be checked by comparing `impl` against the
# Spec on the judge's inputs.)
#
# The cross-check Main.lean lives in <problem>-crosscheck/.

set -euo pipefail

PROBLEM="$1"
CANDIDATE_DIR="$2"
MODULE="$3"
EXE="$4"

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROBLEM_DIR="$REPO/problems/$PROBLEM"
# The cross-check Main.lean lives in the sibling `*-crosscheck` directory,
# named after the *problem*, matching how the candidates are laid out.
CROSSCHECK_DIR="$REPO/candidates/$PROBLEM-crosscheck"

for f in "$CROSSCHECK_DIR/Main.lean"; do
  [ -f "$f" ] || { echo "missing $f" >&2; exit 1; }
done

LAKEFILE="$PROBLEM_DIR/lakefile.toml"
BACKUP="$(mktemp)"
cp "$LAKEFILE" "$BACKUP"

# If the lakefile already declares these targets, drop those blocks first so
# the append below cannot produce a "target already defined" error. Keeps the
# script idempotent even if a previous run was interrupted.
python3 - "$LAKEFILE" "$MODULE" "$EXE" <<'PY'
import re, sys
path, module, exe = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(path).read()
# remove any [[lean_lib]] block naming MODULE and any [[lean_exe]] block naming EXE
for kind, name in (("lean_lib", module), ("lean_exe", exe)):
    text = re.sub(
        r"\n\[\[%s\]\]\n(?:[^\[]*)name = \"%s\"\n" % (kind, re.escape(name)),
        "\n", text)
open(path, "w").write(text)
PY

cleanup() {
  cp "$BACKUP" "$LAKEFILE"
  rm -f "$BACKUP"
  rm -f "$PROBLEM_DIR/$MODULE.lean" "$PROBLEM_DIR/Main.lean"
}
trap cleanup EXIT

# The candidate is copied verbatim; only the namespace name differs, and the
# cross-check opens the candidate's own namespace. This guarantees the bytes
# under test are the bytes to be uploaded.
cp "$CANDIDATE_DIR/Submission.lean" "$PROBLEM_DIR/$MODULE.lean"
cp "$CROSSCHECK_DIR/Main.lean" "$PROBLEM_DIR/Main.lean"

cat >> "$LAKEFILE" <<EOF

[[lean_lib]]
name = "$MODULE"

[[lean_exe]]
name = "$EXE"
root = "Main"
EOF

cd "$PROBLEM_DIR"
echo "== building $EXE =="
lake build "$EXE"
echo "== running $EXE =="
"./.lake/build/bin/$EXE"
