#!/usr/bin/env bash
# Build a candidate file against a problem's Spec, without touching the repo.
#
# Usage: scripts/lean_check.sh <problem> <source.lean> [-v]
#   <problem>   e.g. ca-rule110      -> problems/ca-rule110
#   <source>    path to the .lean to compile (namespace must match the spec)
#   -v          run `lean` directly so full error text (incl. unsolved goals) shows
#
# The file is copied in as a temporary <Lib>.lean, a lean_lib entry is appended
# to the problem's lakefile, and both are reverted on exit (trap). The problem
# dir is left byte-identical, so this is safe to run repeatedly.
#
# Exit 0 = compiles with warningAsError=true and zero `sorry`.

set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

PROBLEM="${1:?usage: lean_check.sh <problem> <source.lean> [-v]}"
SOURCE="${2:?usage: lean_check.sh <problem> <source.lean> [-v]}"
VERBOSE="${3:-}"

PROBLEM_DIR="$REPO/problems/$PROBLEM"
[ -d "$PROBLEM_DIR" ] || { echo "no such problem: $PROBLEM" >&2; exit 2; }
[ -f "$SOURCE" ] || { echo "no such source: $SOURCE" >&2; exit 2; }

# The copy-in lands as <Lib>.lean inside the problem dir. If that name already
# exists there it is a problem file (Spec.lean, Submission.lean, ...) and the
# cleanup below would DELETE it -- which silently destroyed the official
# problems/ca-rule110/Submission.lean once. Refuse instead of clobbering.
LIB="$(basename "$SOURCE" .lean)"
if [ -e "$PROBLEM_DIR/$LIB.lean" ]; then
  echo "refusing: $PROBLEM_DIR/$LIB.lean already exists (would be clobbered then deleted)" >&2
  exit 2
fi

LAKEFILE="$PROBLEM_DIR/lakefile.toml"
BACKUP="$(mktemp)"
cp "$LAKEFILE" "$BACKUP"
cleanup() {
  cp "$BACKUP" "$LAKEFILE"
  rm -f "$BACKUP" "$PROBLEM_DIR/$LIB.lean"
}
trap cleanup EXIT

# drop any pre-existing entry for this lib so re-runs are idempotent
python3 - "$LAKEFILE" "$LIB" <<'PY'
import re, sys
p, lib = sys.argv[1], sys.argv[2]
t = open(p).read()
t = re.sub(r"\n\[\[lean_lib\]\]\n(?:[^\[]*)name = \"%s\"\n" % re.escape(lib), "\n", t)
open(p, "w").write(t)
PY

cp "$SOURCE" "$PROBLEM_DIR/$LIB.lean"
printf '\n[[lean_lib]]\nname = "%s"\n' "$LIB" >> "$LAKEFILE"

cd "$PROBLEM_DIR"
if [ "$VERBOSE" = "-v" ]; then
  lake env lean "$LIB.lean"
else
  lake build "$LIB"
fi
