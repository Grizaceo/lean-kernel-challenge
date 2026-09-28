#!/usr/bin/env bash
# Build candidates/ca-rule110-v2/Work.lean against problems/ca-rule110's Spec.
#
# Work.lean is a scratch copy of the candidate with the same namespace and the
# same definitions; the three anchoring lemmas are the only things being proved.
# It is never uploaded: only Submission.lean goes to the judge.
#
# Usage: scripts/v2_work.sh [goal-filter]   (no args = full build)

set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROBLEM_DIR="$REPO/problems/ca-rule110"
WORK="$REPO/candidates/ca-rule110-v2/Work.lean"

LAKEFILE="$PROBLEM_DIR/lakefile.toml"
BACKUP="$(mktemp)"
cp "$LAKEFILE" "$BACKUP"
cleanup() { cp "$BACKUP" "$LAKEFILE"; rm -f "$BACKUP" "$PROBLEM_DIR/Work.lean"; }
trap cleanup EXIT

# drop any pre-existing Work block so this is idempotent
python3 - "$LAKEFILE" <<'PY'
import re, sys
p = sys.argv[1]
t = open(p).read()
t = re.sub(r"\n\[\[lean_lib\]\]\n(?:[^\[]*)name = \"Work\"\n", "\n", t)
open(p, "w").write(t)
PY

cp "$WORK" "$PROBLEM_DIR/Work.lean"
cat >> "$LAKEFILE" <<'EOF'

[[lean_lib]]
name = "Work"
EOF

cd "$PROBLEM_DIR"
if [ "${1:-}" = "-v" ]; then
  # verbose: run lean directly so full error text (incl. unsolved goals) shows
  lake env lean Work.lean
else
  lake build Work
fi
