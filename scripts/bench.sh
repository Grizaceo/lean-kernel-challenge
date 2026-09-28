#!/usr/bin/env bash
# Build+run a throwaway bench module against a problem's Spec, restoring the
# problem dir afterwards. Same contract as verify_candidate.sh: the temp file
# lives INSIDE the problem dir (so `import Spec` resolves) under a unique name,
# and the lakefile is restored on exit.
#
# Usage: scripts/bench.sh <problem> <bench-source.lean> <exe-name> [more-modules...]

set -uo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

PROBLEM="${1:?usage: bench.sh <problem> <bench.lean> <exe> [modules...]}"
BENCH="${2:?}"
EXE="${3:?}"
shift 3
EXTRA=("$@")

PROBLEM_DIR="$REPO/problems/$PROBLEM"
STEM="$(basename "$BENCH" .lean)"
# unique: the candidate's own modules are copied in as <n>_bench and stripped of
# their `import Spec` line by the caller if needed
TAG="bench_$(printf '%s' "$STEM" | tr -c 'A-Za-z0-9_' '_')"
BUILD_LOG="$REPO/.verify/$TAG.log"
mkdir -p "$REPO/.verify"

[ -d "$PROBLEM_DIR" ] || { echo "no problem dir for $PROBLEM" >&2; exit 2; }

LAKEFILE="$PROBLEM_DIR/lakefile.toml"
BACKUP="$(mktemp)"
cp "$LAKEFILE" "$BACKUP"
COPIED=()
python3 - "$LAKEFILE" "$EXE" "${EXTRA[@]}" <<'PY'
import re, sys
path, exe, *extras = sys.argv[1:]
t = open(path).read()
for kind, name in [("lean_lib", e) for e in extras] + [("lean_exe", exe)]:
    t = re.sub(r"\n\[\[%s\]\]\n(?:[^\[]*)name = \"%s\"\n" % (kind, re.escape(name)), "\n", t)
open(path, "w").write(t)
PY
cleanup() {
  cp "$BACKUP" "$LAKEFILE"; rm -f "$BACKUP"
  for f in "${COPIED[@]}"; do rm -f "$PROBLEM_DIR/$f"; done
}
trap cleanup EXIT

# copy bench + any extra modules in under unique names
cp "$BENCH" "$PROBLEM_DIR/${TAG}.lean"; COPIED+=("${TAG}.lean")
i=0
for m in "${EXTRA[@]}"; do
  cp "$m" "$PROBLEM_DIR/${TAG}_x${i}.lean"; COPIED+=("${TAG}_x${i}.lean")
  i=$((i + 1))
done

{
  printf '\n[[lean_lib]]\nname = "%s"\n' "$TAG"
  j=0
  for m in "${EXTRA[@]}"; do
    printf '\n[[lean_lib]]\nname = "%s_x%d"\n' "$TAG" "$j"
    j=$((j + 1))
  done
  printf '\n[[lean_exe]]\nname = "%s"\nroot = "%s"\n' "$EXE" "$TAG"
} >> "$LAKEFILE"

cd "$PROBLEM_DIR"
echo "== building $EXE (log: $BUILD_LOG) =="
lake build "$EXE" > "$BUILD_LOG" 2>&1
rc=$?
if [ "$rc" != "0" ]; then
  tail -30 "$BUILD_LOG"
  echo "BUILD FAILED"
  exit 1
fi
echo "== running $EXE =="
# no pipe: a `| tail` would report tail's status and hide a crash
out=$(./.lake/build/bin/"$EXE" 2>&1); rc=$?
echo "$out"
echo "BENCH_RC=$rc"
exit $rc
