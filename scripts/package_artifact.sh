#!/usr/bin/env bash
# Package the anonymized review artifact.
#
# Produces dist/<ANON>-artifact/ (and a .zip) containing the Lean development and
# the empirical pipeline, with every occurrence of the project name — directory,
# module file, lakefile target, Lean namespace, and prose — renamed to the
# anonymous name used in the paper (\sys = StemFloor).
#
# The renamed tree MUST be re-verified before upload (the namespace rename
# invalidates cached oleans):
#   cd dist/<ANON>-artifact && lake exe cache get && lake build
set -euo pipefail

REAL="FieldStemProof"
ANON="StemFloor"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/dist/${ANON}-artifact"

rm -rf "$OUT"
mkdir -p "$OUT"

# Artifact scope (paper appendix): Lean development + empirical pipeline.
# Excluded: .git, .lake (caches), dist, paper drafts, internal docs, this script.
cp "$ROOT/lakefile.toml" "$ROOT/lake-manifest.json" "$ROOT/lean-toolchain" \
   "$ROOT/README.md" "$ROOT/${REAL}.lean" "$OUT/"
cp -R "$ROOT/$REAL" "$OUT/$REAL"
cp -R "$ROOT/experiment" "$OUT/experiment"

# Rename the module directory and root file, then the name inside every text file.
mv "$OUT/$REAL" "$OUT/$ANON"
mv "$OUT/${REAL}.lean" "$OUT/${ANON}.lean"
find "$OUT" -type f \( -name '*.lean' -o -name '*.toml' -o -name '*.json' \
    -o -name '*.md' -o -name '*.py' -o -name '*.sbatch' \) -print0 |
  xargs -0 sed -i '' -e "s/${REAL}/${ANON}/g" -e "s/fieldStemProof/${ANON}/g"

# Fail loudly if any identifying string survives (any case).
if grep -rni "fieldstemproof" "$OUT" >/dev/null 2>&1; then
  echo "ERROR: leftover occurrences of the project name in the packaged tree:" >&2
  grep -rni "fieldstemproof" "$OUT" >&2
  exit 1
fi

(cd "$ROOT/dist" && zip -qr "${ANON}-artifact.zip" "${ANON}-artifact")
echo "packaged: $OUT (+ .zip)"
echo "REMINDER: re-verify with 'lake exe cache get && lake build' inside the package before upload."
