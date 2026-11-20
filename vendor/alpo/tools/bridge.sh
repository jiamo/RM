#!/usr/bin/env bash
# Compile vendor/alpo/Bridge.lean: the tree's `riemannHypothesis` against this repository's
# ZetaForm, ZetaStripForm and EtaForm.  Prerequisites (this script builds neither):
#   * the tree is built:            python3 -I vendor/alpo/tools/build.py --root vendor/alpo/lean
#   * RiemannHypothesis.Main built: lake build RiemannHypothesis.Main   (in the repository root)
# Both use the same pins (Lean v4.33.1, Mathlib 0df444a3), so their .olean files are compatible.
# Fails unless the three theorems depend only on propext, Classical.choice, Quot.sound.
set -euo pipefail
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
tree="$repo/vendor/alpo/lean"
lp_tree="$(cd "$tree" && lake env printenv LEAN_PATH)"
lp_repo="$(cd "$repo" && lake env printenv LEAN_PATH)"
out="$(cd "$tree" && LEAN_PATH="$lp_tree:$lp_repo" nice -n 10 lean -j1 "$repo/vendor/alpo/Bridge.lean" 2>&1)" || { echo "$out"; exit 1; }
echo "$out"
if echo "$out" | grep -q "depends on axioms" && ! echo "$out" | grep "depends on axioms" | grep -vq "\[propext, Classical.choice, Quot.sound\]"; then
  echo "bridge OK"
else
  echo "bridge FAILED: unexpected axioms or output"; exit 1
fi
