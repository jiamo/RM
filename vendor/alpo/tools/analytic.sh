#!/usr/bin/env bash
# The analytic half of the alpo.ge proof, compiled in full (minutes on a standard runner):
#   1. tools/build.py: the 31 tree modules behind Deduction.zeroFree_of_rpow_window and
#      Formalism.VW.rh_of_right (they import only Mathlib);
#   2. this repository's RiemannHypothesis.{Defs,Connected,Eta,Zeros,Main}, compiled against the
#      tree's Mathlib (both pin Mathlib 0df444a3), into vendor/alpo/lean/.lake/repo-build;
#   3. vendor/alpo/AnalyticBridge.lean: WindowBound -> ZetaForm, ZetaStripForm, EtaForm.
# Fails unless every "depends on axioms" line is [propext, Classical.choice, Quot.sound].
# Prerequisite (this script does not download): (cd vendor/alpo/lean && lake exe cache get)
# Parallelism: JOBS (default 2) lean processes in step 1, one process afterwards.
set -euo pipefail
JOBS="${JOBS:-2}"
case "$JOBS" in (''|*[!0-9]*) echo "JOBS must be a number"; exit 1 ;; esac
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
tree="$repo/vendor/alpo/lean"

python3 -I "$repo/vendor/alpo/tools/build.py" --root "$tree" --jobs "$JOBS" --target \
  Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow \
  Formalism.GammaFactorNonvanishing.RhOfRight

out="$tree/.lake/repo-build/lib/lean"
mkdir -p "$out/RiemannHypothesis"
lp_tree="$(cd "$tree" && lake env printenv LEAN_PATH)"
export LEAN_PATH="$lp_tree:$out"
# this repository's [leanOptions] (lakefile.toml)
opts=(-DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true
      -Dweak.linter.mathlibStandardSet=true)
stale=0
for m in Defs Connected Eta Zeros Main; do
  src="$repo/RiemannHypothesis/$m.lean"
  o="$out/RiemannHypothesis/$m.olean"
  if [ "$stale" = 1 ] || [ ! -f "$o" ] || [ "$src" -nt "$o" ]; then
    echo "[analytic] compiling RiemannHypothesis.$m"
    nice -n 10 lean -j1 -R "$repo" "${opts[@]}" "$src" -o "$o" -i "${o%.olean}.ilean"
    stale=1
  fi
done

echo "[analytic] compiling vendor/alpo/AnalyticBridge.lean"
res="$(nice -n 10 lean -j1 -R "$repo/vendor/alpo" "${opts[@]}" "$repo/vendor/alpo/AnalyticBridge.lean" 2>&1)" \
  || { echo "$res"; exit 1; }
echo "$res"
n="$(echo "$res" | grep -c "depends on axioms" || true)"
bad="$(echo "$res" | grep "depends on axioms" | grep -vc "\[propext, Classical.choice, Quot.sound\]" || true)"
if [ "$n" -eq 5 ] && [ "$bad" -eq 0 ]; then
  echo "analytic half OK: 5 theorems, standard axioms only"
else
  echo "analytic half FAILED: $n axiom reports, $bad non-standard"; exit 1
fi
