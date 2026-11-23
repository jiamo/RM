#!/usr/bin/env bash
# The analytic half of the alpo.ge proof, compiled in full (minutes on a standard runner):
#   1. tools/build.py: the 31 tree modules behind Deduction.zeroFree_of_rpow_window and
#      Formalism.VW.rh_of_right (they import only Mathlib);
#      and the 87 behind the truncated explicit formula and the zero count in unit windows
#      (explicitFormula_closed, zerosWindow_closed; also Mathlib-only);
#   2. the modules of this repository's RiemannHypothesis library that the bridges import,
#      directly or not (tools/repo_closure.py lists them in dependency order; Mathlib-only),
#      compiled against the tree's Mathlib (both pin Mathlib 0df444a3) into
#      vendor/alpo/lean/.lake/repo-build;
#   3. the bridges: vendor/alpo/AnalyticBridge.lean (WindowBound -> ZetaForm, ZetaStripForm,
#      EtaForm, and the unconditional oscillation theorems) and vendor/alpo/VonKoch.lean
#      (von Koch: ZetaForm -> ChebyshevBoundForm, hence ChebyshevBoundForm <-> ZetaForm).
# Fails unless there is one "depends on axioms" line per `#print axioms` line of the bridges
# and each is [propext, Classical.choice, Quot.sound].
# Prerequisite (this script does not download): (cd vendor/alpo/lean && lake exe cache get)
# Parallelism: JOBS (default 2) lean processes in step 1, one process afterwards.
set -euo pipefail
JOBS="${JOBS:-2}"
case "$JOBS" in (''|*[!0-9]*) echo "JOBS must be a number"; exit 1 ;; esac
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
tree="$repo/vendor/alpo/lean"
bridges=("$repo/vendor/alpo/AnalyticBridge.lean" "$repo/vendor/alpo/VonKoch.lean")

python3 -I "$repo/vendor/alpo/tools/build.py" --root "$tree" --jobs "$JOBS" --target \
  Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow \
  Formalism.GammaFactorNonvanishing.RhOfRight \
  Formalism.PeriodIntegrals.ExplicitFormulaCounts.ExplicitFormula

out="$tree/.lake/repo-build/lib/lean"
lp_tree="$(cd "$tree" && lake env printenv LEAN_PATH)"
export LEAN_PATH="$lp_tree:$out"
# this repository's [leanOptions] (lakefile.toml)
opts=(-DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true
      -Dweak.linter.mathlibStandardSet=true)
mods="$(python3 -I "$repo/vendor/alpo/tools/repo_closure.py" "$repo" "${bridges[@]}")"
echo "[analytic] $(echo "$mods" | wc -l | tr -d ' ') repository modules to check"
# In dependency order; once one module is recompiled, every later one is too.
stale=0
for mod in $mods; do
  rel="${mod//.//}"
  src="$repo/$rel.lean"
  o="$out/$rel.olean"
  mkdir -p "$(dirname "$o")"
  if [ "$stale" = 1 ] || [ ! -f "$o" ] || [ "$src" -nt "$o" ]; then
    echo "[analytic] compiling $mod"
    nice -n 10 lean -j1 -R "$repo" "${opts[@]}" "$src" -o "$o" -i "${o%.olean}.ilean"
    stale=1
  fi
done

status=0
for bridge in "${bridges[@]}"; do
  echo "[analytic] compiling ${bridge#"$repo"/}"
  res="$(nice -n 10 lean -j1 -R "$repo/vendor/alpo" "${opts[@]}" "$bridge" 2>&1)" \
    || { echo "$res"; echo "FAILED: ${bridge#"$repo"/} does not compile"; status=1; continue; }
  echo "$res"
  want="$(grep -c '^#print axioms' "$bridge")"
  n="$(echo "$res" | grep -c "depends on axioms" || true)"
  bad="$(echo "$res" | grep "depends on axioms" | grep -vc "\[propext, Classical.choice, Quot.sound\]" || true)"
  if [ "$n" -eq "$want" ] && [ "$bad" -eq 0 ]; then
    echo "OK: ${bridge#"$repo"/}: $n theorems, standard axioms only"
  else
    echo "FAILED: ${bridge#"$repo"/}: $n axiom reports (expected $want), $bad non-standard"
    status=1
  fi
done
exit "$status"
