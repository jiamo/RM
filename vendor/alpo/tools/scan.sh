#!/usr/bin/env bash
# Static scan of vendor/alpo/lean/src for constructs that could bypass the kernel or add
# assumptions.  Fails if any forbidden construct occurs; lists the metaprogramming that
# does occur, for review.  A clean scan is necessary, not sufficient: the build, Verify.lean
# and the kernel replay are what decide.
#
# Usage: bash vendor/alpo/tools/scan.sh
set -euo pipefail
src="$(cd "$(dirname "$0")/.." && pwd)/lean/src"
fail=0
forbidden=(
  '^[[:space:]]*(private |protected )?axiom[[:space:]]'
  '\bsorry\b' '\badmit\b' 'native_decide' 'implemented_by' '@\[extern' '\bunsafe\b'
  '\bopaque\b' 'skipKernelTC' 'ofReduceBool' 'ofReduceNat' 'trustCompiler' '#eval'
  'set_option[[:space:]]+debug\.' 'unsafeCast' 'addDeclWithoutChecking'
)
for pat in "${forbidden[@]}"; do
  n="$( { grep -rlE --include='*.lean' -e "$pat" "$src" || true; } | wc -l | tr -d ' ')"
  printf '%-55s %s files\n' "$pat" "$n"
  if [ "$n" != 0 ]; then
    grep -rnE --include='*.lean' -e "$pat" "$src" | head -20
    fail=1
  fi
done
echo "==> metaprogramming present (for review, not a failure):"
grep -rnE --include='*.lean' -e 'run_cmd|run_elab|run_meta|addDecl|modifyEnv' "$src" | sed "s|$src/||" || true
echo "files defining elab/macro/syntax: $( { grep -rlE --include='*.lean' -e '^[[:space:]]*(local |scoped )?(elab|macro|syntax|macro_rules|elab_rules)[[:space:]]' "$src" || true; } | wc -l | tr -d ' ')"
if [ "$fail" != 0 ]; then echo "SCAN FAILED"; exit 1; fi
echo "scan OK"
