# M1-SIMPLE-EIGHTY — eighty per cent of the distinct zeroes are simple

Date: 2026-08-21
File: `RiemannHypothesis/EightyPercentSimple.lean`

## Claim

Writing, for an ordinate window, `N` for the nontrivial zeroes of `ζ` counted with multiplicity,
`N_d` for the distinct ones and `Nˢ` for the simple ones:

* `windowCountSimple` — `Nˢ(T₁, T₂)`, the simple nontrivial zeroes of the window;
* `two_mul_ncard_le_ncard_simple_add_finsum` — the general counting inequality: for a finite set
  of points carrying multiplicities `≥ 1`, `2·#S ≤ #{simple points} + ∑ multiplicities`;
* `two_mul_windowCountDistinct_le_add` — its instance for `ζ`: `2·N_d ≤ Nˢ + N`;
* `mtConstant_gt_three_quarters` — the Montgomery–Taylor constant satisfies `c₁* > 3/4`;
* `four_fifths_simple_among_distinct` (and its cumulative form) — for every `ε > 0` and all large
  `T`, `(4/5 − ε)·N_d ≤ Nˢ`;
* `eighty_percent_simple_among_distinct` (and its cumulative form) — the `ε`-free statement
  `0.8·N_d ≤ Nˢ` for all large `T`;
* `tendsto_windowCountDistinct_atTop` and
  `four_fifths_le_liminf_windowCountSimple_div_windowCountDistinct` — the same as a statement
  about the ratio: the denominator tends to infinity, and `liminf Nˢ(0,T)/N_d(0,T) ≥ 4/5`;
* `xiDerivWindowCountSimple`, `two_mul_xiDerivWindowCountDistinct_le_add`,
  `ninety_two_percent_simple_among_distinct_xiDeriv` (and its cumulative form) — the same for the
  zeroes of `ξ′`, where the proved constant is `0.92`;
* `windowCountSimpleL`, `two_mul_windowCountDistinctL_le_add`,
  `eighty_percent_simple_among_distinctL` — the same for `L(·, χ)`, `χ` primitive modulo
  `q > 1`: `0.8·N_{d,χ} ≤ Nˢ_χ` for all large `T`;
* `EightyPercentOnCriticalLine` — the *open* target, `liminf N₀*/N ≥ 4/5`, recorded as a `Prop`
  in the style of `RiemannHypothesis.Partial`: a statement, not a theorem, and unproved here;
  `one_fifth_off_critical_line_of_eightyPercent` derives from it that at most a fifth of the
  zeroes lie off the critical line.

## Proof

Elementary given the distinctness theorems restated in `RiemannHypothesis.Zeta23Bridge` and
`RiemannHypothesis.EightyPercent`. Each window carries finitely many zeroes
(`Zeta23.zerosIn_finite`, `Zeta23.XiPrime.zerosIn_finite`) and each zero has multiplicity at least
one (`Zeta23.zetaSeam.one_le_mult`, `Zeta23.XiPrime.xiDerivZeros₀.one_le_mult`), so splitting the
sum of multiplicities over "simple" and "non-simple" gives `2·N_d ≤ Nˢ + N`. Hence
`Nˢ ≥ (2 − N/N_d)·N_d`, and any lower bound `c` for `N_d/N` yields `Nˢ/N_d ≥ 2 − 1/c`.

Theorem C (`c = 5/6`) gives `4/5` in the limit. Theorem D's constant `(3 − 1/c₁*)/2` is strictly
larger than `5/6` exactly when `c₁* > 3/4`, which is proved here from `x − x³/6 < sin x`
(`Real.sin_gt_sub_cube`) and Mathlib's Taylor bound for `cos` (`Real.cos_bound`) at `x = 1/√2`:
they give `5·sin x > 55√2/24 = 880√2/384` and `3√2·cos x ≤ 879√2/384`, hence
`tan (1/√2) > 3√2/5`, which is equivalent to `c₁* > 3/4`. Instantiating Theorem D at
`ε = (3 − 1/c₁*)/2 − 5/6 > 0` gives `N ≤ (6/5)·N_d` eventually and therefore `Nˢ ≥ 0.8·N_d`,
with no `ε` left over. For `ξ′` the distinctness constant `0.93432` gives `2 − 1/0.93432 > 0.92`
directly.

## Scope — what is *not* claimed

The bounds are `liminf` statements with no effective `T₀`. The denominator is `N_d`, the number of
*distinct* zeroes of the window, not `N`. Nothing here concerns the proportion of zeroes *on the
critical line*: that proportion is `2/3` in this repository
(`two_thirds_on_critical_line`), raising it to `80 %` is an open research problem, and no such
statement is proved anywhere here. The Riemann hypothesis itself is untouched.

## Adversarial revalidation: M1-SIMPLE-EIGHTY

* `lake build RiemannHypothesis.EightyPercentSimple` succeeds; the module contains no `sorry`.
* `#print axioms` for `two_mul_windowCountDistinct_le_add`, `mtConstant_gt_three_quarters`,
  `four_fifths_simple_among_distinct`, `eighty_percent_simple_among_distinct`, its cumulative
  form, both `ξ′` statements and the Dirichlet statement reports exactly
  `[propext, Classical.choice, Quot.sound]`.
* The claims are pinned in `scripts/revalidation.lean`: each statement is written out in full
  there, with the repository's declaration supplied as the proof term, so a weakened or renamed
  declaration stops that file from elaborating.
* The definitions are not vacuous: `windowCountSimple` is cut out of `windowZeros` by
  `zeroMultiplicity ρ = 1`, and the counting inequality `2·N_d ≤ Nˢ + N` relates it to the two
  counting functions already used by the two-thirds results, so a degenerate definition would
  contradict it. The counted sets are finite, so the `ncard`s are honest cardinalities.
* No hypothesis of the form "RH is false", and no unproved hypothesis at all, appears in any of
  the statements; they are unconditional.
