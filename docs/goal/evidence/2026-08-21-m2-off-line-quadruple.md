# Evidence: off-line zeroes come in quadruples, so `4 ∣ N_off(T)` (2026-08-21)

Row: `M2-OFF-LINE-QUADRUPLE` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/OffLineQuadruple.lean`, writing
`nontrivialZeros T = {s | ζ s = 0, 0 < re s < 1, |im s| ≤ T}` and
`offLineNontrivialZeros T = {s ∈ nontrivialZeros T | re s ≠ 1/2}`:

* `criticalReflect` : the reflection `s ↦ 1 - conj s` in the critical line, with
  `criticalReflect_re`, `criticalReflect_im` (it fixes `im` and sends `re s` to `1 - re s`),
  `criticalReflect_criticalReflect` (it is an involution) and `criticalReflect_injective`;
* `conj_mem_nontrivialZeros`, `one_sub_mem_nontrivialZeros`,
  `criticalReflect_mem_nontrivialZeros` : the zeroes of height at most `T` are stable under all
  three symmetries — the height `|im s|` is preserved because `im` is either fixed or negated;
* `offLineQuadruple_distinct` : **for an off-line nontrivial zero `ρ` of height at most `T`, the
  four points `ρ`, `conj ρ`, `1 - ρ`, `1 - conj ρ` are pairwise distinct nontrivial zeroes of
  height at most `T`, none of them on the critical line**;
* `conj_image_upperOffLineNontrivialZeros`,
  `criticalReflect_image_leftUpperNontrivialZeros` : conjugation is a bijection from the upper
  off-line zeroes onto the lower ones, and reflection in the critical line is a bijection from
  the upper-left zeroes onto the upper-right ones;
* `ncard_offLineNontrivialZeros_eq_four_mul` :
  **`N_off(T) = 4 · #{ρ : ζ ρ = 0, 0 < re ρ < 1/2, 0 < im ρ, |im ρ| ≤ T}`**;
* `four_dvd_ncard_offLineNontrivialZeros` : hence **`4 ∣ N_off(T)`** for every `T`;
* `four_le_ncard_offLineNontrivialZeros` : **if one nontrivial zero of height at most `T` lies
  off the critical line, then at least four do.**

## The argument

All the analytic input is already in the repository (`M0-SYMMETRY`, `M2-ZERO-COUNT`,
`M2-ZERO-SYMMETRY-COUNT`); what is new is the combination.

* *The group action.* Conjugation `s ↦ conj s` and the functional-equation reflection
  `s ↦ 1 - s` both preserve the nontrivial zeroes (`conj_mem_nontrivialZeroSet`,
  `one_sub_mem_nontrivialZeroSet`) and both preserve `|im s|`, hence the height condition. Their
  composite `criticalReflect s = 1 - conj s` fixes `im s` and reflects `re s` in `1/2`.
* *Distinctness.* `ρ ≠ conj ρ` and `ρ ≠ 1 - ρ` because no nontrivial zero is real
  (`im_ne_zero_of_mem_nontrivialZeroSet`); `ρ ≠ criticalReflect ρ` because `re ρ ≠ 1/2`. The
  remaining three inequalities are the same two facts read off the real or imaginary part.
* *Counting.* The off-line zeroes of height at most `T` split disjointly into an upper and a
  lower half (no real zeroes), matched bijectively by conjugation; the upper half splits
  disjointly into a left and a right part, matched bijectively by `criticalReflect`. All four
  parts are finite, being subsets of `nontrivialZeros T` (`M2-ZERO-COUNT`), so
  `Set.ncard_union_eq` and `Set.ncard_image_of_injective` give `N_off(T) = 2 · 2 · #(upper left)`.
* *At least four.* Divisibility by four plus positivity of the count when a witness exists.

## Commands run

```
lake build RiemannHypothesis.OffLineQuadruple
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for the results above reports exactly `[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **Nothing about whether `N_off(T)` vanishes.** The Riemann hypothesis says `N_off(T) = 0` for
  every `T`; that is neither proved nor disproved here, and `four_le_ncard_offLineNontrivialZeros`
  is explicitly conditional on the existence of an off-line zero.
* **Multiplicities are ignored.** `ncard` counts points; with multiplicity the divisibility claim
  would additionally need the orders of vanishing at `ρ` and its three companions to agree.
* **No new location information.** The quadruple structure is a symmetry statement; it gives no
  bound on `|re ρ - 1/2|` and no new zero-free region.

## Adversarial revalidation: M2-OFF-LINE-QUADRUPLE

Second, independent pass.

* **Claim mode.** Every result is a `theorem` of this repository and is pinned in full in
  `scripts/revalidation.lean`, including `rfl`-pins of `offLineNontrivialZeros`,
  `leftUpperNontrivialZeros` and `criticalReflect`, so the sets cannot be silently redefined into
  something trivial; `scripts/audit.sh` prints their axioms.
* **Vacuity check.** `ncard_offLineNontrivialZeros_eq_four_mul` is an unconditional equality of
  natural numbers, so it says something even if both sides are `0` — but it is *not* proved by
  showing both sides are `0`: the proof never decides whether off-line zeroes exist, it only uses
  the two bijections. Conversely `four_le_ncard_offLineNontrivialZeros` carries an explicit
  hypothesis exhibiting an off-line zero, and would be false as an unconditional statement if the
  Riemann hypothesis held (then `N_off(T) = 0 < 4`); it is therefore honestly conditional.
* **Is the divisibility a `ncard = 0` degeneracy?** It is possible — indeed the Riemann hypothesis
  asserts exactly that — that `N_off(T) = 0` always, in which case `4 ∣ N_off(T)` is true for a
  trivial reason. The content of the row is the *implication*: any counterexample forces three
  further counterexamples of the same height. That implication is not vacuous as a mathematical
  statement, and the conditional form makes the dependence explicit.
* **Direction check.** `Set.ncard_union_eq` needs disjointness and finiteness of both parts.
  Disjointness of the halves is `0 < im` versus `im < 0`, which uses the absence of real zeroes;
  disjointness of the left and right parts is `re < 1/2` versus `1/2 < re`, which uses `re ≠ 1/2`
  — dropping the off-line hypothesis would make the two parts fail to exhaust the upper zeroes,
  not merely weaken the count. Finiteness comes from `finite_nontrivialZeros`.
* **Is it circular?** No: `M0-SYMMETRY` is proved from the functional equation and the paired eta
  series, `M2-ZERO-COUNT` from a Jensen-type counting lemma, and `M2-ZERO-SYMMETRY-COUNT` from
  those two; none of them uses this row.
* **Sanity check against the literature.** That the nontrivial zeroes off the critical line occur
  in quadruples `ρ, conj ρ, 1-ρ, 1-conj ρ` is the standard textbook remark accompanying the
  functional equation. What is new here is only that it is machine-checked, together with its
  counting consequence, from the repository's own results.
