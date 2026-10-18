# `ζ` and its partial sums (Titchmarsh, Theorem 4.11), with the constant `11`

Date: 2026-10-18
Task: `M1-ZETA-PARTIAL-SUM` (new, `DONE_STRONG`)
Module: `RiemannHypothesis/ZetaPartialSum.lean` (new; imports `VanDerCorputSumIntegral` and
`Continuation`)

## Claim

```lean
theorem norm_riemannZeta_sub_partialSum_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) {x : ℝ}
    (hx : 0 < x) (hxt : |s.im| ≤ x) :
    ‖riemannZeta s - ∑ n ∈ Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s) + (x : ℂ) ^ (1 - s) / (1 - s)‖
      ≤ 11 * x ^ (-s.re)

theorem norm_riemannZeta_criticalLine_sub_partialSum_le {t x : ℝ} (hx : 0 < x) (hxt : |t| ≤ x) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
        - ∑ n ∈ Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
        + (x : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I) / (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I)‖
      ≤ 11 * x ^ (-(1 / 2 : ℝ))

theorem vdcKappa_half_inv_pi_lt_two : vdcKappa (1 / (2 * Real.pi)) < 2
```

(namespace `RiemannHypothesis.ZetaPartialSum`). In words: for `σ > 0`, `s ≠ 1`, `x > 0` and
`|t| ≤ x`, `ζ(s) = ∑_{n ≤ x} n^(−s) − x^(1−s)/(1 − s) + E` with `|E| ≤ 11 x^(−σ)`. This is
Titchmarsh's Theorem 4.11 with `C = 2π` in his hypothesis `x ≥ C|t|/(2π)`; it holds for every
`σ > 0` (so the `σ ∈ [1/2, 1]` form is included), with an explicit constant and no threshold on
`t`. Mode: a **proof** in this repository.

## The argument (Titchmarsh's)

* `riemannZeta_eq_zetaApprox_of_pos_re` (`Continuation.lean`): for every `M`,
  `ζ(s) = ∑_{n ≤ M} n^(−s) + (M+1)^(1−s)/(s − 1) + ∑' eulerTerm (n + M) s`.
* For `M ≥ ⌊x⌋`, with `m = ⌊x⌋ + 1`, the left side of the claim equals
  `(∑_{m ≤ n ≤ M} n^(−s) − ∫_m^{M+1} u^(−s) du) − ∫_x^m u^(−s) du + tail(M)`
  (`integral_cpow_neg` for `∫_x^{M+1}`; `norm_zeta_sub_partialSum_le_add_tail`).
* `cpow_neg_eq_rpow_mul_e2pi`: `u^(−s) = u^(−σ) e(−(t/2π) log u)`. The phase has derivative
  `−t/(2πu)`, monotone (increasing for `t ≥ 0`, decreasing for `t < 0`) with modulus
  `≤ |t|/(2πu) ≤ 1/(2π)` for `u ≥ m > x ≥ |t|`; the weight `u^(−σ)` is positive and decreasing.
  `M1-VDC-SUM-INTEGRAL` gives `(5/2 + 4π/(2π) + 5κ/2) m^(−σ) = (9/2 + 5κ/2) m^(−σ)`
  (`norm_sum_cpow_sub_integral_le`), `κ = κ(1/(2π)) = 2 − cot(1/2)`.
* `|∫_x^m u^(−s)| ≤ (m − x) x^(−σ) ≤ x^(−σ)`, and `m^(−σ) ≤ x^(−σ)`.
* `tail(M) → 0` (`tendsto_sum_nat_add`, summability of `eulerTerm`), so letting `M → ∞`:
  constant `11/2 + 5κ/2`, and `κ < 2` (`cot(1/2) > 0`) gives `11`.

## Hypothesis hygiene

No new `def … : Prop`; no theorem takes an unproved `Prop` as a hypothesis.
`docs/goal/conditional-theorems.txt` is unchanged.

## Adversarial revalidation: M1-ZETA-PARTIAL-SUM

* *Constants, by hand.* `cot(1/2) = 0.8776/0.4794 = 1.8305`, `κ = 0.1695`,
  `11/2 + 5κ/2 = 5.924 ≤ 11`.
* *Sanity, `s = 2`, `x = 1`.* `ζ(2) − 1 + 1/(−1) = 1.6449 − 2 = −0.355`, `|·| ≤ 11`. `x = 10`:
  `∑_{n>10} n^(−2) − 1/10 = 0.09516 − 0.1 = −0.0048`, against `11/100`.
* *Sanity, critical line, `t = 0`, `x = 1`.* `ζ(1/2) − 1 + 1^(1/2)/(1/2) = −1.4604 − 1 + 2 =
  −0.4604`, against `11`.
* *Load-bearing `|t| ≤ x`.* For fixed `x` the partial sum and `x^(1−s)/(1 − s)` stay bounded as
  `t → ∞`, while `ζ(1/2 + it)` is unbounded; so no bound `A x^(−1/2)` can hold without a
  condition tying `x` to `t`.
* *Load-bearing `σ > 0`, `s ≠ 1`.* `σ > 0` is needed for the representation of
  `Continuation.lean` and for the decrease of the weight; `s = 1` is the pole.
* *Non-vacuity.* The hypotheses hold, for example, for every `s = 1/2 + it` and `x = |t| + 1`.
* *Claim mode.* A proof in this repository. The approximate functional equation is neither used
  nor proved; `AFECriticalLine` remains a recorded statement (`M1-ZETA-CHI-AFE`).
* *Statement pinning.* `scripts/revalidation.lean` writes out the three statements above and
  supplies the repository's declarations; axioms pinned in step 3 of `scripts/audit.sh`.

## Not proved

* The approximate functional equation, and Theorem 4.11 with the smaller constants of the
  literature.

## Commands and gates

See the section of the same name in `2026-10-18-m1-hardy-littlewood-mean-square.md`.
