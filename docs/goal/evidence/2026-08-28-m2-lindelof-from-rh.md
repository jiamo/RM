# M2-LINDELOF-FROM-RH — the Lindelöf bound away from the critical line, under the Riemann hypothesis

Date: 2026-08-28
File: `RiemannHypothesis/LindelofFromRH.lean`

## Claim

Littlewood's theorem is that the Riemann hypothesis implies the Lindelöf hypothesis.  This file
proves the part of it that does not need the radii of the three circles to shrink with the height:
for every fixed `δ > 0`, the Riemann hypothesis gives `ζ(σ + i t) = O_ε(t^ε)` uniformly for
`σ ≥ 1/2 + δ`.

```lean
theorem norm_riemannZeta_le_exp_of_zetaStripForm (h : ZetaStripForm) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {s : ℂ} (hre : 1 / 2 + δ ≤ s.re) (hre2 : s.re ≤ 5 / 2)
    (ht : 100 ≤ s.im) :
    ‖riemannZeta s‖
      ≤ 3 * Real.exp (4 * (60 * Real.log s.im / δ)
          ^ (Real.log (5 - 2 * δ) / Real.log (5 - δ)))

theorem exists_bound_riemannZeta_of_zetaStripForm (h : ZetaStripForm) {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → T₀ ≤ s.im →
      ‖riemannZeta s‖ ≤ C * s.im ^ ε

theorem exists_bound_riemannZeta_abs_im_of_zetaStripForm (h : ZetaStripForm) {δ ε : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → T₀ ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ ε
```

The last is the two-sided form, obtained from the conjugation symmetry `ζ(conj s) = conj (ζ s)`.

All three theorems take the Riemann hypothesis (`ZetaStripForm`) as a hypothesis and are therefore
listed in `docs/goal/conditional-theorems.txt`.

## Proof

Under the Riemann hypothesis `ζ` has no zero with `re s > 1/2`, so the entire function
`zetaPoleFree s = (s − 1) ζ(s)` has none either, and `exists_holomorphic_log_halfPlane` supplies a
holomorphic branch `F` of its logarithm on `re s > 1/2` (`exists_logBranch_of_zetaStripForm`).  Fix
a height `t ≥ 100`, put `s₀ = 3 + i t`, and let `G z = F(s₀ + z) − F(s₀)`, so `G 0 = 0` and
`re G z = log ‖zetaPoleFree (s₀ + z)‖ − log ‖zetaPoleFree s₀‖` — the branch constant cancels.

* `‖zetaPoleFree s₀‖ ≥ t/2`, because `‖ζ(3 + i t)‖ ≥ 1/2` (`half_le_norm_riemannZeta_of_three_le_re`)
  and `‖2 + i t‖ ≥ t`; and `‖zetaPoleFree s₀‖ ≤ 2(t + 3)`, because `‖ζ‖ ≤ 2` for `re s ≥ 2`.
* On the disc `‖z‖ < 1` one has `re s ≥ 2`, so `re G z ≤ log(4(t + 3)/t) ≤ 2 log 2 + 3/t < 2`.
  Borel–Carathéodory (`Complex.borelCaratheodory_zero`, `M = 2`, `R = 1`) gives `‖G‖ ≤ 4` on
  `‖z‖ ≤ 1/2`.
* On the disc `‖z‖ < 5/2` one has `re s > 1/2` and `im s ≥ 3`, so `‖ζ(s)‖ ≤ 16‖s‖² + 2`
  (`norm_riemannZeta_le_sq`) and `‖zetaPoleFree s‖ ≤ (t + 7)(16(t + 6)² + 2) ≤ (t/2) t⁶`; dividing
  by the lower bound `t/2` gives `re G z ≤ 6 log t`.  Borel–Carathéodory (`M = 6 log t`, `R = 5/2`)
  gives `‖G‖ ≤ 60 log t / δ` on `‖z‖ ≤ 5/2 − δ/2`.
* Hadamard's three circles (`three_circles`) with radii `1/2` and `5/2 − δ/2` interpolates: on the
  annulus `1/2 ≤ ‖z‖ ≤ 5/2 − δ`,
  `‖G z‖ ≤ 4 · (60 log t/δ)^{λ₀}` with `λ₀ = log(5 − 2δ)/log(5 − δ) < 1`.
* At `z = σ − 3`, exponentiating and dividing by `‖s − 1‖ ≥ t` gives the first theorem; since
  `λ₀ < 1`, the exponent `4(60/δ)^{λ₀} (log t)^{λ₀}` is eventually below `ε log t`, which gives the
  second with `C = 3` and `T₀ = max 100 (exp ((A/ε + 1)^{1/(1 − λ₀)}))`, `A = 4(60/δ)^{λ₀}`.  For
  `re s > 5/2` the Dirichlet series bound `‖ζ‖ ≤ 2` suffices.

## Verification

* `lake build RiemannHypothesis.LindelofFromRH` succeeds; the module contains no `sorry`, and the
  module is imported by the root `RiemannHypothesis.lean`.
* `./scripts/audit.sh` prints `OK`.
* All three statements are pinned in `scripts/revalidation.lean`.
* They appear in `docs/goal/conditional-theorems.txt`, since they assume `ZetaStripForm`.

## Adversarial revalidation: M2-LINDELOF-FROM-RH

* **Is the Lindelöf hypothesis proved?**  No.  `LindelofHypothesis` of
  `RiemannHypothesis/LindelofDensity.lean` asks for the bound uniformly for `re s ≥ 1/2`, and the
  critical line itself is *not* covered here: as `δ → 0` the interpolation exponent
  `λ₀ = log(5 − 2δ)/log(5 − δ)` tends to `1` and the threshold `T₀` tends to infinity.  Reaching
  the line is Littlewood's `log ζ(1/2 + i t) = O(log t / log log t)`, which needs the radii to
  shrink with `t`, and is not formalized.
* **Is the statement vacuous or conditional in a hidden way?**  It is openly conditional: the
  Riemann hypothesis appears as the explicit hypothesis `ZetaStripForm`, which this repository does
  not prove, and the machine-checked manifest of conditional theorems records that.  Nothing
  unconditional about `ζ` is claimed, and no term of type `ZetaForm` is produced.
* **Is the bound trivial?**  No.  For `1/2 + δ ≤ re s ≤ 1` the unconditional bounds available in
  the repository are the convexity bounds `O(|t|^{(1 − σ)/2 + ε})` (M1-CONVEXITY) and
  `O((1 + log|t|)|t|^{(1 − σ)/2})` (M1-CONVEXITY-LOG), which are genuine powers of `t`; the bound
  proved here is `O_ε(t^ε)` for every `ε > 0`, and it is the Riemann hypothesis that supplies it.
* **Are the constants meaningful?**  They are explicit but not optimized: `100`, `3`, `4`, `60` and
  the interpolation radii `1/2`, `5/2` are chosen for convenience of the numerical inequalities.
