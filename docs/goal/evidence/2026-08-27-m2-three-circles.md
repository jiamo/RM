# M2-THREE-CIRCLES — Hadamard's three-circles theorem

Date: 2026-08-27
File: `RiemannHypothesis/ThreeCircles.lean`

## Claim

Mathlib has the three-*lines* theorem
(`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`) but not the
three-*circles* theorem.  This file supplies the latter.

```lean
def closedAnnulus (r₁ r₃ : ℝ) : Set ℂ := {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₃}

theorem norm_le_rpow_mul_rpow_of_annulus {f : ℂ → ℂ} {r₁ r₃ a b : ℝ}
    (hr₁ : 0 < r₁) (hr : r₁ < r₃) (hf : AnalyticOnNhd ℂ f (closedAnnulus r₁ r₃))
    (ha : ∀ z : ℂ, ‖z‖ = r₁ → ‖f z‖ ≤ a) (hb : ∀ z : ℂ, ‖z‖ = r₃ → ‖f z‖ ≤ b)
    {z : ℂ} (hz : z ∈ closedAnnulus r₁ r₃) :
    ‖f z‖ ≤ a ^ (1 - (Real.log ‖z‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁))
      * b ^ ((Real.log ‖z‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁))

theorem three_circles {f : ℂ → ℂ} {r₁ r₃ a b : ℝ}
    (hr₁ : 0 < r₁) (hr : r₁ < r₃) (hf : AnalyticOnNhd ℂ f (closedAnnulus r₁ r₃))
    (ha : ∀ z : ℂ, ‖z‖ = r₁ → ‖f z‖ ≤ a) (hb : ∀ z : ℂ, ‖z‖ = r₃ → ‖f z‖ ≤ b)
    {z : ℂ} (hz : z ∈ closedAnnulus r₁ r₃) :
    ‖f z‖ ≤ a ^ (Real.log (r₃ / ‖z‖) / Real.log (r₃ / r₁))
      * b ^ (Real.log (‖z‖ / r₁) / Real.log (r₃ / r₁))
```

In the classical notation, with `M(r)` an upper bound for `‖f‖` on the circle of radius `r`,

    log M(r) ≤ (log(r₃/r) · log M(r₁) + log(r/r₁) · log M(r₃)) / log(r₃/r₁),

i.e. `log M` is a convex function of `log r`.

## Proof

Transport along the exponential map.  Put `l = log r₁`, `u = log r₃` and `g = f ∘ exp`.

* `exp` maps the closed vertical strip `l ≤ re w ≤ u` into the closed annulus, because
  `‖exp w‖ = exp (re w)` (`exp_mem_closedAnnulus`).
* Hence `g` is analytic at every point of the closed strip, being a composition of two functions
  analytic at the relevant points; restricting gives `DifferentiableOn` on the open strip and
  `ContinuousOn` on its closure, since the closed strip is closed and contains the open one.  That
  is the `DiffContOnCl` hypothesis of the three-lines theorem.
* `‖g‖` is bounded on the closed strip because the closed annulus is compact
  (`isCompact_closedAnnulus`: it is closed, being an intersection of two sublevel sets of the
  continuous function `‖·‖`, and bounded, being contained in `closedBall 0 r₃`) and `‖f‖` is
  continuous on it.
* On the line `re w = l` one has `‖exp w‖ = exp l = r₁`, so `‖g w‖ ≤ a`; likewise `‖g w‖ ≤ b` on
  `re w = u`.
* Applying the three-lines theorem at `w = Complex.log z`, whose exponential is `z` and whose real
  part is `log ‖z‖`, gives the interpolation bound.

The classical form is bookkeeping with `Real.log_div`.

## Verification

* `lake build RiemannHypothesis.ThreeCircles` succeeds; the module contains no `sorry`.
* `#print axioms` for `norm_le_rpow_mul_rpow_of_annulus` and `three_circles` reports exactly
  `[propext, Classical.choice, Quot.sound]` (checked in `scripts/audit.sh`).
* Both statements, and the definition of `closedAnnulus`, are pinned in
  `scripts/revalidation.lean`.
* Neither theorem is conditional, so neither appears in `docs/goal/conditional-theorems.txt`.

## Adversarial revalidation: M2-THREE-CIRCLES

* **Is the statement the real theorem, or a weakened version?**  It is the real interpolation
  inequality, at every point of the closed annulus and not only on the middle circle.  The one
  concession is the hypothesis: `f` is assumed analytic on a *neighbourhood* of the closed
  annulus, rather than continuous on the closed annulus and holomorphic in its interior.  That is
  the form in which the theorem is used in practice; the sharper hypothesis would require
  repeating the three-lines argument with a `DiffContOnCl` assumption transported through `exp`,
  and is not done here.
* **Is anything vacuous?**  No.  The hypotheses `0 < r₁ < r₃` are satisfiable, and the conclusion
  is a genuine bound: taking `a = b = M` recovers `‖f z‖ ≤ M`, and taking `f` a monomial `z ↦ z^n`
  shows the exponents are exactly right.
* **Does anything here bear on the Riemann hypothesis?**  No.  The file mentions neither `ζ` nor
  any of the repository's `Prop`s, and no consequence for `ζ` is drawn.  It is recorded as an
  analytic tool for the two open boundaries named in the module docstring — the converse direction
  of Backlund's criterion and the deduction of the Lindelöf hypothesis from the Riemann
  hypothesis — both of which additionally need a Borel–Carathéodory estimate for `log ζ` that is
  not in the repository.
* **Is it already in Mathlib?**  The three-*lines* theorem is
  (`Mathlib/Analysis/Complex/Hadamard.lean`), and it is what this file uses; a search of the
  Mathlib in the pinned manifest found no three-*circles* statement.
