# M1-SUBCONVEXITY-LOGFREE — the subconvex bound with no logarithm

File: `RiemannHypothesis/SubconvexityLogFree.lean`.
Gates: `lake build RiemannHypothesis.SubconvexityLogFree`, `./scripts/audit.sh`.

## What is proved

Write `e σ = max ((1-σ)/3) (1/2 - 2σ/3)` for the subconvex exponent of
`M1-SUBCONVEXITY-CLOSED-STRIP`, so that `‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t|^(e σ)` on
`0 ≤ σ ≤ 1`, `|t| ≥ 3`.

1. **With an `ε` in the exponent, uniformly in `σ`**
   (`norm_riemannZeta_le_subconvexity_logfree`): for every `ε > 0` there is `C > 0` with

   ```
   ‖ζ(s)‖ ≤ C · |t|^(e σ + ε)      for 0 ≤ σ ≤ 1, |t| ≥ 3,
   ```

   with no logarithm.  The proof is `1 + log|t| ≤ (1 + 1/ε) |t|^ε` (`exists_log_le_rpow`)
   applied to the closed-strip bound.

2. **With no `ε` at all, at a fixed abscissa**
   (`norm_riemannZeta_le_subconvexity_logfree_fixed`): for every fixed `σ ∈ (0,1)` there is
   `C > 0` with

   ```
   ‖ζ(σ + i t)‖ ≤ C · |t|^((1-σ)/2 − min σ (1-σ)/12)      for all |t| ≥ 3.
   ```

   The gap `(1-σ)/2 − e σ` is `σ/6` on the left half of the strip and `(1-σ)/6` on the right
   half, hence at least `min σ (1-σ)/6` (`subconvexity_exponent_le`).  Choosing
   `ε = min σ (1-σ)/12` spends half of that gap on the logarithm and keeps the other half, so
   the exponent stays strictly below the convexity exponent `(1-σ)/2`.

3. **The same in asymptotic form** (`isBigO_riemannZeta_subconvexity_logfree`):
   `ζ(σ + i t) = O(t^((1-σ)/2 − min σ (1-σ)/12))` as `t → ∞`.

This strengthens `M1-GROWTH`'s `norm_riemannZeta_le_convexity_logfree`, which is log-free at
the convexity exponent `(1-σ)/2`: the exponent here is smaller by the fixed positive amount
`min σ (1-σ)/12` at every fixed `σ ∈ (0,1)`.

## Adversarial revalidation: M1-SUBCONVEXITY-LOGFREE

* **Is anything new claimed?**  Only the removal of the logarithm from the subconvex bound.
  The subconvex exponents are exactly those of `M1-SUBCONVEXITY-STRIP` and
  `M1-SUBCONVEXITY-LEFT`; no new analytic input is used, and no exponent is improved.
* **Is the statement vacuous or weaker than what is already there?**  No.  At fixed
  `σ ∈ (0,1)` the exponent `(1-σ)/2 − min σ (1-σ)/12` is strictly smaller than the
  logarithm-free convexity exponent `(1-σ)/2` of `M1-GROWTH`, and both bounds hold for all
  `|t| ≥ 3` with no logarithm, so the new bound is strictly stronger for large `|t|`.
* **Must the constants depend on `ε` and `σ`?**  Yes.  The constant of statement 1 blows up as
  `ε → 0` (it is `C₀ (1 + 1/ε)`), and no `σ`-uniform constant can exist in statement 2, since
  the exponent tends to `0` as `σ → 1` while `ζ(1 + it)` is of size `log t`.
* **Does it depend on anything unproved?**  No.  `#print axioms` on all three results gives
  exactly `propext, Classical.choice, Quot.sound`; the file has no `sorry` and no hypothesis
  that is an unproved `Prop` of this repository.
* **What is still open?**  A logarithm-free bound *at* the subconvex exponent `e σ` itself is
  not proved and cannot be reached this way: absorbing the logarithm costs a positive power,
  and it can only be paid for out of a better exponent than the one being claimed.  The
  bounds remain pointwise, the constants are not explicit, and nothing is deduced about the
  zeroes.
