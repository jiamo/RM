# M1-SUBCONVEXITY-STRIP — the exponent `(1-σ)/3` inside the critical strip

File: `RiemannHypothesis/SubconvexityStrip.lean`.
Gates: `lake build RiemannHypothesis.SubconvexityStrip`, `./scripts/audit.sh`.

## What is proved

Unconditionally, for `1/2 ≤ σ ≤ 1` and `t ≥ 10⁹`,

```
‖ζ(σ + i t)‖ ≤ 400 · t^((1-σ)/3) · (log t + 1)
```

(`norm_riemannZeta_strip_le`).  For `σ > 1/2` the exponent `(1-σ)/3` is smaller than the
convexity exponent `(1-σ)/2` of `RiemannHypothesis/Convexity.lean`, and the saving is a fixed
power of `t`, so the bound is a genuine improvement on the convexity bound for large `t`
despite the logarithm.  At `σ = 1/2` the exponent is `1/6`, the bound of
`M1-SUBCONVEXITY-UNCONDITIONAL` with a worse constant.

## Why it costs nothing beyond the critical line

The block estimates of `M1-SUBCONVEXITY-UNCONDITIONAL` are statements about the *phase*
`−(t/2π) log x` only, so they do not depend on `σ`: `norm_sum_e2pi_logPhase_block_le_all`
is reused verbatim.  What changes with `σ` is the weight Abel summation carries:

* `cpow_strip_eq` splits `x^(-σ-it) = x^(-σ) · e(−(t/2π) log x)`;
* `norm_sum_block_strip_le` runs the same Abel summation with the nonincreasing weight
  `n^(-σ)`, so a block starting at `M ≥ 30u²` (with `u = t^(1/6)`) contributes
  `M^(-σ) · 60 √M u = 60 M^(1/2-σ) u ≤ 60 (u²)^(1/2-σ) u = 60 u^(2-2σ)`, the last inequality
  because `1/2 − σ ≤ 0` and `M ≥ u²`;
* the trivial bound for the base of the dyadic induction is
  `∑_{n ≤ K} n^(-σ) ≤ K^(1-σ)(1 + log K)` (`sum_Icc_rpow_neg_le`, from `n^(-σ) = n^(1-σ)/n`
  and the harmonic bound), which for `K ≤ 60u²` is again `O(u^(2-2σ) log)`;
* the dyadic induction (`norm_zetaSum_strip_le`) therefore gives
  `‖∑_{n ≤ N} n^(-σ-it)‖ ≤ 120 u^(2-2σ)(log₂ N + 1)` for `N ≤ 2u¹²`;
* the Euler–Maclaurin error (`norm_riemannZeta_sub_zetaSum_strip_le`) is again at most `10`:
  the polar term is `(N+1)^(1-σ)/|s-1| ≤ (N+1)^(1/2)/t ≤ 2` because `1-σ ≤ 1/2`, and the tail
  is bounded by the same `(n+1)^(-3/2)` estimate because `1 + σ ≥ 3/2`.

Finally `u^(2-2σ) = t^((1-σ)/3)`.

## Hypothesis hygiene

No hypothesis: every theorem of the file is unconditional and none takes an unproved `Prop`
of this repository as an argument, so `docs/goal/conditional-theorems.txt` is unchanged.

## Adversarial revalidation: M1-SUBCONVEXITY-STRIP

* **Is the statement vacuous?**  No: `1/2 ≤ σ ≤ 1` and `t ≥ 10⁹` are satisfiable, and the
  exponent is a real power (`Real.rpow`).
* **Is it really better than convexity?**  For fixed `σ > 1/2` the ratio to the convexity
  bound `t^((1-σ)/2)` is `t^(-(1-σ)/6) log t → 0`, so yes, for large `t`; for `σ = 1` both
  exponents are `0` and the statement is only the classical `O(log t)` bound with a worse
  constant, and near `σ = 1/2` the crossover happens very late because of the constant `400`.
* **Does it depend on anything unproved?**
  `#print axioms RiemannHypothesis.SubconvexityStrip.norm_riemannZeta_strip_le` gives exactly
  `propext, Classical.choice, Quot.sound`; the file has no `sorry`.
* **What is still open?**  Uniformity is only in `σ ∈ [1/2, 1]` and `t ≥ 10⁹`; the constants
  are not optimized, the logarithm is not removed, and no consequence for the zeroes (a
  density estimate, a zero-free region) is drawn — those need mean values, not pointwise
  bounds.  The exponent `(1-σ)/3` is what the exponent pair `(1/6, 2/3)` gives; the
  Bombieri–Iwaniec, Huxley and Bourgain exponents, and the Lindelöf hypothesis, remain out of
  reach.
