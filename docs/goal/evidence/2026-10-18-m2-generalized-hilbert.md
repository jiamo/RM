# Montgomery and Vaughan's generalized Hilbert inequality, with the constant `π/δ`

Date: 2026-10-18
Task: `M2-HILBERT-INEQUALITY` (now `DONE_STRONG`)
Module: `RiemannHypothesis/MontgomeryVaughan.lean` (new; imports `HilbertInequality` and
`MeanValueWellSpaced`)

## Claim

`RiemannHypothesis.MontgomeryVaughan.generalizedHilbertInequality` proves the repository's
statement `RiemannHypothesis.Hilbert.GeneralizedHilbertInequality`, whose definition in
`RiemannHypothesis/HilbertInequality.lean` is **unchanged**:

```lean
def GeneralizedHilbertInequality : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (x : Fin n → ℂ) (δ : ℝ), 0 < δ →
    (∀ r s : Fin n, r ≠ s → δ ≤ |lam r - lam s|) →
      ‖∑ r, ∑ s ∈ Finset.univ.erase r, x r * (starRingEnd ℂ) (x s) /
          ((lam r : ℂ) - (lam s : ℂ))‖
        ≤ Real.pi / δ * ∑ r, ‖x r‖ ^ 2

theorem generalizedHilbertInequality : Hilbert.GeneralizedHilbertInequality
```

That is: for real frequencies `λ_1, …, λ_n` with `|λ_r − λ_s| ≥ δ > 0` for `r ≠ s` and any
complex `x_r`, `|∑_{r≠s} x_r conj(x_s)/(λ_r − λ_s)| ≤ (π/δ) ∑ |x_r|²`. The constant is exactly
`π/δ`. Mode: a **proof**, in this repository, of a classical theorem (Montgomery–Vaughan,
J. London Math. Soc. (2) 8 (1974), 73–82). Mathlib supplies the spectral theorem for
symmetric operators (`LinearMap.IsSymmetric.eigenvectorBasis`) and Basel's sum
(`hasSum_zeta_two`). It does not supply the inequality.

`#print axioms RiemannHypothesis.MontgomeryVaughan.generalizedHilbertInequality`:
`[propext, Classical.choice, Quot.sound]`.

## The argument, declaration by declaration

Write `A r s = 1/(λ_r − λ_s)` (`kernel`; Lean's `1/0 = 0` makes the diagonal zero).

* `kernel_swap`, `kernel_mul_kernel`, `sum_kernel_mul_kernel`. The partial-fraction identity
  `1/((λ_r−λ_s)(λ_r−λ_t)) = (1/(λ_s−λ_t))(1/(λ_r−λ_s) − 1/(λ_r−λ_t))` holds for
  `r ∉ {s, t}`. With its two correction terms at `r = s` and `r = t`, summing over all `r` gives,
  for **all** `s, t`:
  `∑_r A r s · A r t = A s t (a_s − a_t) + 2 A s t² + [s = t] b_s`,
  where `a_s = ∑_r A r s` (`colSum`) and `b_s = ∑_r A r s²` (`colSq`).
* `eigen_bound`. Let `A v = iμ v` with `μ` real. Then `‖A v‖² = μ²‖v‖²`, and the expansion of
  `‖A v‖²` through the identity above contains the two terms
  `∑_{s,t} v_s conj(v_t) A s t a_s` and `∑_{s,t} v_s conj(v_t) A s t a_t`.
  Because `v` is an eigenvector, `∑_t A s t conj(v_t) = conj((Av)_s) = −iμ conj(v_s)` and
  `∑_s A s t v_s = −(Av)_t = −iμ v_t`. So both terms equal `−iμ ∑_s a_s |v_s|²`, and they
  cancel. **This is the step the circulated "elementary" proof gets wrong: it holds for
  eigenvectors, not for all `x`.** What remains is
  `μ² ‖v‖² = ∑_s b_s |v_s|² + 2 Re ∑_{s,t} A s t² v_s conj(v_t)`.
  Then `|v_s v_t| ≤ (|v_s|² + |v_t|²)/2` and the symmetry `A s t² = A t s²` give
  `μ²‖v‖² ≤ 3 ∑_s b_s |v_s|²`.
* `colSq_le`. `b_s = ∑_{r≠s} (λ_r − λ_s)^{-2} ≤ π²/(3δ²)`. Let
  `g(r) = ⌊|λ_s − λ_r|/δ⌋ ≥ 1` for `r ≠ s`. Then `(λ_r − λ_s)^{-2} ≤ (g(r) δ)^{-2}`, and each
  fibre of `g` has at most two elements (`WellSpaced.card_fiber_le_two`, one frequency on each
  side). So `b_s ≤ 2 δ^{-2} ∑_{k≥1} k^{-2} = 2 δ^{-2} · π²/6`.
* `eigenvalue_sq_le`. Hence `μ² ≤ 3 · π²/(3δ²) = (π/δ)²` for every eigenvalue `iμ` of `A`.
* `hilbertMatrix`, `hilbertMatrix_isHermitian`, `norm_apply_le`. `H = iA` is Hermitian, so
  `toEuclideanLin H` is symmetric. In its orthonormal eigenbasis
  (`LinearMap.IsSymmetric.eigenvectorBasis`), `‖H x‖² = ∑_k ν_k² |⟨u_k, x⟩|²`, and each
  `H u_k = ν_k u_k` gives `A u_k = i(−ν_k) u_k`. So `‖H x‖ ≤ (π/δ) ‖x‖`.
* `generalizedHilbertInequality`. The form equals `i ⟨H x, x⟩`, because the `s = r` term
  vanishes. Cauchy–Schwarz and the operator bound finish the proof.

## Hypothesis hygiene

This round introduces **no** new `def … : Prop`. `GeneralizedHilbertInequality` already
existed; it is now proved, so the four hygiene questions do not arise. No theorem of the
repository takes `GeneralizedHilbertInequality` as a hypothesis. The new theorems have it, or
plain inequalities, as their *conclusion*. So `docs/goal/conditional-theorems.txt` must not
change, and it does not (see Commands).

## Adversarial revalidation: M2-HILBERT-INEQUALITY

* *Constants, by hand.* `ζ(2) = π²/6`, so `2ζ(2)/δ² = π²/(3δ²)` (`colSq_le`).
  `3 · π²/(3δ²) = π²/δ²` (`eigenvalue_sq_le`). `√(π²/δ²) = π/δ` because `π/δ > 0`. The pinned
  statement has `Real.pi / δ`, not a weaker constant.
* *Vacuity.* The hypotheses are `0 < δ` and pairwise separation; both are satisfiable for
  every `n` (`λ_r = r δ`). For `n = 2`, `λ = (0, δ)` and `x = (1, i)`, the left side is
  `‖x₀ conj(x₁)/(−δ) + x₁ conj(x₀)/δ‖ = 2/δ` and the right side is `2π/δ`. So the inequality is
  not trivially satisfied by a zero left side.
* *Load-bearing separation.* Without it, `λ = (0, ε)` and `x = (1, i)` give a left side of
  `2/ε`, which is unbounded as `ε → 0` while the right side stays at `2π/δ`. Positivity of `δ`
  is needed for `π/δ` to make sense: for `δ ≤ 0` the right side is `≤ 0`.
* *The false identity is not used.* The cancellation in `eigen_bound` uses the eigen-equation
  `hv` twice: in `hvc` (conjugated rows) and in `hcol` (columns, through `kernel_swap`). The
  operator bound is assembled only from eigenvectors (`norm_apply_le`), never from a claimed
  identity for arbitrary `x`.
* *Claim mode.* A proof in this repository. The spectral theorem and Basel's sum are Mathlib's.
  The definition being proved is the repository's, unchanged.
* *Statement pinning.* `scripts/revalidation.lean` writes the full statement out (the body of
  the definition, verbatim) and supplies `generalizedHilbertInequality` as the proof term. It
  also pins `example : RiemannHypothesis.Hilbert.GeneralizedHilbertInequality`. The axioms are
  pinned in step 3 of `scripts/audit.sh`.

## Not proved

* The **optimality** of the constant `π` (that `π/δ` cannot be replaced by anything smaller) is
  classical but is **not** proved here.
* The weighted inequality `|∑_{r≠s} x_r conj(x_s)/(λ_r − λ_s)| ≤ (3π/2) ∑ |x_r|² δ_r^{-1}`
  (Montgomery–Vaughan, Theorem 2) is not proved.

## Other rows

This file was first written against an older checkout. On 2026-10-18 the round was rebased onto
the requester's repository at commit `5960dab`, and this section describes that board. There
`M2-HILBERT-INEQUALITY` is `P0` (kept), it had no `revalidation:` field (this file is now named
there), and four rows were `BLOCKED` by the round of 2026-09-16
(`docs/goal/evidence/2026-09-16-round-GHI-blocked.md`) on this theorem. Only what is now false
was changed. Each of them gets a dated `2026-10-18` line in `latest_update`, and none is marked
`DONE_STRONG`:

* `M2-MEANVALUE`: `BLOCKED` → `DONE_WEAK`. Item (i) of its `open_boundary` said that the
  generalized Hilbert inequality is not formalized. It now says that the inequality and the
  unweighted `T + O(N)` mean value theorem are proved, and that the weighted `T + O(n)` form and
  the sharp discrete large sieve remain open. Item (ii), the fourth moment, is unchanged. Its
  exit criteria include the fourth moment and the large sieve, so the row cannot close.
* `M2-MOLLIFIER`: `BLOCKED` → `TODO_NEEDS_DESIGN`. Its block was the sharp mean value theorem,
  hence this inequality. What is left is its own `open_boundary`: the mollifier family has not
  been designed yet.
* `M2-LEVINSON`: `BLOCKED` → `CLAIM_RISK`. It no longer waits on this inequality: it waits on
  `M2-MOLLIFIER`, which is now `TODO_NEEDS_DESIGN` rather than blocked. The one-third bound is
  proved, but only as a corollary of `M1-TWO-THIRDS`. Levinson's mollifier argument, which the
  title names, is not formalized. Its `open_boundary` is empty, so `DONE_WEAK` would not fit, and
  the row must not be marked done.
* `M2-DENSITY`: `BLOCKED` → `DONE_WEAK`. Its `open_boundary` said that the generalized Hilbert
  inequality is "neither in mathlib nor in this repository". That sentence now records that it is
  proved but that the density argument has not been rerun on it. The linear saving is still not
  proved, and the quadratic-saving statements are unchanged.
* `M2-MEANVALUE-MV` (stays `DONE_WEAK`; the Gaussian-majorant row). Its `open_boundary` now
  records that the Hilbert inequality and the unweighted form are proved, and that the weighted
  one, which it would need for the sharp constant, is not.

No other row was `BLOCKED` on this inequality. `M2-BEURLING-SELBERG` depends on this row but is
about the Beurling–Selberg route, which is still not formalized; it is unchanged.
`docs/goal/conditional-theorems.txt` is unchanged.

The statements of `HilbertFreeBound`, `MeanValueWellSpaced` (the Gaussian-majorant mean value
theorem) and `HilbertInequality` are unchanged.

`RiemannHypothesis/HilbertInequality.lean` is the requester's version. The definition of
`GeneralizedHilbertInequality` in it is the same, verbatim, as the one proved here. As shipped
at `5960dab` the file did not compile, so four changes were needed, and no declaration was
removed or restated:

* The module docstring was never closed: its "Attempts toward the general form" section ran
  into the code, and Lean reported `unterminated comment`. That section was rewritten to say
  that the general form is now proved in `MontgomeryVaughan.lean`, and the docstring is
  closed. The half-sentence before it ("…by the Gaussian majorant") gets back its lost end
  ("method, with a worse constant.").
* `fake_cancellation_counterexample_arith` and `fake_cancellation_identity_is_false`: plain
  `decide` does not reduce rational arithmetic, so both proofs are now `decide +kernel`. The
  axioms are still `[propext, Classical.choice, Quot.sound]`.
* `fake_cancellation_identity_is_false`: the deprecated binder `∑ r in s` no longer parses and is
  now `∑ r ∈ s`. The statement is the same.
* `BeurlingSignMajorant` uses `Real.sign`, so `import Mathlib.Data.Real.Sign` was added.

## Continuous integration (R0)

This round also adds `.github/workflows/ci.yml` and updates `docs/build-environment.md`. See
`docs/goal/evidence/2026-10-18-m2-meanvalue-mv-sharp.md` § "Build measurements" for the build
time and memory measured here. No board row is attached to CI.

## Commands

See the end of `docs/goal/evidence/2026-10-18-m2-meanvalue-mv-sharp.md`. That section lists
every gate of this round and its output, for both rows.
