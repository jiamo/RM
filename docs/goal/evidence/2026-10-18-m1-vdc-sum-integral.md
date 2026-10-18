# van der Corput's sum-versus-integral lemma (Titchmarsh, Lemmas 4.8 and 4.10)

Date: 2026-10-18
Task: `M1-VDC-SUM-INTEGRAL` (new, `DONE_STRONG`)
Module: `RiemannHypothesis/VanDerCorputSumIntegral.lean` (new; imports `KusminLandau`)

## Claim

```lean
def cotDefect (Δ : ℝ) : ℝ := cotpi Δ - 1 / (Real.pi * Δ)
def vdcKappa (θ : ℝ) : ℝ := -cotDefect θ

theorem norm_sum_e2pi_sub_integral_le {a θ : ℝ} {N : ℕ} {f f' : ℝ → ℝ}
    (hθ : θ < 1)
    (hf : ∀ u ∈ Set.Icc a (a + N), HasDerivAt f (f' u) u)
    (hmono : MonotoneOn f' (Set.Icc a (a + N)) ∨ AntitoneOn f' (Set.Icc a (a + N)))
    (hbd : ∀ u ∈ Set.Icc a (a + N), |f' u| ≤ θ) :
    ‖∑ n ∈ range N, e2pi (f (a + n)) - ∫ u in a..a + N, e2pi (f u)‖
      ≤ 5 / 2 + 4 * Real.pi * θ + 5 / 2 * vdcKappa θ

theorem norm_sum_mul_e2pi_sub_integral_le {a θ : ℝ} {N : ℕ} {f f' g : ℝ → ℝ}
    (hθ : θ < 1)
    (hf : ∀ u ∈ Set.Icc a (a + N), HasDerivAt f (f' u) u)
    (hmono : MonotoneOn f' (Set.Icc a (a + N)))
    (hbd : ∀ u ∈ Set.Icc a (a + N), |f' u| ≤ θ)
    (hg : ContinuousOn g (Set.Icc a (a + N)))
    (hg0 : ∀ u ∈ Set.Icc a (a + N), 0 ≤ g u)
    (hganti : AntitoneOn g (Set.Icc a (a + N))) :
    ‖∑ n ∈ range N, (g (a + n) : ℂ) * e2pi (f (a + n))
        - ∫ u in a..a + N, (g u : ℂ) * e2pi (f u)‖
      ≤ (5 / 2 + 4 * Real.pi * θ + 5 / 2 * vdcKappa θ) * g a
```

and `norm_sum_mul_e2pi_sub_integral_le_of_antitone`, the same with `AntitoneOn f'` (namespace
`RiemannHypothesis.VdcSumIntegral`; `e2pi x = exp(2πix)` and `cotpi x = cos(πx)/sin(πx)` from
`KusminLandau.lean`).

In words: for real `f` with `f'` monotone and `|f'| ≤ θ < 1`, `∑_{n<N} e(f(a+n))` is
`∫_a^{a+N} e(f)` up to `5/2 + 4πθ + 5κ(θ)/2`, `κ(θ) = 1/(πθ) − cot(πθ)` (`κ(0) = 0` by Lean's
`1/0 = 0`); with a nonnegative decreasing continuous weight the error is that constant times
`g(a)`. This is the general lemma, not only the phase of `ζ`. Mode: a **proof** in this
repository.

## The argument

Not Titchmarsh's (Euler–Maclaurin with the sawtooth, its Fourier series, the first-derivative
test per frequency). Per unit interval `[p, p+1]`, `Δ = f(p+1) − f(p)`:

* `increment_mem_unit`: `f'(p) ≤ Δ ≤ f'(p+1)` (mean value theorem, `f'` monotone); hence the
  increments are monotone in `p` and `|Δ| ≤ θ`.
* `norm_unit_sub_integral_le`: `|f − L| ≤ f'(p+1) − f'(p)` for the linear interpolant `L`, so
  `‖∫ e(f) − ∫ e(L)‖ ≤ 2π (f'(p+1) − f'(p))`; summed, at most `2π · 2θ`.
* `integral_e2pi_linear`, `ampDefect_mul_e2pi_sub_one`: `e(f(p)) − ∫_p^{p+1} e(L) =
  G(Δ)(e(f(p+1)) − e(f(p)))`, `G(Δ) = 1/(e(Δ) − 1) − 1/(2πiΔ) = −1/2 − (i/2) k(Δ)`,
  `k = cotDefect`; `G(0) = −1/2` covers `Δ = 0`.
* `antitoneOn_cotDefect`: `k` decreases on `(−1, 1)` (`k' = π/(πΔ)² − π/sin² πΔ ≤ 0` on
  `(0, 1)`, `k ≤ 0` there from `x cos x ≤ sin x`, `k` odd); so `|k(Δ)| ≤ κ(θ)` and the total
  variation of `k(Δ_n)` is at most `2κ(θ)`.
* Weight: `g(p) e(f(p)) − ∫ g e(f) = ∫ (g(p) − g) e(f) + g(p)(e(f(p)) − ∫ e(f))`; the first
  telescopes to at most `g(a)`.
* Abel summation (`norm_sum_mul_sub_le`) with `c_n = g(a+n) G(Δ_n)`: end terms
  `2 · g(a)(1 + κ)/2`, variation `g(a) κ + g(a)(1 + κ)/2`.

Total `g(a)(1 + 4πθ + 3(1 + κ)/2 + κ) = g(a)(5/2 + 4πθ + 5κ/2)`. The antitone case applies the
increasing case to `−f` (`e(−x) = conj e(x)`, `e2pi_neg`).

## Hypothesis hygiene

No new `def … : Prop`; no theorem takes an unproved `Prop` as a hypothesis.
`docs/goal/conditional-theorems.txt` is unchanged.

## Adversarial revalidation: M1-VDC-SUM-INTEGRAL

* *Constants, by hand.* `κ(1/2) = 2/π − cot(π/2) = 0.6366`, constant `2.5 + 2π + 1.592 = 10.37`.
  `κ(1/(2π)) = 2 − cot(1/2) = 2 − 0.8776/0.4794 = 0.1695`, constant `2.5 + 2 + 0.424 = 4.924`
  (the value used by `M1-ZETA-PARTIAL-SUM`). As `θ → 1`, `κ(θ) ~ 1/(π(1 − θ)) → ∞`, as it must.
* *Non-triviality.* `f(u) = θu`, `a = 0`: the sum is `(e(θN) − 1)/(e(θ) − 1)`, the integral
  `(e(θN) − 1)/(2πiθ)`; the difference is `(e(θN) − 1) G(θ)`, of modulus up to
  `2|G(θ)| ≤ 1 + κ(θ)`, inside the bound, and not `o(1)`, so the lemma is not vacuous.
* *Load-bearing `θ < 1`.* `f(u) = u`: the sum is `N`, the integral `0`; unbounded.
* *Load-bearing monotonicity.* `f(u) = ε sin 2πu`, `|f'| ≤ 2πε < 1`: every `e(f(n)) = 1`, so the
  sum is `N`, while `∫_0^N e(f) = N J₀(2πε)`; the difference `N(1 − J₀(2πε))` is unbounded.
* *Load-bearing weight hypothesis.* `g(u) = u` (increasing), `f = 0`, `a = 0`: the sum is
  `N(N − 1)/2`, the integral `N²/2`, the difference `N/2`, while `g(a) = 0`; so the decrease of
  `g` is needed.
* *Claim mode.* A proof in this repository; Titchmarsh's constants are not claimed, and the proof
  is not his.
* *Statement pinning.* `scripts/revalidation.lean` writes out the three theorems and the
  definition of `vdcKappa` in full and supplies the repository's declarations; axioms pinned in
  step 3 of `scripts/audit.sh`.

## Not proved

* Optimal constants; the second-derivative form of the lemma (Titchmarsh, Lemma 4.9 type
  statements with `f''`).

## Commands and gates

See the section of the same name in `2026-10-18-m1-hardy-littlewood-mean-square.md`, which covers
the three rows of this round.
