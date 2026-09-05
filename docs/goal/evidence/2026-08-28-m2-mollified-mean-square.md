# M2-MOLLIFIED-MEAN-SQUARE — the mean square of the mollified partial sum

Date: 2026-08-28
Files: `RiemannHypothesis/DivisorSquareSum.lean`, `RiemannHypothesis/MollifiedMeanSquare.lean`

## Claim

Write `M_y(s) = ∑_{d ≤ y} μ(d) d^{−s}` for the Möbius mollifier of length `y`
(`RiemannHypothesis.Mollifier.mollifier`) and `P_K(s) = ∑_{k ≤ K} k^{−s}` for the partial sum of
`ζ`.  The finite mollifier identity of M2-ZERO-DETECTION says that `M_y P_K − 1` is a Dirichlet
polynomial supported on `m > y`; this row bounds its mean square on a vertical line `re s = σ`
with `σ > 1/2`, uniformly in `K` and `T`.

```lean
theorem mollifiedTail_eq {y K : ℕ} (hy : 1 ≤ y) (hyK : y ≤ K) (s : ℂ) :
    Mollifier.mollifier y s * (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s)) - 1
      = dirichletPoly (mollifiedTailCoeff y K) (y * K) s

theorem exists_integral_normSq_mollified_partialSum_sub_one_le {σ ε : ℝ} (hσ : 1 / 2 < σ)
    (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧ ∀ K : ℕ, y ≤ K → ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖ ^ 2)
        ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K))) * ε

theorem exists_volume_norm_mollified_partialSum_sub_one_ge_le {σ ε : ℝ} (hσ : 1 / 2 < σ)
    (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧ ∀ K : ℕ, y ≤ K → ∀ T : ℝ, 0 ≤ T → ∀ V : ℝ, 0 < V →
      (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
            (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖}).toReal
        ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K))) * ε / V ^ 2
```

The mollifier length `y` depends only on `σ` and `ε`; the bounds then hold for **every** `K ≥ y`
and every `T ≥ 0`.

The arithmetic input is proved separately, in `RiemannHypothesis/DivisorSquareSum.lean`:

```lean
theorem divisorCount_le_mul_of_dvd {n u : ℕ} (hn : n ≠ 0) (hu : u ∣ n) :
    divisorCount n ≤ divisorCount u * divisorCount (n / u)

theorem divisorCount_sq_le_divisorCount4 (n : ℕ) : divisorCount n ^ 2 ≤ divisorCount4 n

theorem summable_divisorCount_sq_rpow {a : ℝ} (ha : 1 < a) :
    Summable fun n : ℕ => (divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-a)

theorem exists_tsum_normSq_tailCoeff_lt {σ ε : ℝ} (hσ : 1 / 2 < σ) (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧
      ∑' n : ℕ, ‖Mollifier.tailCoeff y (n + 1)‖ ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) < ε
```

## Proof

1. *Sub-multiplicativity of `d`.*  For `u ∣ n`, `n ≠ 0`, the map `v ↦ (gcd(u, v), v / gcd(u, v))`
   injects the divisors of `n` into `divisors u ×ˢ divisors (n/u)`; injectivity is
   `gcd(u,v) · (v / gcd(u,v)) = v`, and the target membership uses
   `v / gcd(u,v) ∣ n / u` (`div_gcd_dvd_div_of_dvd`, from `lcm u v ∣ n`).  Summing the resulting
   bound `d(n) ≤ d(u) d(n/u)` over the `d(n)` divisors `u` of `n` gives `d(n)² ≤ d₄(n)`, where
   `d₄ = d ⍟ d` is the four-fold divisor function.
2. *Summability.*  `d₄` is a Dirichlet convolution of two Dirichlet series absolutely convergent
   for `re s > 1`, so `∑ d₄(n) n^{−a} < ∞` for `a > 1`, and a fortiori `∑ d(n)² n^{−a} < ∞`.
3. *Small tails.*  The coefficients `c_{y,K}(m) = ∑_{d ∣ m, d ≤ y, m/d ≤ K} μ(d)` of `M_y P_K`
   satisfy `|c_{y,K}(m)| ≤ d(m)` (a sub-sum of `∑_{d ∣ m} 1`), and they vanish for `m ≤ y`.  Since
   `2σ > 1`, the tail `∑_{m > y} d(m)² m^{−2σ}` tends to `0` as `y → ∞`, so a length `y = y(σ, ε)`
   can be chosen with tail `< ε`.
4. *Mean value theorem.*  `abs_integral_normSq_dirichletPoly_sub_diag_le_mvt` (M2-MEANVALUE)
   applied to the polynomial `∑_{m ≤ yK} c_{y,K}(m) m^{−s}` bounds
   `∫₀ᵀ ‖·‖²` by `(T + 8·yK·(1 + log(yK))) · ∑_{y < m ≤ yK} |c_{y,K}(m)|² m^{−2σ}`, and the last
   factor is at most the infinite tail of step 3, hence at most `ε`.
5. *Large values.*  Chebyshev's inequality on `(0, T]`, using continuity of
   `t ↦ ‖dirichletPoly a N (σ + i t)‖²` for measurability of the level set.

## Scope

* Everything here is about the **Dirichlet polynomial** `M_y · P_K`, not about `ζ M_y`.  Replacing
  the partial sum `P_K` by `ζ` in the strip requires the Euler–Maclaurin (or approximate
  functional equation) approximation of `ζ` together with control of the resulting error against
  the mollifier; that step is not carried out.
* The factor `8 yK (1 + log(yK))` is the error term of the repository's elementary mean value
  theorem.  It is harmless as long as `yK` is small compared with `T`, but the Carlson–Ingham
  density argument needs polynomials of length comparable with `T`, where this error term is of
  size `T log T` and destroys the saving.  Reaching `o(T)` therefore also needs the sharp
  Montgomery–Vaughan form of the mean value theorem, with error `O(N)` in place of
  `O(N log N)`.
* Consequently **no zero-density estimate** is claimed, and no zero of `ζ` is located.

## Gates

* `lake build RiemannHypothesis.DivisorSquareSum` and `lake build
  RiemannHypothesis.MollifiedMeanSquare` succeed; both modules contain no `sorry` and are imported
  by the root `RiemannHypothesis.lean`.
* `#print axioms` on the results gives exactly `propext, Classical.choice, Quot.sound`.
* `./scripts/audit.sh` prints `OK`.
* The statements are pinned in `scripts/revalidation.lean`.
