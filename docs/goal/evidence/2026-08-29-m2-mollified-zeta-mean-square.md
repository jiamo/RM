# M2-MOLLIFIED-ZETA-MEAN-SQUARE — the mean square of `ζ M_y − 1` in the strip

Date: 2026-08-29
Files: `RiemannHypothesis/MollifiedZetaMeanSquare.lean`, `RiemannHypothesis/MollifiedZetaCircle.lean`

## Claim

```lean
theorem exists_integral_normSq_zeta_mul_mollifier_sub_one_le {σ₀ ε : ℝ} (h0 : 1 / 2 < σ₀)
    (h1 : σ₀ < 1) (hε : 0 < ε) :
    ∃ y₀ : ℕ, 4 ≤ y₀ ∧ ∀ y : ℕ, y₀ ≤ y → ∃ b₀ : ℝ, 6 ≤ b₀ ∧
      ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 6 → ∀ a b : ℝ, 1 ≤ a → a ≤ b → b₀ ≤ b →
        (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
            Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) ≤ ε * b
```

together with its circle-average companion

```lean
theorem exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le {R ε : ℝ}
    (hR0 : 0 < R) (hR : R < 5 / 2) (hε : 0 < ε) : …
```

`M_y(s) = ∑_{n ≤ y} μ(n) n^{−s}` is the mollifier of `M2-ZERO-DETECTION` and
`F_y = ζ M_y` is `mollifiedZeta`.

## Proof

Split `ζ M_y − 1 = (M_y P_K − 1) + M_y (ζ − P_K)` with `P_K(s) = ∑_{k ≤ K} k^{−s}` and the
truncation length `K = ⌈b^α⌉`, `α = (1 + 1/(3/2 − σ₀))/2`, which satisfies `1 < α` and
`α (3/2 − σ₀) < 1`.

*The polynomial half.*  `mollifiedTail_eq` writes `M_y P_K − 1` as a Dirichlet polynomial of
length `yK` supported on `m > y`, with coefficients bounded by the divisor function.  The
Montgomery–Vaughan shape of the mean value theorem (`M2-MEANVALUE-MV`) gives

`∫₀ᵀ ‖M_y P_K − 1‖² ≤ 58 ∑_{y < m ≤ yK} d(m)² m^{−2σ} (T + m)`,

with the error term inside the sum.  The diagonal part `T ∑_{m > y} d(m)² m^{−2σ}` is small
because the series converges for `σ > 1/2` (`summable_divisorCount_sq_rpow`), and the second
part is `∑_{m ≤ yK} d(m)² m^{1−2σ} ≤ S (yK)^{3/2−σ₀}`, which is `o(b)` exactly because
`α (3/2 − σ₀) < 1`.  With the elementary mean value theorem, whose error `8 N (1 + log N)`
sits outside the sum, this length would have contributed `≈ b^α log b`, and the argument
would fail.

*The tail half.*  Euler–Maclaurin of order `m` gives
`‖ζ − P_K‖ ≤ (K+1)^{1−σ}/‖s−1‖ + C (K^{−σ} + (σ + |t| + m)^m K^{1−σ−m})`; the first term
contributes `O(K^{2−2σ₀} ∫ t^{−2}) = O(b^{2α(1−σ₀)}) = o(b)` and the last is `o(1)` once `m`
is large enough in terms of `α`.  Multiplying by `‖M_y‖ ≤ y` costs a fixed factor.

*The circle averages.*  `norm_mollifiedZeta_sub_one_le` bounds `‖F_y − 1‖` by `1/y` on
`re s ≥ 3`, and the vertical bound is transported to circles of radius `R < 5/2` about
`3 + i u` by Tonelli, exactly as in the unmollified case of `M2-BOHR-LANDAU`.

## Verification

`lake build` succeeds; no `sorry`; `#print axioms` on the statements above gives exactly
`propext, Classical.choice, Quot.sound` (checked in `scripts/audit.sh`); the main statement is
pinned in `scripts/revalidation.lean`.

## Scope

The mollifier length `y` is *fixed*: the theorem says the mean square is `o(b)`, not that it is
`O(b y^{1−2σ})` for a length `y` growing as a power of the height.  That explicit form is what
a power saving in the density theorem would require, and it is not proved here.  Nothing is
claimed on the critical line itself, and no higher moment is addressed.  The consequence for
the zeroes is drawn on `M1-ALMOST-ALL-STRIP`.
