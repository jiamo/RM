# A rate of convergence for equidistribution modulo one

Date: 2026-09-04
Module: `RiemannHypothesis/WeylDiscrepancy.lean`

## Why

Every counting row of the Weyl track — `M1-WEYL-CRITERION`, `M1-WEYL-COUNT`,
`M1-WEYL-COUNT-GENERAL`, `M1-WEYL-PORTMANTEAU` — records the same gap in its scope or its open
boundary: *no rate of convergence is claimed*.  What those rows prove is an implication between
two limits: if the exponential sums are `o(N)` then the proportion of the first `N` fractional
parts in `[a, b)` tends to `b − a`.  Nothing there is effective, so the quantitative exponential
sum bounds of `M1-WEYL-QUADRATIC-QUANTITATIVE`, `M1-WEYL-BADLY-APPROXIMABLE` and
`M1-WEYL-CLASSICAL` had no counting consequence at all.  This module supplies the missing device:
an inequality that bounds the discrepancy of the first `N` terms by *finitely many* exponential
sums, valid for every `N`, with explicit constants.

## What is proved

All statements live in `RiemannHypothesis.WeylDiscrepancy`.

*The kernel.*

* `kern M t = ‖∑_{j<M} e(t j)‖² / M` — the Fejér-type kernel.
* `kern_nonneg`, `kern_neg`, `kern_periodic`, `continuous_kern`.
* `kern_eq_sum`, `kern_eq_sum'` — the expansion as the double sum `(1/M) ∑_{j,k<M} e(t(j−k))`.
* `integral_kern`, `integral_kern_symm` — mass one over a period, obtained from the diagonal of
  the double sum, every off-diagonal character integrating to `0`.
* `kern_le_inv` — `kern M t ≤ 1/(4 M t²)` for `0 < |t| ≤ 1/2`, from the geometric-series bound
  `‖∑_{j<M} e(θ j)‖ ≤ 1/(2‖θ‖)` of `M1-WEYL-QUADRATIC` together with `intDist_eq_abs`.
* `integral_kern_tail` — the mass outside `[−δ, δ]` is at most `1/(2Mδ)`.

*The two estimates.*

* `abs_sub_smoothing_le` — for `g` `1`-periodic, `L`-Lipschitz, with values in `[0, 1]`,

      |g(y) − ∫₀¹ g(t) K_M(y − t) dt| ≤ L δ + 1/(2Mδ) .

* `abs_avgKern_sub_one_le` — the smoothed empirical density deviates from `1` by at most
  `2 ∑_{m=1}^{M−1} ‖∑_{n<N} e(m xₙ)‖ / N`, uniformly in `t`.
* `abs_avg_smoothing_sub_integral_le` — hence the same bound for the smoothed averages.
* `abs_avg_sub_integral_le` — **the quantitative Weyl criterion**, the sum of the two.

*The counting form.*

* `perTrap`, `abs_trap_sub_trap_le`, `abs_perTrap_sub_perTrap_le`, `integral_perTrap` — the
  trapezoid of `M1-WEYL-COUNT`, periodized, and its `1/η`-Lipschitz bound.
* `countIn_le_sum_perTrap`, `sum_perTrap_le_countIn` — the indicator of `[a, b)` squeezed between
  the two trapezoids.
* `abs_countIn_div_sub_le` — the discrepancy bound with free parameters `η`, `δ`, `M`.
* `abs_countIn_div_sub_le_pow` — with `η = 1/K`, `δ = 1/K²`, `M = K⁴`:

      |#{n < N : Int.fract xₙ ∈ [a, b)}/N − (b − a)| ≤ 4/K + 2 ∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N .

*An explicit rate.*

* `norm_expSum_linear_le` — for `α` badly approximable (`‖mα‖ ≥ c/m` for all `m ≥ 1`) the
  exponential sums of `α n` at frequency `m` are at most `m/(2c)`.
* `abs_countIn_div_sub_le_linear` — hence the discrepancy of `α n` on an interval is at most
  `(4 + 1/c)/K` as soon as `K⁹ ≤ N`; that is, `O(N^(−1/9))`.

## Proof

The kernel `K_M(t) = |∑_{j<M} e(tj)|²/M` expands as `(1/M) ∑_{j,k<M} e(t(j−k))`, which is where
both estimates come from.  Integrating over a period, only the `M` diagonal pairs survive and the
mass is `1`.  Bounding `|∑_{j<M} e(tj)|` by `1/(2‖t‖)` gives `K_M(t) ≤ 1/(4Mt²)` away from the
integers, so `∫_{δ ≤ |t| ≤ 1/2} K_M ≤ 1/(2Mδ)`, computed from `∫ t^(−2)`.

*Smoothing.*  Since `K_M` has mass one and is periodic, `g(y) − ∫₀¹ g(t)K_M(y−t)dt` is, after
translating the interval of integration to `[y−1/2, y+1/2]` and substituting `t = y − s`, the
average of `g(y) − g(y−s)` against `K_M(s)` over `[−1/2, 1/2]`.  On `|s| ≤ δ` the integrand is at
most `Lδ` by the Lipschitz bound; outside, it is at most `1` because `0 ≤ g ≤ 1`, and the mass
there is at most `1/(2Mδ)`.

*Averaging.*  `(1/N) ∑_n K_M(xₙ − t) − 1` is, by the same expansion, `(1/(NM))` times the sum over
the `M² − M` off-diagonal pairs `(j, k)` of `∑_n e((j−k)(xₙ − t))`, and each of those has modulus
`‖∑_n e((j−k)xₙ)‖`.  For fixed `j` the map `k ↦ j − k` is injective into the nonzero integers of
modulus `< M`, so the inner sum is at most `2 ∑_{m=1}^{M−1} ‖∑_n e(m xₙ)‖`
(`sum_norm_expSum_shift_le`, using `‖S(−m)‖ = ‖S(m)‖`); the `M` values of `j` cancel the `1/M`.
Since `0 ≤ g ≤ 1`, testing against `g` costs nothing.

*Counting.*  The indicator of `[a, b)` lies between the periodized trapezoids with plateaus
`[a+η, b−η]` and `[a, b]`, both `1/η`-Lipschitz — across the glueing point too, because the
trapezoid vanishes at `0` and at `1`, which is what `abs_perTrap_sub_perTrap_le` checks by a case
split on whether `|fract s − fract t|` exceeds `1/2`.  Their integrals differ from `b − a` by at
most `2η`.

## Gates

* `lake build RiemannHypothesis.WeylDiscrepancy` — success, no `sorry`.
* `lake build` — success; the only `sorry`s in the repository are the three intentional ones in
  `Challenge.lean`.
* `#print axioms` on `abs_avg_sub_integral_le`, `abs_countIn_div_sub_le`,
  `abs_countIn_div_sub_le_pow`, `abs_countIn_div_sub_le_linear`: each is exactly
  `[propext, Classical.choice, Quot.sound]`.
* `./scripts/audit.sh` — `OK`.
* Three statements pinned in `scripts/revalidation.lean`, written out with `countIn`, `expSum`
  and `e2pi` fully unfolded.

## Adversarial revalidation: M1-WEYL-DISCREPANCY

* **Is the inequality vacuous?**  No.  Its right-hand side is finite and explicit for every `N`,
  and the last theorem instantiates it in a case where it tends to `0` at a definite rate: for
  badly approximable `α`, the discrepancy of `α n` on a fixed interval is `≤ (4 + 1/c)/K` once
  `K⁹ ≤ N`.  Taking `K` as large as `K⁹ ≤ N` allows gives `O(N^(−1/9))`.
* **Does the bound degenerate into triviality?**  It can, and that is the truth of the matter:
  when the exponential sums are of size `N` the right-hand side exceeds `1` and says nothing, as
  it must, since a non-equidistributed sequence has discrepancy of order `1`.
* **Is the hypothesis on the interval load-bearing?**  Yes.  `1/K < a`, `b + 1/K < 1` and
  `a + 2/K ≤ b` keep the two trapezoids inside `(0, 1)` and their plateaus non-empty; an interval
  shorter than `2/K` is simply not covered at that `K`, which is the correct behaviour, since
  `4/K` already exceeds its length.
* **Is the Lipschitz constant honest?**  The trapezoid of slope `1/η` really is `1/η`-Lipschitz on
  the circle: `abs_perTrap_sub_perTrap_le` proves the bound against `|s − t|` for *all* reals,
  using that the trapezoid vanishes at both ends of the period, so no cheating happens at the
  glueing point.
* **Is anything conditional?**  No unproved `Prop` of this repository is used.  The module imports
  `RiemannHypothesis.WeylLinear`, `RiemannHypothesis.LargeSieveGallagher`,
  `RiemannHypothesis.WeylMinSum` and Mathlib; every declaration's axioms are the standard three.
* **What is not proved.**  The sharp Erdős–Turán inequality, whose `m`-th term carries the weight
  `1/m` and which needs the Beurling–Selberg extremal majorant, is not formalized; consequently
  the linear application reaches `N^(−1/9)` rather than the classical `log N / N`.  No rate is
  drawn for the quadratic or higher-degree sequences, and nothing about `ζ` is claimed.
