# M2-ZERO-ORDINATE — `γ_n ~ 2π n / log n`

Date: 2026-08-25
File: `RiemannHypothesis/ZeroOrdinate.lean`
Predecessor: `docs/goal/evidence/2026-08-25-m2-rvm-cumulative-sharp.md`

## Claim

The counting function asymptotic `N(0, T) ~ (T/2π) log T` of `M2-RVM-CUMULATIVE` is inverted:

* `nthZeroOrdinate n` — the ordinate `γ_n` of the `n`-th nontrivial zero of `ζ` in the upper
  half plane, counted with multiplicity, defined as the least height at which `N(0, ·)`
  reaches `n`;
* `le_windowCount_nthZeroOrdinate` — the infimum is attained: `n ≤ N(0, γ_n)`;
* `exists_mem_nontrivialZeroSet_im_eq_nthZeroOrdinate` — for `n ≥ 1` the height `γ_n` is the
  ordinate of an actual zero of `ζ` in the open critical strip, so the definition deserves its
  name;
* `tendsto_nthZeroOrdinate_atTop` — `γ_n → ∞`;
* `tendsto_nthZeroOrdinate_mul_log_div_nat` — `γ_n log γ_n ~ 2π n`;
* `tendsto_nthZeroOrdinate_mul_log_nat_div` — **the classical form** `γ_n ~ 2π n / log n`.

## Proof

* The set `{T ≥ 0 | n ≤ N(0, T)}` is nonempty because `N(0, T) → ∞`
  (`tendsto_windowCount_zero_atTop`, from the lower bound `exists_mul_le_windowCount_zero`), and
  is bounded below by `0`; `γ_n` is its infimum.  Since the set is upward closed, `N(0, T) < n`
  for `0 ≤ T < γ_n` and `n ≤ N(0, T)` for `T > γ_n`.
* Attainment uses that the zeroes are locally finite: if `N(0, γ_n) < n`, then no zero has
  ordinate in `(γ_n, T]` for some `T > γ_n` (either the finite set of zeroes in `(γ_n, γ_n+1]`
  is empty, or one takes `T` below its least ordinate), so `N(0, T) = N(0, γ_n) < n`,
  contradicting `n ≤ N(0, T)`.  The same finiteness, applied to the zeroes in `(0, γ_n]` and
  their largest ordinate, shows that `γ_n` is itself the ordinate of a zero.
* The asymptotic: for `ε > 0` the counting asymptotic gives `T₀` with
  `(1/2π − ε) T log T ≤ N(0, T) ≤ (1/2π + ε) T log T` for `T ≥ T₀`.  Letting `T ↑ γ_n` in
  `N(0, T) < n` and `T ↓ γ_n` in `n ≤ N(0, T)` — the function `T ↦ T log T` is continuous — gives
  `(1/2π − ε) γ_n log γ_n ≤ n ≤ (1/2π + ε) γ_n log γ_n` for all large `n`, i.e.
  `n/(γ_n log γ_n) → 1/2π`.
* Taking logarithms in `γ_n log γ_n ~ 2π n` and using `log log γ_n / log γ_n → 0` gives
  `log n / log γ_n → 1`; multiplying the two limits gives `γ_n log n / n → 2π`.

## Scope — what is *not* claimed

* Zeroes are counted **with** multiplicity, and only those of positive ordinate are counted; a
  zero of multiplicity `m` therefore occupies `m` consecutive indices `n`.
* No error term is claimed for `γ_n`: the argument uses only the asymptotic `N(T) ~ (T/2π) log T`,
  not the sharper `O((log T)²)` form, and gives no rate of convergence.
* Nothing about the real parts of the zeroes is claimed, and nothing here bears on the Riemann
  hypothesis.

## Verification

* `lake build` — the whole project, clean; `RiemannHypothesis/ZeroOrdinate.lean` is imported by
  `RiemannHypothesis.lean`.
* `bash scripts/audit.sh` — exit 0; the statements are pinned in full in
  `scripts/revalidation.lean` and their axioms are checked.
* No `sorry` in `RiemannHypothesis/ZeroOrdinate.lean`.

## Adversarial revalidation: M2-ZERO-ORDINATE

* `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
  `le_windowCount_nthZeroOrdinate`, `exists_mem_nontrivialZeroSet_im_eq_nthZeroOrdinate`,
  `tendsto_nthZeroOrdinate_mul_log_div_nat` and `tendsto_nthZeroOrdinate_mul_log_nat_div`.
* The definition is not vacuous or degenerate: `exists_mem_nontrivialZeroSet_im_eq_nthZeroOrdinate`
  shows `γ_n` is the ordinate of a genuine zero for every `n ≥ 1`, and
  `tendsto_nthZeroOrdinate_atTop` shows the sequence is unbounded, so the limits below are
  statements about infinitely many distinct zeroes.
* The limits are *finite and nonzero* (`2π`), so they are not satisfiable by a degenerate
  sequence: they give both `γ_n ≪ n/log n` and `γ_n ≫ n/log n`.
* The statements are unconditional: they take no unproved `Prop` of this repository as a
  hypothesis, and the module adds no row to `docs/goal/conditional-theorems.txt`.
