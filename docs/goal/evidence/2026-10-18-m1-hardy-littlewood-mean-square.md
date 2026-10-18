# The Hardy–Littlewood mean square on the critical line: `∫₀ᵀ |ζ(1/2 + it)|² dt = T log T + O(T)`

Date: 2026-10-18
Task: `M1-HARDY-LITTLEWOOD-MEAN-SQUARE` (new, `DONE_STRONG`; filed under milestone M2 because it
depends on `M2-MEANVALUE-WEIGHTED`, and the board forbids an M1 row to depend on an M2 row)
Module: `RiemannHypothesis/HardyLittlewoodMeanSquare.lean` (new; imports `ZetaPartialSum` and
`MontgomeryVaughanWeightedMeanValue`)

## Claim

```lean
theorem abs_integral_block_zeta_sub_le {T : ℝ} (hT : 1 ≤ T) :
    |(∫ t in T..2 * T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        - T * Real.log T| ≤ 584 * T

theorem exists_abs_integral_normSq_riemannZeta_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        - T * Real.log T| ≤ C * T

theorem tendsto_integral_normSq_riemannZeta_div :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) / (T * Real.log T))
      atTop (nhds 1)
```

(namespace `RiemannHypothesis.HardyLittlewood`). Intermediate results, also pinned for their
axioms: `abs_integral_criticalPoly_sub_le` (`|∫₀^{T'} |P_N|² − T' H_N| ≤ 20√2 N`),
`abs_integral_block_criticalPoly_sub_le` (`≤ 122 T` on `[T, 2T]` with `N = ⌊2T⌋`),
`norm_zeta_sub_criticalPoly_le` (`|ζ(1/2 + it) − P_{⌊2T⌋}(t)| ≤ 13/√T` for `t ∈ [T, 2T]`).

Mode: a **proof** in this repository. The global statement holds for every `T ≥ 1` (the request
asked for `T ≥ 2`); its constant is existential.

## The argument (Montgomery–Vaughan's route)

1. `abs_integral_criticalPoly_sub_le`: with `a_n = n^(−1/2)`, `|a_n|² = 1/n`,
   `∑_{n ≤ N} (n + 1)|a_n|² ≤ 2N`, the weighted mean value theorem
   (`abs_integral_normSq_dirichletPoly_sub_le_weighted`, constant `10√2`) gives
   `|∫₀^{T'} |P_N|² − T' H_N| ≤ 20√2 N`, `H_N = ∑_{n ≤ N} 1/n`.
2. `abs_integral_block_criticalPoly_sub_le`: `∫_T^{2T} = ∫₀^{2T} − ∫₀^T` (same `N = ⌊2T⌋` in both),
   error `40√2 N ≤ 80√2 T ≤ 120 T`; `log T ≤ log(N + 1) ≤ H_N ≤ 1 + log N ≤ 1 + log 2 + log T`
   (`harm_floor_two_mul_bounds`, from mathlib's `log_add_one_le_harmonic` and
   `harmonic_le_one_add_log`) adds `≤ 2T`. Total `122 T`.
3. `norm_zeta_sub_criticalPoly_le`: Theorem 4.11 (`M1-ZETA-PARTIAL-SUM`) with `x = 2T ≥ t`:
   `11 (2T)^(−1/2) ≤ 11/√T`, and `|(2T)^(1/2−it)/(1/2 − it)| ≤ √2 √T / T ≤ 2/√T`.
4. `abs_integral_block_zeta_sub_le`: with `r = √T`, `p = |P|`, `e = |ζ − P|`, `z = |ζ|`:
   `z² ≤ p² + 2pe + e²` and `z² ≥ p² − 2pe`; `2pe ≤ p²/r + r e²` (pointwise Cauchy–Schwarz);
   `e² ≤ 169/T`. Integrating over `[T, 2T]`: `(1/r)∫|P|² ≤ (T log T + 122 T)/√T ≤ 124 T`
   (`log T ≤ 2√T`), `T (r + 1) 169/T ≤ 338 T`. Total `122 + 124 + 338 = 584`.
5. `exists_abs_integral_normSq_riemannZeta_sub_le`: `F(T) = ∫₀ᵀ |ζ|² − T log T`;
   `F(2T) − F(T) = ∫_T^{2T} |ζ|² − T log T − 2T log 2`, so `|F(2T) − F(T)| ≤ 586 T`; on `[1, 2]`,
   `|F| ≤ M₀ = ∫₀² |ζ(1/2 + it)|² dt + 2`; induction over `[1, 2^(k+1)]` gives
   `|F(T)| ≤ M₀ + 586 T ≤ (M₀ + 586) T`.
6. `tendsto_integral_normSq_riemannZeta_div`: `|ratio − 1| ≤ C/log T → 0`.

## Hypothesis hygiene

No new `def … : Prop`; no theorem takes an unproved `Prop` as a hypothesis.
`docs/goal/conditional-theorems.txt` is unchanged.

## Adversarial revalidation: M1-HARDY-LITTLEWOOD-MEAN-SQUARE

* *Constants, by hand.* `20√2 = 28.28 ≤ 30`, so `40√2 N ≤ 60 · 2T = 120 T`; `1 + log 2 = 1.693
  ≤ 2`; `122 + 124 + 338 = 584`; `2 log 2 = 1.386 ≤ 2`, so `584 + 2 log 2 ≤ 586`. Error of the
  approximation at `T = 1`: `11/√2 + √2 = 9.19 ≤ 13`.
* *Consistency with the literature.* Ingham: `∫₀ᵀ |ζ(1/2 + it)|² dt = T log T + (2γ − 1 − log 2π) T
  + O(T^(1/2) log T)`, `2γ − 1 − log 2π = −1.6834`; so the difference is `≈ −1.68 T`, which is
  `O(T)` and not `o(T)`: the statement proved is of the right strength and cannot be improved to
  `o(T)` without the second term.
* *Non-vacuity.* `C` is existential but the statement is not vacuous: it implies the limit
  `ratio → 1`, which fails for any wrong main term (`c T log T` with `c ≠ 1`).
* *Load-bearing `T ≥ 1`.* At `T → 0⁺` the main term `T log T` and the bound `C T` both tend to `0`,
  but `|T log T|/T = |log T| → ∞` while the integral is `≈ ζ(1/2)² T`; so no bound `C T` holds
  near `0`, and the restriction is needed.
* *Claim mode.* A proof in this repository. The approximate functional equation is not used.
  Ingham's second term and the error `O(T^(1/2) log T)` are **not** proved.
* *Statement pinning.* `scripts/revalidation.lean` writes out the three statements above and
  supplies the repository's declarations; axioms pinned in step 3 of `scripts/audit.sh`.

## Not proved

* Ingham's second term `(2γ − 1 − log 2π) T`, the error `O(T^(1/2) log T)`, an explicit global
  constant, and the fourth moment.

## Board edits of this round (one line each)

* `M1-CRITICAL-LINE-MEAN-SQUARE` (stays `DONE_WEAK`): the open boundary no longer says the
  asymptotic needs the approximate functional equation; what remains open is the fourth moment.
* `M1-STRIP-MEAN-SQUARE` (stays `DONE_WEAK`): item (ii) now points to this row; items (i), (iii),
  (iv) remain open.
* `M1-STRIP-MEAN-SQUARE-ASYMPTOTIC` (stays `DONE_WEAK`): the first sentence now points to this
  row; the second order term, an explicit saving and higher moments remain open.
* `M1-ZETA-CHI-AFE` (stays `DONE_WEAK`): the clause saying the mean value theorem is missing is
  replaced; the approximate functional equation is still only recorded.
* `M1-MEAN-SQUARE` (stays `DONE_STRONG`): the clause "needing the approximate functional
  equation" in its scope note is replaced; `open_boundary` is empty as before.
* `M2-LEVINSON` (stays `CLAIM_RISK`): `open_boundary` written from its own `latest_update`.

## Commands and gates

```
$ lake build            # full, from a cold cache, then incremental after the last edits
✔ [12519/12521] Built RiemannHypothesis.StripMeanSquareAsymptoticHalf (20s)
✔ [12520/12521] Built RiemannHypothesis (6.9s)
Build completed successfully (12521 jobs).

$ bash scripts/audit.sh   # exit status 0
==> coverage of the pinned axiom checks (scripts/audit_coverage.py)
exported theorems : 28805
audited names     : 893
covered           : 893 (3.1%)
missing coverage  : 27912
stale audit lines : 0
==> checking for Float
==> pinning the claims of the closed rows (scripts/revalidation.lean)
==> checking the conditional/unconditional boundary
==> validating the task board
OK: 187 tasks validate
OK

$ python3 scripts/goal_state.py validate
OK: 187 tasks validate

$ git diff --stat <round-3 tree> -- docs/goal/conditional-theorems.txt
(empty)
```
