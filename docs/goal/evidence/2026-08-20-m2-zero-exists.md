# Evidence: the critical strip contains a zero of `ζ` (2026-08-20)

Row: `M2-ZERO-EXISTS` (new, `DONE_STRONG`).

## Why the row exists

Every earlier result of this repository about the zeroes of `ζ` inside the open critical strip is
an upper bound (`M2-ZERO-COUNT`, `M2-ZERO-COUNT-LOCAL`), a symmetry (`M0-XI`, `M1-ZERO-LOCATION`)
or a convergence statement (`M2-ZERO-SUM`). Each of them is *equally true* if the strip contains
no zero at all — the evidence file of `M2-ZERO-SUM` says so explicitly. This row removes that
escape hatch by proving that a nontrivial zero exists.

## What is proved (without `sorry`)

`RiemannHypothesis/ZeroExists.lean`:

* `exists_exp_of_ne_zero` : an entire `f` with `f z ≠ 0` for all `z` is `exp ∘ g` for an entire
  `g`;
* `linear_of_re_le` : an entire `g` with `(g z).re ≤ C(1+‖z‖)log(2+‖z‖) + D` (with `0 ≤ C`,
  `0 ≤ D`) satisfies `g z = a + b·z` for constants `a b : ℂ`;
* `factorial_le_norm_xiFn` : `π^{-(n+1)}·n! ≤ ‖ξ(2(n+1))‖` for `n ≥ 1`;
* `exists_xiFn_eq_zero` : **`ξ` has a zero**;
* `nontrivialZeroSet_nonempty` : **`nontrivialZeroSet` is nonempty**;
* `exists_riemannZeta_eq_zero_of_mem_strip` : **there is an `s` with `ζ s = 0`, `0 < re s < 1`**.

## The argument

Suppose `ξ` has no zero. Since `ℂ` is convex and `ξ` is entire (`differentiable_xiFn`), the
entire function `ξ'/ξ` has a primitive `G` (`Convex.exists_forall_hasDerivWithinAt` on
`Set.univ`), and `(ξ · e^{-G})' = 0`, so `ξ = e^g` with `g` entire
(`is_const_of_deriv_eq_zero`). Taking `Real.log` of the order-one bound
`‖ξ(s)‖ ≤ exp(C(1+‖s‖)log(2+‖s‖))` of `M1-XI-GROWTH` (`norm_xiFn_le`) gives
`(g z).re ≤ C(1+‖z‖)log(2+‖z‖)`.

`linear_of_re_le` converts that into linearity. Borel–Carathéodory
(`Complex.borelCaratheodory`) bounds `‖g‖` on the closed ball of radius `R/2` by a constant times
the bound on `re g` over the ball of radius `R`, i.e. by `O(R log R) = O(R^{3/2})` using
`log x ≤ 2√x`; Cauchy's estimate for the second derivative
(`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` with `n = 2`) then gives
`‖g''(z)‖ ≤ 2·O(R^{3/2})/R² → 0`, so `g'' ≡ 0`, so `g'` is constant `b` and `g z = g 0 + b z`.

Hence `‖ξ(z)‖ = e^{re(a + b z)} ≤ e^{‖a‖} e^{2‖b‖(n+1)}` at `z = 2(n+1)`, an exponential bound
`B·Lⁿ` with `L = π·e^{2‖b‖}`.

The lower bound is a computation on the real axis. With
`ξ(s) = ½ s(s−1)Λ(s)` and `Λ(s) = Γ_ℝ(s)ζ(s)`, at `s = 2(n+1)` one has
`Γ_ℝ(2(n+1)) = π^{-(n+1)}Γ(n+1)`, so `‖Γ_ℝ(2(n+1))‖ = π^{-(n+1)} n!` (`norm_Gammaℝ_even`),
while `‖ζ(2(n+1))‖ ≥ 1/2` for `n ≥ 1` by `half_le_norm_riemannZeta_of_three_le_re`
(`M2-ZERO-COUNT-LOCAL`) and `½·|2(n+1)|·|2(n+1)−1| ≥ 2` for `n ≥ 1`. Multiplying,
`‖ξ(2(n+1))‖ ≥ π^{-(n+1)}·n!`.

So `n! ≤ B·Lⁿ` for all `n ≥ 1`, contradicting `Lⁿ/n! → 0`
(`FloorSemiring.tendsto_pow_div_factorial_atTop`). Therefore `ξ` has a zero `s`, and
`riemannXi_eq_zero_iff` (via `xiPoint_neg_I_mul_sub`) turns it into a zero of `ζ` with
`0 < re s < 1`.

## Commands run

```
lake build RiemannHypothesis.ZeroExists
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for all six declarations above reports exactly
`[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **Nothing is located.** The proof is a contradiction: it produces no bound on the height of
  the zero it asserts, no algorithm to find one, and of course no information about its real
  part. In particular this row does not bear on the Riemann hypothesis at all.
* **No count.** That the zeroes are *infinite* in number is not proved here; it follows from the
  same scheme after dividing out a polynomial factor, and is proved in row `M2-ZERO-INFINITE`,
  [`docs/goal/evidence/2026-08-20-m2-zero-infinite.md`](2026-08-20-m2-zero-infinite.md). No
  lower bound `N(T) ≫ T log T` is proved anywhere in this repository.
* The Hadamard product for `ξ` is still not constructed; only the "no zeroes ⇒ `e^{linear}`"
  special case is.
* The constants `a`, `b`, `C`, `L` are all non-explicit existentials.

## Adversarial revalidation: M2-ZERO-EXISTS

Second, independent pass.

* **Claim mode.** All six results are `theorem`s proved in this repository and are pinned in
  full in `scripts/revalidation.lean` with the repository declarations as proof terms. No
  statement mentions the Riemann hypothesis, and none implies it: knowing that a zero exists in
  the open strip says nothing about where it is.
* **Vacuity check.** The two headline statements are existential, so they cannot be vacuous:
  `exists_riemannZeta_eq_zero_of_mem_strip` produces an actual `s : ℂ` together with proofs of
  `riemannZeta s = 0`, `0 < s.re` and `s.re < 1`. There is no hypothesis to be unsatisfiable.
  This is the precise complement of the risk flagged in the `M2-ZERO-SUM` evidence.
* **Direction check.** The contradiction runs between an upper bound on `‖ξ‖` derived from the
  assumption of no zeroes (exponential in `n`) and an unconditional lower bound at the same
  points (factorial in `n`). Both are bounds on the *same* quantity `‖ξ(2(n+1))‖` at the *same*
  arguments, so no mismatch of scales can hide in between; and factorial growth strictly beats
  exponential growth, which is what `FloorSemiring.tendsto_pow_div_factorial_atTop` supplies.
* **Where each input is really used.** `M1-XI-GROWTH` (`norm_xiFn_le`) is what makes `re g` small
  enough for Borel–Carathéodory; if `ξ` were only of order two the same scheme would give a
  quadratic `g` and no contradiction, so the order-one bound is genuinely load-bearing.
  `half_le_norm_riemannZeta_of_three_le_re` is what stops the lower bound from being destroyed by
  a possible zero of `ζ` on the real axis to the right of `3`.
* **Independent sanity check of the lower bound.** At `n = 1`, `ξ(4) = ½·4·3·π^{-2}Γ(2)ζ(4)`
  `= 6π^{-2}·(π⁴/90) = π²/15 ≈ 0.658`, and the proved bound is `π^{-2}·1! ≈ 0.101`; the
  inequality holds with room, as it must, since the proof throws away a factor
  `½|s||s−1|·‖ζ‖ ≥ 2·½ = 1`.
* **Sanity check of the conclusion.** The first nontrivial zero is at `½ + 14.13…i`, so the
  statement is of course true; what the row provides is that it is now *proved* in this
  repository rather than assumed.
* **Statement pinning.** `scripts/revalidation.lean` writes out `exists_exp_of_ne_zero`,
  `linear_of_re_le`, `factorial_le_norm_xiFn`, `exists_xiFn_eq_zero`,
  `nontrivialZeroSet_nonempty` and `exists_riemannZeta_eq_zero_of_mem_strip` in full;
  `scripts/audit.sh` prints their axioms.
