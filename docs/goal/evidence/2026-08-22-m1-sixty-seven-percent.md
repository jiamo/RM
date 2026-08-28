# M1-SIXTY-SEVEN-CRITICAL — an `ε`-free 67 % on the critical line

Date: 2026-08-22
Module: `RiemannHypothesis/SixtySevenPercent.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

* `cos_le_one_sub_sq_div_two_add_pow_four_div_24` — `cos x ≤ 1 − x²/2 + x⁴/24` for `x ≥ 0`.
  Proved from Mathlib's `Real.sin_gt_sub_cube` (`x − x³/6 < sin x`): the difference
  `1 − x²/2 + x⁴/24 − cos x` vanishes at `0` and has derivative `−x + x³/6 + sin x ≥ 0`, so it is
  monotone on `[0, ∞)`.  Mathlib has no quartic upper bound for `cos`; its `Real.cos_bound` has
  error `|x|⁴·5/96`, which is too weak here.
* `tan_one_div_sqrt_two_gt_quartic` — `tan(1/√2) > 44√2/73 = 0.85240…`, from
  `sin(1/√2) > (11/12)·(1/√2)` and `cos(1/√2) ≤ 73/96`.  Sharper than the existing
  `tan_one_div_sqrt_two_gt` (`3√2/5 = 0.84852…`).
* `mtConstant_gt_eightyEight_div_117` — `c₁* > 88/117 = 0.75213…`, where
  `c₁* = √2·tan(1/√2)/(1 + tan(1/√2)/√2)`.  The existing bound `c₁* > 3/4` gives only
  `2 − 1/c₁* > 2/3`.
* `sixty_seven_lt_two_sub_inv_mtConstant` — `2 − 1/c₁* > 0.67` (in fact `> 59/88 = 0.67045…`).
* `sixty_seven_percent_on_critical_line` — the `ε`-free
  `0.67·N(T,2T) ≤ N₀*(T,2T)` for all large `T`, from Theorem D
  (`montgomery_taylor_on_critical_line`).
* `sixty_seven_percent_simple_on_critical_line` and its cumulative form over `(0, T]` — the same
  with the simple zeroes on the line.
* `thirty_three_percent_off_critical_line` — the complementary `ε`-free
  `N_off(T,2T) ≤ 0.33·N(T,2T)`.

## Why the constant works, exactly

`2 − 1/c₁* > 0.67` needs `√2·tan(1/√2) > 100/83`, i.e. `tan(1/√2) > 50√2/83`.  The bound proved
here is `tan(1/√2) > 44√2/73`, and `44·83 = 3652 > 3650 = 50·73`.  The comparison is exact
rational arithmetic; no floating point enters.

## Scope

* The method and its constant are unchanged: Theorem D of the vendored `Zeta23` library yields
  `2 − 1/c₁* = 0.67250…`, and that remains the proportion the method gives.  What is new is that
  the repository states a proportion on the critical line with no `ε` and a decimal constant
  strictly above `2/3`.
* Still `liminf`-type statements: `T₀` is not effective.
* 80 % on the critical line remains open and is not claimed anywhere.

## Gates

* `lake build RiemannHypothesis.SixtySevenPercent` — succeeds, no `sorry`.
* `./scripts/audit.sh` — `OK`; the new claims are pinned in `scripts/revalidation.lean`.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-SIXTY-SEVEN-CRITICAL

A second pass, made against the compiled module rather than against this note.

* **Is the statement non-vacuous?**  `windowCount`, `windowCountOnLine`, `windowCountSimpleOnLine`
  and `windowCountOffLine` are the repository's existing counting functions (`Partial.lean`,
  `Zeta23Bridge.lean`), unchanged here; the new theorems are inequalities between them for all
  large `T`, with no hypothesis that could be unsatisfiable.  The claims are pinned in
  `scripts/revalidation.lean`, so a later weakening or renaming stops that file elaborating.
* **Is it stronger than what was already there?**  `0.67 > 2/3`, and the previous statements on
  the critical line all carried an `ε`.  It is weaker than the true constant `2 − 1/c₁* =
  0.67250…`, which is the ceiling of the method and is not claimed to be improved.
* **Is the numerical chain right?**  `tan(1/√2) = 0.8545137…`; the bound proved is
  `44√2/73 = 0.8524034…`, and `0.67` requires `50√2/83 = 0.8519568…`.  The comparison used in
  Lean is `44·83 = 3652 > 3650 = 50·73`, exact integer arithmetic.  `c₁* = 0.7532960… > 88/117 =
  0.7521367…` and `2 − 117/88 = 59/88 = 0.6704545… > 0.67`.
* **Is the quartic cosine bound genuine?**  It is proved, not assumed: the difference
  `1 − x²/2 + x⁴/24 − cos x` is shown monotone on `[0, ∞)` from `Real.sin_gt_sub_cube`, and it
  vanishes at `0`.  No numerical evaluation of `cos` is involved.
* **Proof hygiene.**  No `sorry` in the module; `#print axioms` on each new theorem returns
  exactly `propext`, `Classical.choice`, `Quot.sound`; no `axiom`, `native_decide` or
  `implemented_by` is used.
* **What is *not* claimed.**  Nothing about 80 % on the critical line, nothing effective in `T₀`,
  and no improvement to the analytic method itself.
