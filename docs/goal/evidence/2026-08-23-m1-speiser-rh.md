# M1-SPEISER-RH — the easy half of Speiser's theorem, quantitatively

Date: 2026-08-23
Module: `RiemannHypothesis/SpeiserRH.lean` (imported by `RiemannHypothesis.lean`)

## What is proved

* `windowZerosOffLine_eq_empty_of_zetaStripForm`, `windowCountOffLineMult_eq_zero_of_zetaStripForm`,
  `windowCountOnLineMult_eq_of_zetaStripForm` — under `ZetaStripForm` the window contains no
  off-line zero of `ζ`, so the off-line count with multiplicity is `0` and the on-line count is
  the whole of `N(T₁,T₂)`.
* `speiserOffLineTransfer_of_zetaStripForm` — hence the transfer `Prop` of
  M1-EIGHTY-CRITICAL-ROUTE / M1-SPEISER-ROLLE is *implied* by the hypothesis, trivially.  With
  `eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer` this places
  `SpeiserOffLineTransfer` strictly between "the hypothesis" and "86.864 % of the zeroes on the
  critical line".
* `xiDerivWindowCountOffLineMult_le_log_of_zetaStripForm` — **the easy half of Speiser's theorem
  in quantitative form**: under `ZetaStripForm`, `ξ′` has at most `C log T` zeroes off the
  critical line in the dyadic window `(T, 2T]`, counted with multiplicity.  The proof is the
  unconditional Rolle inequality `xiDerivWindowCountOffLineMult_le_windowCountOffLineMult` of
  M1-SPEISER-ROLLE with a vanishing right-hand side.
* `not_zetaStripForm_of_xiDeriv_offLine_gt` — the contrapositive: if for every `C` and every
  threshold some dyadic window contains more than `C log T` off-line zeroes of `ξ′`, the
  hypothesis fails.

## Scope — what is *not* claimed

* This is **weaker** than Speiser's theorem, whose easy half gives no off-line zero of `ξ′` at
  all.  The `O(log T)` is the error term of the two Riemann–von Mangoldt formulas and cannot be
  removed by this argument.
* The hard half of Speiser's theorem (from `ξ′` back to `ζ`) is not proved; it is exactly what
  `SpeiserOffLineTransfer` would supply, and that `Prop` has no term in this repository.
* Nothing here is unconditional information about `ζ`, and nothing here proves or disproves the
  Riemann hypothesis.

## Gates

* `lake build RiemannHypothesis.SpeiserRH` — succeeds, no `sorry`.
* `bash scripts/audit.sh` — `OK`; the three theorems are pinned in `scripts/revalidation.lean`
  and their axioms are printed by the audit.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-SPEISER-RH

* **Is the conclusion vacuous?**  The statement is conditional, and its hypothesis
  `ZetaStripForm` is not known to be true — so the theorem has no unconditional content, which is
  stated plainly above.  It is not *vacuously* proved, though: the proof genuinely uses the Rolle
  inequality, and the same statement with `ζ` in place of `ξ′` would be false in general.  The
  hypothesis is also not contradictory (no `False` is derived anywhere), so the implication is
  informative: its contrapositive is a usable falsification criterion.
* **Does the emptiness step really need the hypothesis?**  Yes.  `windowZerosOffLine` is the
  intersection of `windowZeros` (zeroes of `ζ` in the open strip with ordinate in the window)
  with `{re ρ ≠ 1/2}`; the hypothesis is applied to a member with `0 < re ρ < 1` and
  `ζ ρ = 0`, which are exactly the fields of `nontrivialZeroSet`.
* **Is `speiserOffLineTransfer_of_zetaStripForm` an abuse of the definition?**  No: the `Prop` is
  an inequality whose left side becomes `0` and whose right side is a nonnegative cast plus
  `0 · log T`; the witnesses `C = S = 0` are legitimate.  It is recorded precisely to show that
  the transfer hypothesis is *not* a weaker statement one may freely assume.
* **Proof hygiene.**  No `sorry`, `axiom`, `native_decide` or `implemented_by`; no `exact?`
  leftovers; the file is 100 lines.
* **Duplication check.**  Nothing is redeclared: the counting vocabulary comes from
  `EightyPercentMultiplicity.lean` and `SpeiserRolle.lean`, the inequality from
  `SpeiserEquivalence.lean`, and `ZetaStripForm` from `Defs.lean`.
