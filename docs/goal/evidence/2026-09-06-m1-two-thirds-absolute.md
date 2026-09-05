# The two-thirds theorem in absolute form, and the audit of the trust it rests on

Date: 2026-09-06
Modules: `RiemannHypothesis/Zeta23Verification.lean`, `scripts/axiom_audit.lean`,
`scripts/list_theorems.lean`, `scripts/audit_coverage.py`, `scripts/conditional_theorems.lean`

## Why

The strongest results of this repository (`M1-TWO-THIRDS`, and everything derived from it:
`M2-CONREY`, `M2-METHOD-CEILING`, the eighty-percent routes) come from the vendored `Zeta23`
library, and the repository's only reason to trust it was `vendor/zeta23/AUDIT.md`, the vendored
library's own report.  Two independent things had never been checked here:

1. that the *statements* mean what they appear to mean — that `windowCount` is the classical
   zero-counting function `N` and not something smaller, and that the ratio `N₀*/N ≥ 2/3` is not
   vacuous;
2. that the *proofs* are clean in this repository's environment, not only in the vendored one.

## What was checked

### The axioms, re-run here

`lake env lean` on a file importing `Zeta23.Unconditional` and `RiemannHypothesis.Zeta23Bridge`:

```
'Zeta23.thmA₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmA₀_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmB₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmC₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmA₀_N0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Zeta23.thmA₀` is `thmA₁ zetaEF`, and `zetaEF : EF.EF_lit zetaZeroConfig` is a theorem, not an
assumption, so Theorem A carries no hypotheses.  This is now covered permanently rather than by a
one-off run: `scripts/axiom_audit.lean` walks the whole environment and collects the axioms of
**every** theorem of this repository — 2242 of them — and the dependency closure of each one runs
through the vendored proofs.

### The statements, read against Mathlib

`Zeta23.zerosIn T₁ T₂` is `{ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}`
and `Zeta23.zeroMult ρ` is `(analyticOrderAt riemannZeta ρ).toNat`, both directly against Mathlib;
`Ncount` sums the multiplicities over that set and `N0star` is the `ncard` of its on-line part.  So
Theorem A's left-hand side counts *with* multiplicity and its right-hand side counts *distinct*
points, which makes the normalization stronger than the usual `N₀(T)/N(T)`, not weaker.  The bridge
lemmas of `Zeta23Bridge.lean` (`windowCount_eq`, `windowCountOnLine_eq`, …) are `rfl`-level, so this
repository's counting functions are literally the vendored ones.

### The size of the denominator

Reading the definitions is not enough: `N₀* ≥ (2/3 − ε)·N` would also hold if `N` were eventually
zero.  `RiemannHypothesis/Zeta23Verification.lean` closes that gap by turning the ratio into an
absolute count, using the Riemann–von Mangoldt formula that the vendored library also proves
unconditionally (`Zeta23.riemannVonMangoldt_zeta`):

* `windowCount_sub_mainTerm_le` —
  `|N(T, 2T) − (T/2π)(log(T/2π) + 2log 2 − 1)| ≤ C log T` for all large `T`.  The main term is
  exactly the classical `N(2T) − N(T)`, so `windowCount` *is* the `N` of the literature;
* `eventually_windowCount_ge` — hence `N(T, 2T) ≥ (T/4π) log T` for all large `T`;
* `eventually_windowCountOnLine_ge` — Theorem A in absolute form: for all large `T` there are at
  least `(T/8π)·log T` **distinct** zeroes of `ζ` on the critical line with ordinate in `(T, 2T]`;
* `eventually_windowCountSimpleOnLine_ge` — the same count of *simple* zeroes on the line, from
  Theorem B.

The constants are deliberately lossy (half of the main term is thrown away so that the thresholds
stay explicit and the proof stays short): the true main term is `(T/2π)(log T − c₀)` with
`c₀ = log 2π + 1 − 2 log 2 ≈ 1.4516`, and the sharp form of the on-line bound would be
`(2/3 − ε)(T/2π)(log T − c₀)`.

## Adversarial revalidation: M1-TWO-THIRDS-ABSOLUTE

* **Could the new theorems be vacuous?**  No: they are `∀ᶠ T in atTop` statements with a
  non-trivial right-hand side, and `atTop` on `ℝ` is not the bottom filter.  Each bound is a lower
  bound on a natural-number cast, so a vacuous reading would need the *left*-hand side to be
  eventually non-positive, and `T/(8π)·log T → ∞`.
* **Do they assume anything?**  No hypotheses; the inputs are `two_thirds_on_critical_line`,
  `two_thirds_simple_on_critical_line` and `Zeta23.riemannVonMangoldt_zeta`, all unconditional.
  `scripts/conditional_theorems.lean` reports no new conditional theorem.
* **Are they really about `ζ`?**  `windowCount`, `windowCountOnLine`, `windowCountSimpleOnLine` are
  defined in `Zeta23Bridge.lean` from `nontrivialZeroSet` and `analyticOrderAt riemannZeta`, with no
  reference to any abstract configuration.
* **Axioms**: `propext`, `Classical.choice`, `Quot.sound` for all four results, checked both by the
  pinned `#print axioms` lines in `scripts/audit.sh` and by the exhaustive `scripts/axiom_audit.lean`.
* **Statement pins**: the three headline statements are written out in `scripts/revalidation.lean`
  with the repository's declarations as proof terms.

## Adversarial revalidation: M0-AUDIT-COVERAGE

* **Is the exhaustive audit actually able to fail?**  Checked with a positive control: a
  `theorem … := by sorry` was added to a leaf module, the library rebuilt, and the audit reported
  `NONSTANDARD RiemannHypothesis.audit_positive_control_tmp : [sorryAx]` and
  `AXIOM AUDIT: 2243 theorems checked, 1 outside the standard three`.  The control was then removed.
* **Does it cover what the hand list missed?**  The hand-maintained list in `scripts/audit.sh`
  checks 719 names; the library exports 2030 theorems under the filters of
  `scripts/list_theorems.lean` (2242 under the wider filter the audit itself uses).  Coverage of the
  hand list is 35.4 %; the exhaustive audit is at 100 % by construction and is wired into
  `scripts/audit.sh` as step 3b.  Step 3c additionally fails the audit if the hand list names a
  theorem the library no longer exports — four such stale names were found and fixed while writing
  the tool (three `RiemannHypothesisConjecture.*` names live in `Solution`, and one was a regex
  artefact).
* **Is the conditional-theorem classification exhaustive?**  The detector was widened in four ways:
  `Prop`-valued *structures, classes and inductives* now count as statements (previously only
  `def`/`opaque`); the vendored `Zeta23` library's own statements are scanned; Mathlib's
  `RiemannHypothesis` (for which `ZetaForm` is an `abbrev`) is included; and a hypothesis is
  discharged only by a proof of *that very proposition*, arguments included, rather than by any
  proof with the same head constant.  The output is byte-identical to the recorded
  `docs/goal/conditional-theorems.txt`: 36 conditional theorems, no `UNCLASSIFIED` entry.  Positive
  controls confirmed the three new powers: a probe theorem assuming `_root_.RiemannHypothesis` and a
  probe assuming a parameterized statement at an argument for which no proof exists are both
  reported, and were both invisible to the previous version.

## What this does not establish

Nothing here re-proves the vendored analytic work.  What is established is that the statements are
about Mathlib's `ζ`, that they are not vacuous, that they have the classical normalization, and
that every theorem of this repository — including all of those that depend on the vendored library —
depends on nothing but `propext`, `Classical.choice` and `Quot.sound`.  A reader who wants the
analytic argument checked independently still has the comparator route described in
`vendor/zeta23/AUDIT.md`.

## Addendum: how far the two-thirds theorem is from the conjecture

`RiemannHypothesis/EventualCountingCriterion.lean` answers, as a theorem, the question the
two-thirds theorem raises: what exactly is missing.  The naive answer — "raise the proportion to
`1`, then verify the low zeroes separately" — over-counts the work.  No verification of low zeroes
is needed, because an off-line zero is a permanent deficiency: it is missed by *every* window
`(0, T]` above its ordinate.

* `zetaStripForm_of_eventually_windowCountOnLine_eq` — if `N₀*(0,T) = N_d(0,T)` for all
  sufficiently large `T`, then every nontrivial zero of `ζ` is on the critical line;
* `zetaStripForm_iff_eventually_windowCountOnLine_eq` — the equivalence;
* `zetaStripForm_iff_eventually_windowCountOnLine_eq_windowCount` — the same with both sides
  counted with multiplicity, i.e. in the denominator the two-thirds theorem bounds (this form also
  forces every zero to be simple, which is what "counted with multiplicity on the right" means);
* `zetaStripForm_iff_eventually_windowCountDistinct_le` — the same in the shape the two-thirds
  theorem approximates: the conjecture is exactly the endpoint `c = 1` of the family
  `(c − ε)·N ≤ N₀*`, and `c = 2/3` is what is proved.

The step that makes the low zeroes unnecessary is `exists_offLine_pos_im_of_not_zetaStripForm`: if
the conjecture fails, some off-line zero has *positive* ordinate — `ζ` has no real zero in `(0,1)`
(`riemannZeta_ofReal_ne_zero_of_lt_one`) and the zero set is closed under conjugation
(`riemannZeta_conj_of_mem_strip`).

## Adversarial revalidation: M3-EVENTUAL-COUNTING-CRITERION

* **Is the hard direction really proved, or is the `iff` trivial?**  The direction
  `ZetaStripForm → …` is immediate.  The other direction is a genuine argument: it produces an
  off-line zero of positive ordinate, places it in the window `(0, T]` for one `T` beyond both the
  eventual threshold and its own ordinate, and derives a strict inequality of `ncard`s from the
  finiteness of the window (`finite_windowZeros`, from the vendored seam's `finite_window`).
  Deleting either the conjugation step or the "no real zero" step breaks the proof, since a zero
  with non-positive ordinate would sit in no window `(0, T]`.
* **Does it prove the conjecture?**  No.  Nothing in the file produces a term of `ZetaStripForm`;
  every statement is an implication or an equivalence, and `scripts/conditional_theorems.lean`
  continues to report no unproved statement being assumed here.
* **Is it new relative to `zeta_strip_iff_counting`?**  That criterion quantifies over *all*
  heights `T`; this one only over all sufficiently large `T`, which is the weaker hypothesis and
  the one an asymptotic method can hope to supply.
* **Axioms**: `propext`, `Classical.choice`, `Quot.sound`, checked by the pinned `#print axioms`
  lines and by the exhaustive audit; two of the four statements are pinned in
  `scripts/revalidation.lean`.
