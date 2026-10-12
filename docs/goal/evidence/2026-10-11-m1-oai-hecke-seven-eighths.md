# Finite-order Hecke `L`-functions over `ℚ(√-3)`: no zeroes with `re s > 7/8` (openai/math family 003)

Date: 2026-10-11
Module: `RiemannHypothesis/HeckeSevenEighths.lean` (public endpoint), with the two further
absorbed upstream modules `RiemannHypothesis/Family003/NumberTheory/DirichletL/Hecke/ConditionalNonvanishing.lean`
and `RiemannHypothesis/Family003/NumberTheory/DirichletL/Hecke/Nonvanishing.lean`.
Row: `M1-OAI-HECKE-SEVEN-EIGHTHS` (rank 3, depends on `M1-OAI-DIRICHLET-SEVEN-EIGHTHS`).

## What is proved

| theorem | statement |
|---|---|
| `RiemannHypothesis.HeckeSevenEighths.LFunction_ne_zero_of_seven_eighths_lt_re` | `∀ (χ : HeckeFamily.Character) {s : ℂ}, (7/8 : ℝ) < s.re → ¬ (χ.residue = 1 ∧ s = 1) → HeckeFamily.LFunction χ s ≠ 0` |
| `RiemannHypothesis.HeckeSevenEighths.LFunction_ofResidue_ne_zero_of_seven_eighths_lt_re` | the same for `Character.ofResidue M hM χ hu`, a residue character `χ` of `O ⧸ M` trivial on units, with exception `¬ (χ = 1 ∧ s = 1)` |
| `RiemannHypothesis.HeckeSevenEighths.rayCharacter_LFunction_ne_zero_of_seven_eighths_lt_re` | the same for every ray-class character `χ ∈ rayCharacters M` modulo a non-zero ideal `M`, with exception `¬ (χ = 1 ∧ s = 1)` |

The first is the upstream comparator theorem
`OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re`
(`ComparatorChallenges/HeckeSevenEighths.json`, solution module
`OAI.NumberTheory.DirichletL.Hecke.Nonvanishing`), with the same statement; the other two are the
upstream corollaries in the same module.  The proofs are the upstream proofs, compiled against
this repository's pins as `RiemannHypothesis.Family003.…`.

## Correspondence with the upstream character model

The section *Correspondence* of `RiemannHypothesis/HeckeSevenEighths.lean` states, each as an
equation proved by `rfl`, that the native objects are the ones of the upstream comparator file:
`O = 𝓞 (CyclotomicField 3 ℚ)`, `coordinateElement x y = x + y ω`,
`elementCoeff χ z = χ.residue (z mod χ.modulus)`, `coefficients χ (a, b) = elementCoeff χ
(coordinateElement a b)`, `continuedLattice χ = HeckeTheta.latticeL (coefficients χ)`,
`LFunction χ s = continuedLattice χ s / 6`, `latticeL w s = π^s Γ(s)⁻¹ completed w s`,
`completed w = (pair w).Λ`; and that a `Character` is exactly the data
`⟨modulus, modulus ≠ ⊥, residue, residue trivial on units, period, 0 < period, period ∈ modulus⟩`.
`LFunction_eq` is also pinned in `scripts/revalidation.lean`.

The identification of `LFunction χ` with the Dirichlet series `∑ χ(𝔞) N𝔞^{-s}` is part of the
upstream development and is not restated here; the claim is about the upstream object, which is
the object of the upstream comparator statement.

## Closure

The import closure of the endpoint is the closure compiled for `M1-OAI-ZETA-SEVEN-EIGHTHS` and
`M1-OAI-DIRICHLET-SEVEN-EIGHTHS` (2958 modules under `RiemannHypothesis/Family003/`) plus the two
upstream modules `Hecke.ConditionalNonvanishing` and `Hecke.Nonvanishing`, both of which compile
with no host-compatibility edit (header `Host compatibility edits: none`).

## Adversarial revalidation: M1-OAI-HECKE-SEVEN-EIGHTHS

* `lake build +RiemannHypothesis.HeckeSevenEighths` succeeds; the module is imported from
  `RiemannHypothesis.lean`, so the default `lake build` compiles it.
* `#print axioms` on the three public theorems: `[propext, Classical.choice, Quot.sound]`
  (pinned list in `scripts/audit.sh`, and the exhaustive `scripts/axiom_audit.lean`).
* No `sorry`, `axiom`, `native_decide`, `bv_decide` or `implemented_by` in the endpoint or the
  two new absorbed modules; the upstream comparator stub is not imported.
* Faithfulness: the main statement is pinned in `scripts/revalidation.lean` with the hypothesis
  `7/8 < re s` and the upstream pole exclusion `¬ (χ.residue = 1 ∧ s = 1)` only — no detector
  certificate, analytic band or other assumed `Prop`.
* Non-vacuity: `Character` is inhabited (e.g. modulus `⊤`... any non-zero ideal with the trivial
  residue character and a period in it), and `s = 2` satisfies the hypotheses.
* Hypothesis hygiene (AGENTS.md): no new `Prop` is assumed; nothing is conditional.

## Open boundary

None for this row.  This is a zero-free half-plane for the Hecke `L`-functions of the single
field `ℚ(√-3)`; it is not the Riemann hypothesis and locates no zero on the critical line.
