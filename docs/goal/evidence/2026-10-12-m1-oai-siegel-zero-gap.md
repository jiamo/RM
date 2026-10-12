# A uniform logarithmic gap for real zeroes of real primitive Dirichlet `L`-functions (openai/math family 003)

Date: 2026-10-12
Module: `RiemannHypothesis/SiegelZeroGap.lean` (public endpoint), with the absorbed closure of
upstream `OAI.NumberTheory.SiegelZeros.Main` under
`RiemannHypothesis/Family003/NumberTheory/SiegelZeros/` (306 modules) and
`RiemannHypothesis/Family003/External/PrimeNumberTheoremAnd/SiegelZeros/` (12 third-party
modules), plus the compatibility file `RiemannHypothesis/Family003/Compat/SiegelBackports.lean`.
Row: `M1-OAI-SIEGEL-ZERO-GAP` (rank 4, depends on `M1-OAI-HECKE-SEVEN-EIGHTHS`; both rows were
`TODO_READY` at the start of the delivery and lie on one dependency chain, so they were completed
together, in order, under §2.1 of `docs/goal/goal-prompt.md`).

## What is proved

| theorem | statement |
|---|---|
| `RiemannHypothesis.SiegelZeroGap.exists_absolute_real_zero_gap` | `∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → c ≤ (1 - β) * Real.log (q : ℝ)` |
| `RiemannHypothesis.SiegelZeroGap.dirichletRealZeroBound` | the same, with `0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0` as one hypothesis |

These are the two theorems of the upstream comparator challenge
`ComparatorChallenges/SiegelZeros` (`theorem_names`:
`OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap` and
`OAI.SiegelZeros.WeightedTorusJets.dirichletRealZeroBound_proof`, solution module
`OAI.NumberTheory.SiegelZeros.Main`, permitted axioms `propext`, `Classical.choice`,
`Quot.sound`).  The native statements are character-for-character the comparator statements
(checked against `openai-math/lean/ComparatorChallenges/SiegelZeros.lean` in the intake bundle);
they mention only Mathlib's `DirichletCharacter`, `DirichletCharacter.IsPrimitive` and
`DirichletCharacter.LFunction`.  The proofs are the upstream proofs, compiled against this
repository's pins (Lean v4.33.0, Mathlib `db584cd6`).

The constant `c` is absolute: it is chosen before `q`, `χ` and `β`.  Both parities of `χ` are
covered (there is no hypothesis on `χ (-1)`).

## How the closure was made to compile

The mechanical stage had already written the 306 upstream modules and the 12
PrimeNumberTheoremAnd `SiegelZeros/*` modules with provenance headers.  This delivery compiled the
whole import closure of `RiemannHypothesis.SiegelZeroGap` (322 modules of this repository on top
of the closure already compiled for the zeta / Dirichlet / Hecke rows) and repaired the modules
that did not compile at the host pin.  Each repair is recorded as a bullet in the edited file's
header (`Host compatibility edits: yes.`); 105 of the 318 Siegel-closure files carry `yes`.  The
kinds of edit:

* the same mechanical edits as in the rest of the family (`convert` with
  `(preTransparency := .instances)`; imports of `Compat.Backports` / `Compat.SiegelBackports` for
  upstream-named lemmas absent at the host pin, each proved there from host material);
* renames between the pins: `Ideal.isMaximal_under_of_isIntegral_of_isMaximal` →
  `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`,
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite` →
  `MvPolynomial.ringKrullDim_of_isNoetherianRing` (stated with `Nat.card`, so `Nat.card_fin` is
  added to the same `simp`), `MvPolynomial.monomial_mul_monomial` → `MvPolynomial.monomial_mul`,
  and a few earlier ones (TFAE renumberings, signature changes) recorded in their files;
* small `simp` repairs where the host simp set is weaker: `MvPolynomial.coeff_sum` and
  `coeff_X'` added (two files), a one-line `Finset.induction_on` fact evaluating a finite sum of
  derivations at a point (`FiniteTypeFieldModelEquiv.invariantDerivation_X`);
* `set_option backward.isDefEq.respectTransparency.types false` on five declarations that use
  `AlgebraicGeometry.StructureSheaf.stalkIso` (the host Mathlib declares `stalkIso` itself under
  this option, because its `Algebra` instance on the stalk is stated over `PrimeSpectrum.Top R`):
  `LaurentEvalOne.spec_stalk_isLocalRing`, `LaurentEvalOne.spec_localization_stalk_regular`,
  `AffineZeroScheme.spec_stalk_cotangent_eq_localization`,
  `AffineZeroScheme.affineZeroSchemeStalkEquiv`,
  `TorusJetZeroSchemeInclusion.localizationQuotientEquivStalkQuotient`;
* raised heartbeat limits, proofs unchanged: `synthInstance.maxHeartbeats 400000` on
  `finrank_degreePiece_pos_of_prime_variable_not_mem`, `component_functionField_finite`,
  `polynomialRectangleMap_eq_zero_iff`, `derivation_laurent_fraction_eq_zero`,
  `source_principal_existing_data_completion`, `source_master_principal_same_data`;
  `maxHeartbeats 1000000` on `smallerComponentTaylor_coeff`.

No statement of an upstream theorem was changed; no `sorry`, `axiom`, `native_decide`,
`bv_decide` or `implemented_by` was introduced.  `docs/family003/source-to-native-map.tsv` now
lists the 318 Siegel-closure modules as well (3263 entries in total).

## Adversarial revalidation: M1-OAI-SIEGEL-ZERO-GAP

* `lake build RiemannHypothesis.HeckeSevenEighths RiemannHypothesis.QuasiRiemann
  RiemannHypothesis.DirichletSevenEighths RiemannHypothesis.SiegelZeroGap` succeeds (exit 0); the
  module is imported from `RiemannHypothesis.lean`, so the default `lake build` compiles it.
* `#print axioms` on both public theorems: `[propext, Classical.choice, Quot.sound]` (pinned in
  `scripts/audit.sh`, and covered by the exhaustive `scripts/axiom_audit.lean`).
* Faithfulness: the statement of `exists_absolute_real_zero_gap` is pinned in
  `scripts/revalidation.lean`; it has exactly the comparator hypotheses (primitive, non-trivial,
  real-valued, `q ≥ 3`, `0 < β < 1`, `L(β, χ) = 0`) and no assumed `Prop`, detector certificate or
  analytic input.
* Non-vacuity: the hypotheses are satisfiable in shape (e.g. the primitive real character mod 4
  exists, and `β` ranges over all of `(0, 1)`); the content of the theorem is that its conclusion
  holds for every real zero in that range, with one constant.
* Hypothesis hygiene (AGENTS.md): no new `Prop` is assumed; nothing is conditional.
* Conditional-theorem audit (`scripts/conditional_theorems.lean`): the first full run of the
  audit with the absorbed family-003 closure in the build listed about 1400 *intermediate*
  upstream lemmas under `RiemannHypothesis/Family003/` as `UNCLASSIFIED`, because they take a
  `Prop`-valued structure of the upstream development as a hypothesis.  The detector now treats
  `Family003/` like the vendored `Zeta23` library: its `Prop`-valued definitions still count as
  statements (so a theorem of this repository assuming one is still reported), but its own
  theorems are not listed.  The public endpoints `QuasiRiemann`, `DirichletSevenEighths`,
  `HeckeSevenEighths` and `SiegelZeroGap` are outside `Family003/`, are scanned, and produce no
  entry: `docs/goal/conditional-theorems.txt` is unchanged.

## Open boundary

None for this row.  The theorem excludes Landau–Siegel zeroes for real primitive Dirichlet
characters; it is not the Riemann hypothesis, says nothing about complex zeroes, and locates no
zero on the critical line.
