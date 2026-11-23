# Where the content of the alpo.ge proof lies

A read-only trace, made on 2026-11-23, through the live route of `everyCharacter` in the
alpo.ge tree (`vendor/alpo/lean/src`). Nothing was compiled. Every claim is marked
**[read]** (the code was read) or **[inferred]** (from definitions or names, without a full
walk). Paths are relative to `vendor/alpo/lean/src`. The tree has no licence, so this note
names declarations and files and does not quote code.

It answers J. L. Nielsen, *The Invalidity of Alpöge's Proof of the Riemann Hypothesis*
(dated 20 November 2026). He argues that the proof certifies only a tautology because:

* its geometry predicate is `True`;
* its lattice witnesses are copies, equal by `rfl`;
* its divisor height is overwritten by an explicit formula.

**Verdict.**

* His facts check out where they were checked.
* His inference does not. The geometric layer is carried but never consumed, so the proof
  cannot rest on it.
* The content is an inequality between a von Mangoldt-weighted prime sum and its main term,
  proved from Hermitian-lattice slope and pairing-norm estimates and then fed to Landau's
  window theorem.

## The final step

`zero_free_all_of_green_v_win`
(`Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12`)
is `zeroFreeAll_of_topG` applied to the package `forall_goal_of_shape_of_hyps … (shape_closed_link_n_of_green hG) trivial trivial h`. **[read]**

`zeroFreeAll_of_topG` (`Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:26`)
is `zeroFreeOn_of_tiedWin_cyc`
(`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean:90`), whose
three hypotheses are supplied as follows. **[read]**

| Hypothesis | Supplied by | Uses the package `TopG`? |
|---|---|---|
| `ChebyshevInequalityOnWindows` | `UpperTheory.Comparison₂.level_gm_le_on_family_scales`, a closed theorem | no |
| `FormB` | `UpperTheory.Comparison₂.formB`, a closed theorem: Landau's engine, window bound ⇒ zero-free half-plane | no |
| `ChebyshevInequalityAtWindowScale` | `TopG`, through `FamilyClassConnected`: for every small ε, families `Fm` with `ChainTied Fm … x` for all large `x` in the window | yes |

The chain ends in `Landau.zero_free_of_Chebyshev_growth`: the analytic half, which
`vendor/alpo/AnalyticBridge.lean` compiles in CI.

## (A) The closed half: `ChainTied` ⇒ a Chebyshev bound

* `level_gm_le_on_family_scales`
  (`Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean:28`) is
  `windowInequality_of_artinInputs (tiedCore_of_chainTied)`. **[read]**
* `tiedCore_of_chainTied` discards the conjuncts `TiePts`, `TieGlobal` and `TieLocal` of
  `ChainTied`. **[read]**
* `core_gm` (`…/PrimitiveCosets/CoreGm.lean:12`) gives `Λ.Gm x ≤ x^(1/2 + (eD+eL+7)ε)` through
  `Deduction.ch_core` (`…/DedekindLFunctions/LandauTheorems/ChCore.lean:343`), fed per word `u`
  by `Deduction.ch_top` (`…/LandauTheorems/ChTop.lean:37`). **[read]**
* The per-word input is `ASK(u) ≤ MAIN(u) + error`:
  * `IdentU` identifies `ASK` with a von Mangoldt-weighted prime sum and `MAIN` with the main
    term. **[read]**
  * The inequality is `each_unit_bound_statement`
    (`Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`). **[read]**
  * That theorem is real-number algebra over an abstract record. It holds for any record that
    satisfies the 11 clauses of `SizeData₂`. **[read]**
  * The clauses are defined in `Formalism/RankGapBounds/MeanBoundSecondForm.lean:111–163` and
    `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean`: `HidaSetting`, `DIV`,
    `EComp5`, `HComp`, `Count5`, `Slopes`, `QuotientSlopeBoundsWith`, `LossBounds`,
    `SlopeIneq`, `HHBound` and `FParams`.

## (B) What `TopG` supplies: families satisfying the 11 clauses

* `shape_closed_link_n_of_green` (`…/ThirdPlaceSeries/TopShape.lean:33`) ends with `topDesWin`
  (`Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean:11`). **[read]**
  * `topDesWin` assembles `GlobalTheoremInputs` (`LinkG ∧ LinkS ∧ LinkIRR ∧ LinkDIV ∧ LinkMu`).
  * It then applies the global link: `link_gl` → … → `linkGLOBAL_of`
    (`Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:853`).
* `linkGLOBAL_of` builds the record `Dd := M.data …` (same file, line 464) and proves the 11
  clauses. **[read]**
  * The record's fields are read from the family's lattice data: `h := div.h`,
    `muN := (div.Nu u).mu`, `muCC := div.RR.muDual`, `Ga` and `Fo` from `SizeData₂`.
  * `ASK` is the arithmetic sum.
  * The central clauses:

| Clause | Source |
|---|---|
| `SlopeIneq` | `data_SlopeIneq` (line 699), from `FrameF`: a Hermitian-lattice slope inequality, `sFrame(Nu, h) − log #W − … ≤ muDual` |
| `DIV` | `data_DIV` (line 580), from `LinkDIV`: `muDual + div.h u − Fo ≤ MAIN u + err` |
| `LossBounds` | `ASK − Ga ≤ LoP`, from `losses_family_of_division_side`, `slope_loss_lemma_family`, `askIsF` |
| `Count5`, `Slopes`, `QuotientSlopeBoundsWith` | `CountF`, `SlopesMF`, `SlopesNF` |

* `LinkDIV` comes from `closed_linkDIVt_of_closed_bridge_kernel`
  (`…/ThirdPlaceSeries/DIVRecBridgeSel.lean:197`) and `linkDIVt_closedK`
  (`Formalism/LocalToGlobal/Divisibility/RecBridgeSel.lean:369`). **[read]**
* Its source `DivClausesR` (`Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:184`,
  `divClausesR_of`) has Arakelov/Hermitian content **[read]**:
  * the pairing lands in the dual lattice;
  * operator norms at the infinite places are bounded;
  * the slope of the shifted lattice follows from local valuations.

  These are proved from `DivInputsR` (valuation lower bounds) and log operator-norm bounds
  along a chain of matrices.
* That `linkDIVt_closedK` reaches `divClausesR_of` was **not walked**. **[inferred]**

Not followed down to Mathlib: `FrameF`, `DivInputsR`, `CountF` and the rest span thousands of
files. This is where the arithmetic content of the proof lies, and the next thing to map.

## Nielsen's four points

1. **The geometry predicate is `True`.** Correct. `anyGeometry` is `fun _ _ _ => True`
   (`Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:19`) and is
   used 118 times in 24 files. **[read]**
   * `GeoCl` occurs on 6 lines: its definition, its two constructors, `geoCl`, `geoCl_of`, and
     one `GeoCl.step` (`NotGeoClFalse.lean:21–28`,
     `DivisionGeometryScalarsTransferSetDivision.lean:106`). No proof does case analysis or
     induction on it. **[read]**
   * The record `M.data` reads no geometric proof, and `tiedCore_of_chainTied` drops the tie
     conjuncts. **[read]**
   * A proposition that is never eliminated contributes nothing to a conclusion. So the
     geometry is dead weight, not a hidden assumption.
2. **The lattice witnesses hold by `rfl`.** Not re-checked here. It concerns the same unused
   geometric layer.
3. **The height is overwritten by a formula.** Correct.
   * `setDiv` overwrites `div.h`
     (`Development/AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean:25`),
     with `ht := hExpl6 …` (line 379) and `h_eq := fun _ => rfl` (line 400). **[read]**
   * That this constructor is the one on the live route is taken from Nielsen. **[inferred]**
   * But `h` cancels by design: it enters `DIV` as `+h` and `SlopeIneq`/`HHBound` as `−h`.
     `ScaleFree` (`Formalism/SizeWindowBrackets/SBrDiv.lean:325`) states the invariance of the
     clauses under `h − c`, `muCC + c`. **[read the statement; its proof not checked]**
   * The derived bound `ASK ≤ MAIN + err` does not mention `h`.
   * Choosing `h := hExpl6` is a choice of gauge, not a circularity. The slope inequality and
     the `DIV` bound must both be proved for that same `h`, and their sum is an inequality
     between a prime sum and its main term.
4. **Two shape inputs are `trivial`.** Correct.
   * They are the `V` and `NR` slots of `TopShapeAlt` (`TopShapeAlt.lean:24`, fields at lines
     27 and 61). `shape_closed_link_n_of_green` sets both to `True` in its own statement and
     never uses them. **[read]**
   * They are unused slots, not discharged requirements.

The paper's title claim, that the release "certifies only the tautology RiemannHypothesis =
RiemannHypothesis", is a type error. The kernel checks a closed term of Mathlib's
`RiemannHypothesis` with only `propext`, `Classical.choice` and `Quot.sound`, and the paper
itself (§12) finds no axiom, `sorry`, `native_decide`, `unsafe` or `opaque` declaration.

Whether the arithmetic layer (B) is correct is what the Lean kernel checked (independently
reproduced, `vendor/alpo/README.md`). This note locates that layer; it does not re-derive it.
