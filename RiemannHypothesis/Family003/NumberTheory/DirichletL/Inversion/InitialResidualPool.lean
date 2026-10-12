/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialResidualPool.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialResidualPool
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialExcludedPool
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindow

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialResidualPool
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open InverseInitialExcludedPool InverseInitialCommonTuples InverseInitialEnergyCallerWindow
local notation "O"=>ActualEisensteinCubic.O

theorem exists_original_complete_pool {κ:Type*}
    (q:ℕ)(Z r b cap Btree:ℝ)(hZ:0<Z)(hBtree:0≤Btree)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside (reflectionExcludedPrimes q) (P k)):
    ∃Dpool:ℕ,Btree*Z^(cap+1)≤Dpool ∧
      tupleColumns (originalOutside (originalSource Z r b) (reflectionExcludedPrimes q)) T P j⊆
        InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool:=by
  obtain ⟨D,hcover,hsize⟩:=exists_excluded_complete_pool (originalSource Z r b)
    (reflectionExcludedPrimes q) T P j (reflectionExcludedPrimes_prime q) hP hj hPE
    (originalSource_supported Z r b) Btree (Z^(cap+1)) hBtree (Real.rpow_nonneg hZ.le _)
  exact ⟨D,hsize Btree (Z^(cap+1)) hBtree le_rfl (Real.rpow_nonneg hZ.le _) le_rfl,hcover⟩

end SevenEighths.InverseInitialResidualPool

end

end RiemannHypothesis.Family003
