/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/Split.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.Split
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.Partition

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}
noncomputable local instance splitPhaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def residualBlock [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c0 : Eis) (R : Finset ι) : ℂ :=
  ∏ i ∈ R, (∏ k ∈ R.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 4)*
    residualPrimeScalar (p i) c0 (hp i) (hg i)

def markedBlock [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c0 : Eis) (P : Finset ι) : ℂ :=
  ∏ i ∈ P, (∏ k ∈ P.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 2)*
    markedPrimeScalar (p i) c0 (hp i) (hg i)

theorem activePhase_row_slot [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R P : Finset ι)
    (hd : Disjoint R P) (hu : R ∪ P = Finset.univ) :
    D.activePhase hp hg (fun i => if i ∈ R then 1 else 0) =
      residualBlock hp hg c0 R * markedBlock hp hg c0 P := by
  let l : ι → ℂ := fun i => if i ∈ R then residualPrimeScalar (p i) c0 (hp i) (hg i)
    else markedPrimeScalar (p i) c0 (hp i) (hg i)
  have he : D.activePhase hp hg (fun i => if i ∈ R then 1 else 0) =
      ∏ i, (∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^
        (if i ∈ R then 4 else 2))*l i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hr : i ∈ R
    · simp only [hr,ite_true,l]
      rw [controlled_residual_phase]
      ring
    · simp only [hr,ite_false,l]
      rw [controlled_marked_phase]
      ring
  rw [he, ordered_cross_partition _ l 4 2 R P hd hu,
    InverseMoment.row_slot_product_phase p hcop hg hprimary R P hd, mul_one]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [l,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun h => Finset.disjoint_left.mp hd h hi
    simp [l,hn]

end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
