/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/TupleKernel.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.TupleKernel
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.TupleRows

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def tuplePhysicalScalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))

lemma tuple_scaled_coefficient {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    tuplePhysicalScalar η p J*
      sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
        (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z=
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      tupleIndexedCoefficient η p J x w := by
  have ha := sourceMellinWeight_subset W0 W1 X Y Z (elementNorm (∏i∈J,p i))
    (elementNorm (∏i∈Finset.univ\J,p i)) hX hY hZ (tuple_norm_pos p hp J)
    (tuple_norm_pos p hp (Finset.univ\J))
    (star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))) x w z
  have hb := tuple_source_scalar η p hp J x w z
  unfold tuplePhysicalScalar tupleIndexedCoefficient
  linear_combination (-1:ℂ)^J.card*ha +
    (-1:ℂ)^J.card*sourceMellinWeight W0 W1 X Y Z x w z*hb

lemma compensatedRow_kernel_subsets {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (hp : ∀i,p i≠0) (u : O) (a : ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      (a*indexedCompensatedHigh η S p u x w z)=
    ∑J∈(Finset.univ:Finset (Fin K)).powerset,tuplePhysicalScalar η p J*
      ((a*markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z)*
        sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
          (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z) := by
  unfold indexedCompensatedHigh
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_scaled_coefficient η p hp J W0 W1 X Y Z hX hY hZ x w z
  linear_combination -a*markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z*he

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
