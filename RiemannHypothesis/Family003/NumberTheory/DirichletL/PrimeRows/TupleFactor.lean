/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/PrimeRows/TupleFactor.lean
  Original module: OAI.NumberTheory.DirichletL.PrimeRows.TupleFactor
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrimeRows.MarkedHolomorphic

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalCompensatedRow_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    physicalCompensatedRow S hS (Finset.univ.image P) hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,continuedCompensatedLocal η u (P i)
          (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  dsimp only
  unfold physicalCompensatedRow continuedCompensatedRow
  congr 2
  symm
  apply Finset.prod_bij (fun i _=>⟨P i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  · intro i _; exact Finset.mem_attach _ _
  · intro i _ j _ h; exact hP (congrArg Subtype.val h)
  · intro Q _
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp Q.property
    exact ⟨i,hi,Subtype.ext he⟩
  · intro i _; rfl

end SevenEighths.ProbeHighRowFamily
end

end RiemannHypothesis.Family003
