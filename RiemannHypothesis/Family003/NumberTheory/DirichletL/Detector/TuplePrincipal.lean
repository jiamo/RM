/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/TuplePrincipal.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.TuplePrincipal
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.TuplePrime

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem indexedCompensatedHigh_principal_continued {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x*globalClosedCorrection η S x w z)*
      ∏i,compensatedReplacement (coordV (Ideal.absNorm (P i).val) z)
        (coordW (Ideal.absNorm (P i).val) 1 w)
        (coordD (Ideal.absNorm (P i).val) (HeckeFamily.idealCoeff η (P i).val) 1 x)
        (idealMarkedClosed η (P i) x w z)
        (star (HeckeFamily.idealCoeff η (P i).val)*(Ideal.absNorm (P i).val:ℂ)^x)
        ((Ideal.absNorm (P i).val:ℂ)^(-w))/idealClosedCorrection η (P i) x w z := by
  have hs (i : Fin K) : Supported (P i).val := outside_prime_supported S hS.bad (P i) (hPS i)
  rw [indexedCompensatedHigh_principal η S P hP hs]
  have ht : ∀Q∈Finset.univ.image P,Q.val∉S := by
    intro Q hQ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hPS i
  rw [spectralCompensatedHigh_continued S hS (Finset.univ.image P) ht η x w z _ _ hx hw hz,
    Finset.prod_image hP.injOn]

end SevenEighths.ProbePhysical
end

end RiemannHypothesis.Family003
