/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/SelectedPrimeIndexed.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.SelectedPrimeSums

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma weighted_slot_bound_indexed (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀{ι : Type*} (f : ι→Ideal O), Function.Injective f →
    ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset ι), (∀i∈S,f i≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : ι→ℂ), (∀i∈S,‖G i‖≤K*(if f i∣U then (Ideal.absNorm (f i):ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑i∈S,‖W ((Ideal.absNorm (f i):ℝ)/P)*(Ideal.absNorm (f i):ℂ)^(z-1)*G i‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmain⟩ := weighted_slot_bound eps a b r d B K heps ha hb hd hB hK
  refine ⟨C,hC,?_⟩
  intro ι f hf U hU P hP S hS W hWS hWB G hG z hz
  let G' : Ideal O→ℂ := Function.extend f G (fun _=>0)
  have he (i : ι) : G' (f i)=G i := hf.extend_apply G (fun _=>0) i
  have hI (I : Ideal O) (hI : I∈S.image f) : I≠0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hS i hi
  have hg (I : Ideal O) (hI : I∈S.image f) :
      ‖G' I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    rw [he]
    exact hG i hi
  have hh := hmain U hU P hP (S.image f) hI W hWS hWB G' hg z hz
  rw [Finset.sum_image hf.injOn] at hh
  simpa only [he] using hh

end SevenEighths.ProbeSelectedPrimeSums
end

end RiemannHypothesis.Family003
