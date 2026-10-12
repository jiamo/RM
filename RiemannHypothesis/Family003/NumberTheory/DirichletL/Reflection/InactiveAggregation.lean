/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/InactiveAggregation.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.InactiveAggregation
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.OriginalTransport
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem inactive_slot_mass {ι : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hinj : Function.Injective P.ideal) (L : Finset ι) (H : ℝ)
    (hH : ∀ i∈L, (Ideal.absNorm (P.ideal i):ℝ)≤H) :
    (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹‖)≤256*(columnDyadicLength H+1:ℝ) := by
  have he : (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹‖)=
      ∑ I∈L.image P.ideal, 1/(Ideal.absNorm I:ℝ) := by
    rw [Finset.sum_image hinj.injOn]
    simp only [norm_inv,Complex.norm_natCast,one_div]
  rw [he]
  apply finite_inverse_norm_sum
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact NeZero.ne (P.ideal i)
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hH i hi

theorem inactive_slot_mass_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (P : PrimeFamily ι),
      Function.Injective P.ideal → ∀ (L : Finset ι) (H : ℝ), 1≤H →
      (∀ i∈L, (Ideal.absNorm (P.ideal i):ℝ)≤H) →
      (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹‖)≤C*H^ε := by
  refine ⟨256*(2+(ε*Real.log 2)⁻¹),by positivity,?_⟩
  intro ι _ P hinj L H hH hnorm
  exact (inactive_slot_mass P hinj L H hnorm).trans
    (by simpa only [mul_assoc,one_div] using (mul_le_mul_of_nonneg_left
      (columnDyadicLength_small_power ε hε H hH) (by norm_num : (0:ℝ)≤256)))

theorem original_pool_choice_count (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (R Q Q₀ : Ideal Eis), R≠0 → Q≠0 →
      (Fintype.card (FreeReflection.pool R Q Q₀→Fin 6):ℝ)^2≤C*(Ideal.absNorm (R*Q):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := completed_branch_count_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro R Q Q₀ hR hQ
  let (P : FreeReflection.pool R Q Q₀) : P.val.IsMaximal := FreeReflection.pool_maximal R Q Q₀ P
  have hh := hbound (R*Q) (mul_ne_zero hR hQ) (fun P : FreeReflection.pool R Q Q₀ => P.val)
    Subtype.val_injective (FreeReflection.pool_divides R Q Q₀ hR hQ)
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,← pow_mul,
    Nat.mul_comm (Fintype.card (FreeReflection.pool R Q Q₀)) 2] using hh
end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
