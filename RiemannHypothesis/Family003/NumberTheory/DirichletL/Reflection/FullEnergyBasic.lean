/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/FullEnergyBasic.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.FullEnergyBasic
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.WholeTail
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.InactiveEnergy

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
noncomputable section

lemma norm_sq_le_retained (f g : ℂ) (E : ℝ) (_hE : 0≤E) (hf : ‖f-g‖≤E) :
    ‖f‖^2≤2*‖g‖^2+2*E^2 := by
  have hh : ‖f‖≤‖g‖+E := by
    calc
      _ = ‖g+(f-g)‖ := by congr 1;ring
      _ ≤ ‖g‖+‖f-g‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hf _
  have hsq := pow_le_pow_left₀ (norm_nonneg f) hh 2
  nlinarith [sq_nonneg (‖g‖-E)]

lemma row_energy_le_retained {α : Type*} (rows : Finset α) (f g : α→ℂ) (E : ℝ)
    (hE : 0≤E) (hf : ∀ k∈rows,‖f k-g k‖≤E) :
    (∑ k∈rows,‖f k‖^2)≤2*(∑ k∈rows,‖g k‖^2)+2*rows.card*E^2 := by
  calc
    _ ≤ ∑ k∈rows, (2*‖g k‖^2+2*E^2) := Finset.sum_le_sum (fun k hk => norm_sq_le_retained (f k) (g k) E hE (hf k hk))
    _ = _ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul];ring
end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003
