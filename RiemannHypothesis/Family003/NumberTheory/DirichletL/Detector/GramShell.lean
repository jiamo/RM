/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramShell.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramShell
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.LowGramHeight
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramResidue
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical EisensteinSchwartzPoisson

def shellProfile (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ) : ℂ :=
  lowGramProfile W v x*star (lowGramProfile W v y)*paperRadialFourier U (T/(x*y))

lemma shellProfile_zero_left (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hx : W x=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hx]

lemma shellProfile_zero_right (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hy : W y=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hy]

theorem shellProfile_weighted_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
      ∀(W : ℝ→ℂ),(Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤B)→
      ∀(U : SchwartzMap ℝ ℂ)(v T x y : ℝ),0≤T→
        (1+T)^A*‖shellProfile W v U T x y‖≤
          C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := by
  obtain ⟨s,C,hC,hpaper⟩ := paperRadialFourier_euler_source_weighted_bound A 0
  refine ⟨s,(1+B/a)^2*(1+b^2)^A*C,by positivity,?_⟩
  intro W hs hW U v T x y hT
  by_cases hx : W x=0
  · rw [shellProfile_zero_left _ _ _ _ _ _ hx,norm_zero,mul_zero]
    positivity
  by_cases hy : W y=0
  · rw [shellProfile_zero_right _ _ _ _ _ _ hy,norm_zero,mul_zero]
    positivity
  have hxa := (hs hx).1
  have hya := (hs hy).1
  have hxb := (hs hx).2
  have hyb := (hs hy).2
  have hx0 := ha.trans_le hxa
  have hy0 := ha.trans_le hya
  have hxy : 0<x*y := mul_pos hx0 hy0
  have hxyb : x*y≤b^2 := by nlinarith [mul_le_mul hxb hyb hy0.le (hx0.le.trans hxb)]
  have ht : 0≤T/(x*y) := div_nonneg hT hxy.le
  have hp := hpaper U 0 (by omega) (T/(x*y)) ht
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hp
  have hscale : 1+T≤(1+b^2)*(1+T/(x*y)) := by
    have he : T=(x*y)*(T/(x*y)) := by field_simp
    have hbound := mul_le_mul_of_nonneg_right hxyb ht
    rw [←he] at hbound
    nlinarith [sq_nonneg b]
  have hp' : (1+T)^A*‖paperRadialFourier U (T/(x*y))‖≤
      (1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    calc
      _ ≤ ((1+b^2)*(1+T/(x*y)))^A*‖paperRadialFourier U (T/(x*y))‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale _) (norm_nonneg _)
      _ = (1+b^2)^A*((1+T/(x*y))^A*‖paperRadialFourier U (T/(x*y))‖) := by rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hwx : ‖lowGramProfile W v x‖≤1+B/a := by
    rw [lowGramProfile_norm W v x hx0]
    exact (div_le_div₀ hB (hW x) ha hxa).trans (by linarith)
  have hwy : ‖lowGramProfile W v y‖≤1+B/a := by
    rw [lowGramProfile_norm W v y hy0]
    exact (div_le_div₀ hB (hW y) ha hya).trans (by linarith)
  rw [shellProfile,norm_mul,norm_mul,norm_star]
  calc
    _ = (‖lowGramProfile W v x‖*‖lowGramProfile W v y‖)*
        ((1+T)^A*‖paperRadialFourier U (T/(x*y))‖) := by ring
    _ ≤ (1+B/a)^2*((1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul _ hp' (by positivity) (by positivity)
      nlinarith [mul_le_mul hwx hwy (norm_nonneg _) (by positivity : 0≤1+B/a)]
    _ = _ := by ring

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
