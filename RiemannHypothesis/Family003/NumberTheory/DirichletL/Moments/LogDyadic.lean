/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/LogDyadic.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.LogDyadic
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SectorLocalization
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondWholeKernel
import RiemannHypothesis.Family003.Compat.NormNumIntToNat
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

def logAnnulus (x : ℝ) : ℂ := annulus (Real.exp x)

theorem logAnnulus_smooth : ContDiff ℝ ∞ logAnnulus :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logAnnulus_support : Function.support logAnnulus ⊆ Set.Icc (-Real.log 4) 0 := by
  intro x hx
  have hn : annulus (Real.exp x)≠0 := by simpa only [Function.mem_support,logAnnulus,ne_eq,Complex.ofReal_eq_zero] using hx
  have hlo : 1/4<Real.exp x := lt_of_not_ge (fun h=>hn (annulus_zero_low _ h))
  have hhi : Real.exp x<1 := lt_of_not_ge (fun h=>hn (annulus_zero_high _ h))
  constructor
  · have hh := Real.strictMonoOn_log (show 1/4∈Set.Ioi (0:ℝ) by norm_num)
      (Real.exp_pos x) hlo
    rw [Real.log_exp,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hh
    exact hh.le
  · exact (Real.exp_lt_one_iff.mp hhi).le

theorem logAnnulus_compact : HasCompactSupport logAnnulus :=
  HasCompactSupport.intro (isCompact_Icc) (fun x hx=>by
    by_contra hn
    exact hx (logAnnulus_support hn))

theorem logAnnulus_norm (x : ℝ) : ‖logAnnulus x‖≤1 := by
  rw [logAnnulus,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (annulus_bounds _).1]
  exact (annulus_bounds _).2

theorem logAnnulus_log (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window (n : ℤ) (q : ℝ) (hq : 0<q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

theorem actual_product_windows (k H a b : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b) (n : Fin 4→ℤ) :
    ((dyadicWeight (n 0) k*dyadicWeight (n 1) H*
      dyadicWeight (n 2) a*dyadicWeight (n 3) b:ℝ):ℂ)=
      windows (fun _=>logAnnulus) k H a b
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp only [Complex.ofReal_mul,actual_dyadic_log_window (n 0) k hk,
    actual_dyadic_log_window (n 1) H hH,actual_dyadic_log_window (n 2) a ha,
    actual_dyadic_log_window (n 3) b hb,windows]

end SevenEighths.CenteredMomentLogDyadic

end

end RiemannHypothesis.Family003
