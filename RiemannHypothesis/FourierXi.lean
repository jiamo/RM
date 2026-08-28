/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ThetaW
import RiemannHypothesis.Xi

/-!
# Riemann's Fourier representation of `Ξ`, and the identification `H₀ = Ξ`

This file proves the classical integral representation

`Ξ(z) = 1/2 - (4z² + 1) ∫₀^∞ W(u) cos(2uz) du`,  `W(u) = e^u ω(e^{4u})`,

and deduces from it the identity relating the Riemann `Ξ` function to the `t = 0` member of
the de Bruijn–Newman family `H_t(z) = ∫₀^∞ e^{tu²} Φ(u) cos(uz) du`:

`H₀(z) = Ξ(z/2) / 8`.

Consequently the Riemann hypothesis is *equivalent*, with no further hypotheses, to the
statement that every zero of `H₀` is real.

The proof has two halves.

* The `Ξ` side (`riemannXi_eq_integral`): Mathlib's `completedRiemannZeta₀` is by definition
  the Mellin transform of the modified theta kernel of the abstract functional-equation
  machinery; folding the part of the Mellin integral over `(0,1)` onto `(1,∞)` with the
  functional equation and substituting `x = e^{4u}` turns it into the cosine integral above.
* The `H₀` side (`dbnH_zero_eq_integral`): the weight satisfies `Φ = (W'' - W)/8`, and
  `u ↦ W'(u) cos(uz) + z W(u) sin(uz)` is an explicit antiderivative of
  `(W'' + z²W) cos(uz)`, so that integration by parts leaves only the boundary term
  `-W'(0) = 1/2`.
-/

noncomputable section

open Set MeasureTheory Filter Complex
open scoped Topology Real

namespace RiemannHypothesis

/-! ### The `Ξ` side -/

open HurwitzZeta in
/-- The modified theta kernel of Mathlib's abstract functional-equation machinery, whose Mellin
transform is `Λ₀`. -/
noncomputable def fmod : ℝ → ℂ := (hurwitzEvenFEPair 0).f_modif

open HurwitzZeta in
lemma fmod_of_one_lt {x : ℝ} (hx : 1 < x) : fmod x = 2 * (thetaOmega x : ℂ) := by
  have h0 : (0 : ℝ) < x := lt_trans one_pos hx
  have : fmod x = ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1 := by
    simp [fmod, WeakFEPair.f_modif, hurwitzEvenFEPair, Set.indicator_of_mem, hx,
      Set.notMem_Ioo_of_ge hx.le]
  rw [this, evenKernel_zero_eq x h0]
  push_cast
  ring

open HurwitzZeta in
/-- The functional equation of the modified kernel, `f(1/x) = √x f(x)`. -/
lemma fmod_inv {x : ℝ} (hx : 0 < x) : fmod x⁻¹ = ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * fmod x := by
  have hg : (hurwitzEvenFEPair 0).g_modif = (hurwitzEvenFEPair 0).f_modif := by
    have h : (hurwitzEvenFEPair 0).symm.f_modif = (hurwitzEvenFEPair 0).g_modif := rfl
    rw [hurwitzEvenFEPair_zero_symm] at h
    exact h.symm
  have h := (hurwitzEvenFEPair 0).hf_modif_FE x hx
  rw [hg] at h
  simp only [fmod, one_div] at h ⊢
  simpa [hurwitzEvenFEPair, smul_eq_mul] using h

open HurwitzZeta in
lemma mellinConvergent_fmod (w : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) • fmod x) (Ioi 0) :=
  ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin w).1


private lemma inter_Ioi_zero_Ici_one : Ioi (0 : ℝ) ∩ Ici 1 = Ici 1 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le zero_lt_one h, h⟩⟩

private lemma inter_Ioi_zero_Ioi_one : Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioi]
  exact ⟨fun h => h.2, fun h => ⟨lt_trans zero_lt_one h, h⟩⟩

/-- The Mellin transform of a function supported in `(1, ∞)` is an integral over `(1, ∞)`. -/
lemma mellin_indicator_Ioi_one (h : ℝ → ℂ) (w : ℂ) :
    mellin ((Ioi (1 : ℝ)).indicator h) w = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) * h x := by
  rw [mellin]
  have key : ∀ x : ℝ, (x : ℂ) ^ (w - 1) • (Ioi (1 : ℝ)).indicator h x
      = (Ioi (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ) ^ (w - 1) * h x) x := by
    intro x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  simp_rw [key]
  rw [MeasureTheory.setIntegral_indicator (measurableSet_Ioi (a := (1 : ℝ))),
    inter_Ioi_zero_Ioi_one]

open HurwitzZeta in
/-- Reflecting the part of the Mellin integral over `(0, 1]` to `(1, ∞)` using the functional
equation of the modified kernel. -/
lemma mellin_fmod_lower (w : ℂ) :
    mellin ((Ioc (0 : ℝ) 1).indicator fmod) (-w)
      = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1 / 2) * fmod x := by
  rw [← mellin_comp_inv ((Ioc (0 : ℝ) 1).indicator fmod) w, mellin]
  have key : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (w - 1) • (Ioc (0 : ℝ) 1).indicator fmod x⁻¹
      = (Ici (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ) ^ (w - 1 / 2) * fmod x) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hxne : (x : ℂ) ≠ 0 := by simpa using hx0.ne'
    rcases le_or_gt 1 x with h1 | h1
    · have hmem : x⁻¹ ∈ Ioc (0 : ℝ) 1 :=
        ⟨by positivity, by rw [inv_le_one_iff₀]; right; exact h1⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_Ici.mpr h1), fmod_inv hx0,
        smul_eq_mul, ← mul_assoc, Complex.ofReal_cpow hx0.le, ← Complex.cpow_add _ _ hxne,
        show (w - 1 + ((1 / 2 : ℝ) : ℂ) = w - 1 / 2) from by push_cast; ring]
    · have hmem : x⁻¹ ∉ Ioc (0 : ℝ) 1 := by
        intro hc
        rcases inv_le_one_iff₀.mp hc.2 with hle | hle
        · exact absurd hle (not_le.2 hx0)
        · exact absurd hle (not_le.2 h1)
      have hnot : x ∉ Ici (1 : ℝ) := by simp only [Set.mem_Ici, not_le]; exact h1
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hnot, smul_zero]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi key,
    MeasureTheory.setIntegral_indicator (measurableSet_Ici (a := (1 : ℝ))),
    inter_Ioi_zero_Ici_one, MeasureTheory.integral_Ici_eq_integral_Ioi]

open HurwitzZeta in
/-- Folding the Mellin integral of the modified kernel onto `(1, ∞)`. -/
lemma mellin_fmod_eq (w : ℂ) :
    mellin fmod w = ∫ x in Ioi (1 : ℝ), ((x : ℂ) ^ (w - 1) + (x : ℂ) ^ (-w - 1 / 2)) * fmod x := by
  have hIA : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (w - 1) • (Ioi (1 : ℝ)).indicator fmod x) (Ioi 0) := by
    refine ((mellinConvergent_fmod w).indicator
      (measurableSet_Ioi (a := (1 : ℝ)))).congr_fun ?_ measurableSet_Ioi
    intro x _
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hIB : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (w - 1) • (Ioc (0 : ℝ) 1).indicator fmod x) (Ioi 0) := by
    refine ((mellinConvergent_fmod w).indicator
      (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))).congr_fun ?_ measurableSet_Ioi
    intro x _
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hsplit : mellin fmod w =
      mellin ((Ioi (1 : ℝ)).indicator fmod) w + mellin ((Ioc (0 : ℝ) 1).indicator fmod) w := by
    rw [mellin, mellin, mellin, ← MeasureTheory.integral_add hIA hIB]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rcases le_or_gt x 1 with h1 | h1
    · have hnot : x ∉ Ioi (1 : ℝ) := by simp only [Set.mem_Ioi, not_lt]; exact h1
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx0, h1⟩)]
      simp
    · have hnot : x ∉ Ioc (0 : ℝ) 1 := by
        simp only [Set.mem_Ioc, not_and, not_le]
        exact fun _ => h1
      rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h1), Set.indicator_of_notMem hnot]
      simp
  have hB := mellin_fmod_lower (-w)
  rw [neg_neg] at hB
  rw [hsplit, mellin_indicator_Ioi_one, hB]
  have hI1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * fmod x) (Ioi 1) := by
    have h := (mellinConvergent_fmod w).mono_set (Set.Ioi_subset_Ioi zero_le_one)
    simpa [smul_eq_mul] using h
  have hI2 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-w - 1 / 2) * fmod x) (Ioi 1) := by
    have h := (mellinConvergent_fmod (-w + 1 / 2)).mono_set (Set.Ioi_subset_Ioi zero_le_one)
    rw [show (-w + 1 / 2 - 1 : ℂ) = -w - 1 / 2 from by ring] at h
    simpa [smul_eq_mul] using h
  rw [← MeasureTheory.integral_add hI1 hI2]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- The completed zeta function `Λ₀` as an integral over `(1, ∞)` against the theta series.
This is the classical formula
`Λ₀(s) = ∫₁^∞ (x^{s/2-1} + x^{-s/2-1/2}) · 2ω(x) dx / 2`, obtained by folding the Mellin
integral of the modified theta kernel. -/
theorem completedRiemannZeta₀_eq_integral (s : ℂ) :
    completedRiemannZeta₀ s =
      ∫ x in Ioi (1 : ℝ), ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ (-s / 2 - 1 / 2)) *
        (thetaOmega x : ℂ) := by
  have h : completedRiemannZeta₀ s = mellin fmod (s / 2) / 2 := rfl
  rw [h, mellin_fmod_eq (s / 2)]
  rw [← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [fmod_of_one_lt hx]
  have : (-(s / 2) - 1 / 2 : ℂ) = -s / 2 - 1 / 2 := by ring
  rw [this]
  ring

/-! ### The substitution `x = e^{4u}` -/

lemma ofReal_exp_cpow (t : ℝ) (v : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ v = Complex.exp (t * v) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le)]

lemma image_exp_Ici : (fun u : ℝ => Real.exp (4 * u)) '' Ici 0 = Ici 1 := by
  ext y
  simp only [Set.mem_image, Set.mem_Ici]
  constructor
  · rintro ⟨u, hu, rfl⟩
    calc (1 : ℝ) = Real.exp 0 := by simp
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  · intro hy
    refine ⟨Real.log y / 4, ?_, ?_⟩
    · have := Real.log_nonneg hy; linarith
    · rw [show 4 * (Real.log y / 4) = Real.log y by ring, Real.exp_log (by linarith)]

lemma image_exp_Ioi : (fun u : ℝ => Real.exp (4 * u)) '' Ioi 0 = Ioi 1 := by
  ext y
  simp only [Set.mem_image, Set.mem_Ioi]
  constructor
  · rintro ⟨u, hu, rfl⟩
    calc (1 : ℝ) = Real.exp 0 := by simp
      _ < _ := Real.exp_lt_exp.2 (by linarith)
  · intro hy
    refine ⟨Real.log y / 4, ?_, ?_⟩
    · have := Real.log_pos hy; linarith
    · rw [show 4 * (Real.log y / 4) = Real.log y by ring, Real.exp_log (by linarith)]

lemma thetaOmega_eq_wFun {x : ℝ} (hx : 0 < x) :
    thetaOmega x = wFun (Real.log x / 4) * Real.exp (-(Real.log x / 4)) := by
  have h := wFun_eq (Real.log x / 4)
  rw [show 4 * (Real.log x / 4) = Real.log x by ring, Real.exp_log hx] at h
  rw [h, mul_right_comm, ← Real.exp_add]
  simp

lemma continuousOn_thetaOmega : ContinuousOn thetaOmega (Ioi 0) := by
  have hc : ContinuousOn
      (fun x : ℝ => wFun (Real.log x / 4) * Real.exp (-(Real.log x / 4))) (Ioi 0) := by
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    have hl : ContinuousAt (fun x : ℝ => Real.log x / 4) x :=
      (Real.continuousAt_log (ne_of_gt hx)).div_const 4
    exact (continuous_wFun.continuousAt.comp hl).mul (Real.continuous_exp.continuousAt.comp hl.neg)
  exact hc.congr (fun x hx => thetaOmega_eq_wFun hx)

open HurwitzZeta in
lemma integrableOn_cpow_mul_fmod (w : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ w * fmod x) (Ioi 1) := by
  have h := (mellinConvergent_fmod (w + 1)).mono_set (Set.Ioi_subset_Ioi zero_le_one)
  rw [show (w + 1 - 1 : ℂ) = w from by ring] at h
  simpa [smul_eq_mul] using h

open HurwitzZeta in
lemma integrableOn_cpow_mul_thetaOmega (w : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ w * (thetaOmega x : ℂ)) (Ioi 1) := by
  have h : IntegrableOn (fun x : ℝ => (1 / 2 : ℂ) * ((x : ℂ) ^ w * fmod x)) (Ioi 1) :=
    (integrableOn_cpow_mul_fmod w).const_mul (1 / 2 : ℂ)
  refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [fmod_of_one_lt hx]
  ring

/-- The substitution `x = e^{4u}` turns the integral over `(1, ∞)` into a cosine integral. -/
theorem integral_Ioi_one_eq_cos_integral (z : ℂ) :
    (∫ x in Ioi (1 : ℝ), ((x : ℂ) ^ (xiPoint z / 2 - 1) + (x : ℂ) ^ (-(xiPoint z) / 2 - 1 / 2)) *
        (thetaOmega x : ℂ))
      = 8 * ∫ u in Ioi (0 : ℝ), (wFun u : ℂ) * Complex.cos (2 * u * z) := by
  set S : ℂ := xiPoint z with hSdef
  have hS : S = 1 / 2 + z * I := rfl
  set F : ℝ → ℝ := fun u : ℝ => Real.exp (4 * u) with hF
  set g : ℝ → ℂ := fun x : ℝ =>
    ((x : ℂ) ^ (S / 2 - 1) + (x : ℂ) ^ (-S / 2 - 1 / 2)) * (thetaOmega x : ℂ) with hgdef
  -- the pointwise identity after substitution
  have hkey : ∀ u : ℝ, (4 * Real.exp (4 * u)) • (g ∘ F) u
      = 8 * ((wFun u : ℝ) : ℂ) * Complex.cos (2 * u * z) := by
    intro u
    have hw : ((wFun u : ℝ) : ℂ)
        = Complex.exp ((u : ℂ)) * ((thetaOmega (Real.exp (4 * u)) : ℝ) : ℂ) := by
      rw [wFun_eq u]
      push_cast
      ring
    set A : ℂ := Complex.exp (2 * (u : ℂ) * z * I) with hA
    set B : ℂ := Complex.exp (-(2 * (u : ℂ) * z) * I) with hB
    have h1 : ((Real.exp (4 * u) : ℝ) : ℂ) ^ (S / 2 - 1) = Complex.exp (-3 * (u : ℂ)) * A := by
      rw [ofReal_exp_cpow, hA, ← Complex.exp_add]
      congr 1
      rw [hS]
      push_cast
      ring
    have h2 : ((Real.exp (4 * u) : ℝ) : ℂ) ^ (-S / 2 - 1 / 2) = Complex.exp (-3 * (u : ℂ)) * B := by
      rw [ofReal_exp_cpow, hB, ← Complex.exp_add]
      congr 1
      rw [hS]
      push_cast
      ring
    have h3 : Complex.exp (4 * (u : ℂ)) * Complex.exp (-3 * (u : ℂ)) = Complex.exp (u : ℂ) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hcos : Complex.cos (2 * (u : ℂ) * z) = (A + B) / 2 := by
      rw [hA, hB, Complex.cos]
    have h4 : ((4 * Real.exp (4 * u) : ℝ) : ℂ) = 4 * Complex.exp (4 * (u : ℂ)) := by
      push_cast
      rfl
    simp only [Function.comp_apply, hF, hgdef, Complex.real_smul, hw, hcos, h1, h2]
    rw [h4]
    linear_combination (4 * (A + B) * ((thetaOmega (Real.exp (4 * u)) : ℝ) : ℂ)) * h3
  have hfc : ContinuousOn F (Ici 0) := by
    have : Continuous F := by fun_prop
    exact this.continuousOn
  have hft : Tendsto F atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 4))
  have hff' : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt F (4 * Real.exp (4 * x)) (Ioi x) x := by
    intro x _
    have h : HasDerivAt F (Real.exp (4 * x) * 4) x :=
      (Real.hasDerivAt_exp (4 * x)).comp x (((hasDerivAt_id x).const_mul 4).congr_deriv (by ring))
    exact (h.congr_deriv (by ring)).hasDerivWithinAt
  have hg_cont : ContinuousOn g (F '' Ioi 0) := by
    rw [hF, image_exp_Ioi]
    have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Set.Ioi_subset_Ioi zero_le_one
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.add ?_ ?_ <;>
      · refine ContinuousOn.cpow_const ?_ ?_
        · exact Complex.continuous_ofReal.continuousOn
        · intro x hx
          exact Or.inl (by simpa using (lt_trans zero_lt_one hx))
    · exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_thetaOmega.mono hsub)
  have hg1 : IntegrableOn g (F '' Ici 0) := by
    rw [hF, image_exp_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have hA := integrableOn_cpow_mul_thetaOmega (S / 2 - 1)
    have hB := integrableOn_cpow_mul_thetaOmega (-S / 2 - 1 / 2)
    refine IntegrableOn.congr_fun (hA.add hB) ?_ measurableSet_Ioi
    intro x _
    simp only [Pi.add_apply, hgdef]
    ring
  have hg2 : IntegrableOn (fun u : ℝ => (4 * Real.exp (4 * u)) • (g ∘ F) u) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hcm : IntegrableOn
        (fun u : ℝ => 8 * ((wFun u : ℂ) * Complex.cos (u * (2 * z)))) (Ioi 0) :=
      (integrableOn_wFun_mul_cos (2 * z)).const_mul 8
    refine IntegrableOn.congr_fun hcm ?_ measurableSet_Ioi
    intro u _
    dsimp only
    rw [hkey u, show ((u : ℂ) * (2 * z)) = 2 * (u : ℂ) * z from by ring]
    ring
  have hmain := MeasureTheory.integral_comp_smul_deriv_Ioi hfc hft hff' hg_cont hg1 hg2
  have hF0 : F 0 = 1 := by simp [hF]
  rw [hF0] at hmain
  rw [← hmain]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun u _ => hkey u), ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  ring

lemma xiPoint_mul_sub_one (z : ℂ) : xiPoint z * (xiPoint z - 1) = -z ^ 2 - 1 / 4 := by
  have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
  simp only [xiPoint]
  linear_combination (z ^ 2) * hI

/-- **Riemann's integral representation of `Ξ`**. -/
theorem riemannXi_eq_integral (z : ℂ) :
    riemannXi z = 1 / 2 - (4 * z ^ 2 + 1) *
      ∫ u in Ioi (0 : ℝ), (wFun u : ℂ) * Complex.cos (2 * u * z) := by
  rw [riemannXi, completedRiemannZeta₀_eq_integral, integral_Ioi_one_eq_cos_integral,
    xiPoint_mul_sub_one]
  ring

/-! ### The `H₀` side -/

/-- The explicit antiderivative used in the integration by parts. -/
def wPrimitive (z : ℂ) (u : ℝ) : ℂ :=
  (wFun' u : ℂ) * Complex.cos (u * z) + z * (wFun u : ℂ) * Complex.sin (u * z)

lemma hasDerivAt_ofReal_mul (z : ℂ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) * z) z u := by
  simpa using ((hasDerivAt_id u).ofReal_comp.mul_const z)

lemma hasDerivAt_ccos_real (z : ℂ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.cos ((t : ℂ) * z)) (-Complex.sin ((u : ℝ) * z) * z) u := by
  refine ((Complex.hasDerivAt_cos ((u : ℂ) * z)).scomp u
    (hasDerivAt_ofReal_mul z u)).congr_deriv ?_
  simp only [smul_eq_mul]
  ring

lemma hasDerivAt_csin_real (z : ℂ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.sin ((t : ℂ) * z)) (Complex.cos ((u : ℝ) * z) * z) u := by
  refine ((Complex.hasDerivAt_sin ((u : ℂ) * z)).scomp u
    (hasDerivAt_ofReal_mul z u)).congr_deriv ?_
  simp only [smul_eq_mul]
  ring

lemma hasDerivAt_wPrimitive (z : ℂ) (u : ℝ) :
    HasDerivAt (wPrimitive z)
      (((wFun'' u : ℂ) + z ^ 2 * (wFun u : ℂ)) * Complex.cos (u * z)) u := by
  have h1 : HasDerivAt (fun t : ℝ => (wFun' t : ℂ)) ((wFun'' u : ℝ) : ℂ) u :=
    (hasDerivAt_wFun' u).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => (wFun t : ℂ)) ((wFun' u : ℝ) : ℂ) u :=
    (hasDerivAt_wFun u).ofReal_comp
  have h3 := (h1.mul (hasDerivAt_ccos_real z u)).add
    ((h2.const_mul z).mul (hasDerivAt_csin_real z u))
  refine h3.congr_deriv ?_
  ring

lemma tendsto_wPrimitive_atTop (z : ℂ) : Tendsto (wPrimitive z) atTop (𝓝 0) := by
  refine squeeze_zero_norm'
    (a := fun u : ℝ => |wFun' u| * Real.exp (‖z‖ * u) + ‖z‖ * (|wFun u| * Real.exp (‖z‖ * u))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    have hcos : ‖Complex.cos ((u : ℝ) * z)‖ ≤ Real.exp (‖z‖ * u) := by
      refine (norm_ccos_le _).trans_eq ?_
      congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu, mul_comm]
    have hsin : ‖Complex.sin ((u : ℝ) * z)‖ ≤ Real.exp (‖z‖ * u) := by
      refine (norm_csin_le _).trans_eq ?_
      congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu, mul_comm]
    calc ‖wPrimitive z u‖
        ≤ ‖(wFun' u : ℂ) * Complex.cos ((u : ℝ) * z)‖
            + ‖z * (wFun u : ℂ) * Complex.sin ((u : ℝ) * z)‖ := norm_add_le _ _
      _ ≤ |wFun' u| * Real.exp (‖z‖ * u) + ‖z‖ * (|wFun u| * Real.exp (‖z‖ * u)) := by
          gcongr
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
          · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsin (abs_nonneg _)) (norm_nonneg _)
  · have t1 := tendsto_decay_mul_exp (f := wFun') (fun hu => abs_wFun'_le hu) ‖z‖
    have t2 := tendsto_decay_mul_exp (f := wFun) (fun hu => abs_wFun_le hu) ‖z‖
    simpa using t1.add (t2.const_mul ‖z‖)

/-- The integration by parts: `∫₀^∞ (W'' + z² W)(u) cos(uz) du = 1/2`. -/
theorem integral_wFun''_add_sq_mul_wFun (z : ℂ) :
    (∫ u in Ioi (0 : ℝ), ((wFun'' u : ℂ) + z ^ 2 * (wFun u : ℂ)) * Complex.cos (u * z))
      = 1 / 2 := by
  have hint : IntegrableOn
      (fun u : ℝ => ((wFun'' u : ℂ) + z ^ 2 * (wFun u : ℂ)) * Complex.cos (u * z)) (Ioi 0) := by
    have h := (integrableOn_wFun''_mul_cos z).add
      ((integrableOn_wFun_mul_cos z).const_mul (z ^ 2))
    refine h.congr ?_
    filter_upwards with u
    simp only [Pi.add_apply]
    ring
  have hcont : ContinuousWithinAt (wPrimitive z) (Ici 0) 0 := by
    have : Continuous (wPrimitive z) := by
      unfold wPrimitive
      exact ((Complex.continuous_ofReal.comp continuous_wFun').mul
        (Complex.continuous_cos.comp (by fun_prop))).add
        (((continuous_const.mul (Complex.continuous_ofReal.comp continuous_wFun))).mul
          (Complex.continuous_sin.comp (by fun_prop)))
    exact this.continuousWithinAt
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun x _ => hasDerivAt_wPrimitive z x) hint (tendsto_wPrimitive_atTop z)
  rw [key]
  simp [wPrimitive, wFun'_zero]

/-- The de Bruijn–Newman function at `t = 0`, in terms of the same cosine integral. -/
theorem dbnH_zero_eq_integral (z : ℂ) :
    dbnH 0 z = 1 / 16 - (z ^ 2 + 1) / 8 *
      ∫ u in Ioi (0 : ℝ), (wFun u : ℂ) * Complex.cos (u * z) := by
  have hsplit : ∀ u : ℝ, dbnKernel 0 z u
      = (1 / 8 : ℂ) * (((wFun'' u : ℂ) + z ^ 2 * (wFun u : ℂ)) * Complex.cos (u * z))
        - ((z ^ 2 + 1) / 8) * ((wFun u : ℂ) * Complex.cos (u * z)) := by
    intro u
    simp only [dbnKernel, zero_mul, Real.exp_zero, one_mul, dbnPhi_eq u]
    push_cast
    ring
  have hint1 : IntegrableOn
      (fun u : ℝ => ((wFun'' u : ℂ) + z ^ 2 * (wFun u : ℂ)) * Complex.cos (u * z)) (Ioi 0) := by
    have h := (integrableOn_wFun''_mul_cos z).add
      ((integrableOn_wFun_mul_cos z).const_mul (z ^ 2))
    refine h.congr ?_
    filter_upwards with u
    simp only [Pi.add_apply]
    ring
  have hint2 := integrableOn_wFun_mul_cos z
  rw [dbnH, setIntegral_congr_fun measurableSet_Ioi (fun u _ => hsplit u),
    integral_sub (hint1.const_mul _) (hint2.const_mul _),
    integral_const_mul, integral_const_mul, integral_wFun''_add_sq_mul_wFun]
  ring

/-! ### The identification -/

/-- **The de Bruijn–Newman function at `t = 0` is the Riemann `Ξ` function**:
`H₀(z) = Ξ(z/2)/8`. -/
theorem dbnH_zero_eq_riemannXi (z : ℂ) : dbnH 0 z = riemannXi (z / 2) / 8 := by
  have hcong : (∫ u in Ioi (0 : ℝ), (wFun u : ℂ) * Complex.cos (2 * u * (z / 2)))
      = ∫ u in Ioi (0 : ℝ), (wFun u : ℂ) * Complex.cos (u * z) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    congr 2
    ring
  rw [dbnH_zero_eq_integral, riemannXi_eq_integral, hcong]
  ring

/-- The zeroes of `H₀` are exactly the zeroes of `Ξ`, doubled. -/
theorem dbnH_zero_eq_zero_iff (z : ℂ) : dbnH 0 z = 0 ↔ riemannXi (z / 2) = 0 := by
  rw [dbnH_zero_eq_riemannXi]
  constructor
  · intro h
    field_simp at h
    simpa using h
  · intro h
    rw [h]
    simp

/-- **The Riemann hypothesis is equivalent to the reality of the zeroes of `H₀`**, the `t = 0`
member of the de Bruijn–Newman family.  Unconditional: the Fourier representation `H₀ = Ξ`
(up to the scaling `z ↦ z/2` and the factor `8`) is proved above. -/
theorem zeta_iff_dbnH_zero : ZetaForm ↔ ∀ z : ℂ, dbnH 0 z = 0 → z.im = 0 := by
  rw [zeta_iff_xi]
  constructor
  · intro hx z hz
    have := hx (z / 2) ((dbnH_zero_eq_zero_iff z).mp hz)
    simpa [Complex.div_im] using this
  · intro hx z hz
    have h2 : dbnH 0 (2 * z) = 0 := by
      rw [dbnH_zero_eq_zero_iff]
      simpa using hz
    have := hx (2 * z) h2
    simpa using this

end RiemannHypothesis

end
