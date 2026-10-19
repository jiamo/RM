/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.OscillatoryIntegral
import RiemannHypothesis.LaplaceGamma
import RiemannHypothesis.ZetaChi
import RiemannHypothesis.GammaVertical

/-!
# The stationary-phase integrals of `ζ` on the critical line (the B process, second half)

For `s = 1/2 + it` and a frequency `ω = 2πν > 0`, the integrals produced by Poisson summation of
`n^(-s)` are

  `∫_a^b u^(-s) e^{iωu} du = ∫_a^b u^(-1/2) e^{iΦ(u)} du`,   `Φ(u) = ωu − t log u`,

whose phase is stationary at `u = t/ω = t/(2πν)`.  Instead of the general stationary-phase lemma
(Titchmarsh, Lemma 4.6) we use a direct computation for this phase: the complete integral is a
Gamma integral.

* `tendsto_integral_mellin` — `∫_0^B u^(-s) e^{iωu} du → Γ(1-s) (i/ω)^(1-s)` as `B → ∞`.
  It is obtained from the Laplace transform at complex frequency
  (`RiemannHypothesis.LaplaceGamma`, Mathlib only has real frequencies) by letting the real part of
  the frequency tend to `0⁺`, with tails controlled uniformly by the first-derivative test.  This
  is where the Fresnel integral would enter in Titchmarsh's treatment; no Fresnel integral is
  needed here.
* `mellinMain_sub_zetaChi_eq`, `norm_mellinMain_sub_zetaChi_le` — `Γ(1-s) (i/(2πν))^(1-s) =
  χ(s) ν^(s-1) + E` with `‖E‖ ≤ ν^(-1/2) e^(-πt)` for `t ≥ 0`: the main term **is**
  `χ(1/2+it) ν^(-1/2+it)` up to an exponentially small error.  No Stirling formula is used.

The evaluation of the truncated integrals `∫_a^b` across the stationary point, with the endpoint
terms extracted to second order, is in `RiemannHypothesis.ZetaStationaryPhase`
(`norm_integral_sub_zetaChi_add_boundary_le`).

Nothing is assumed.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology intervalIntegral

namespace RiemannHypothesis

namespace ZetaMellinPhase

open VanDerCorput Oscillatory

/-! ## The phase and its amplitude functions -/

/-- The phase `Φ(u) = ωu − t log u` of `u^(-1/2-it) e^{iωu}`. -/
def phase (t ω : ℝ) (u : ℝ) : ℝ := ω * u - t * Real.log u

/-- `Φ'(u) = ω − t/u`. -/
def phase' (t ω : ℝ) (u : ℝ) : ℝ := ω - t / u

/-- `h = u^(-1/2)/Φ' = √u/(ωu − t)`. -/
def ampH (t ω : ℝ) (u : ℝ) : ℝ := Real.sqrt u / (ω * u - t)

/-- `h' = −(ωu + t)/(2√u (ωu − t)²)`. -/
def ampH' (t ω : ℝ) (u : ℝ) : ℝ := -(ω * u + t) / (2 * Real.sqrt u * (ω * u - t) ^ 2)

/-- `k = h'/Φ' = −√u (ωu + t)/(2 (ωu − t)³)`. -/
def ampK (t ω : ℝ) (u : ℝ) : ℝ := -(Real.sqrt u * (ω * u + t)) / (2 * (ω * u - t) ^ 3)

/-- `k' = (3ω²u² + 8ωut + t²)/(4√u (ωu − t)⁴)`. -/
def ampK' (t ω : ℝ) (u : ℝ) : ℝ :=
  (3 * ω ^ 2 * u ^ 2 + 8 * ω * u * t + t ^ 2) / (4 * Real.sqrt u * (ω * u - t) ^ 4)

theorem hasDerivAt_phase (t ω : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (phase t ω) (phase' t ω u) u := by
  have h := ((hasDerivAt_id u).const_mul ω).sub ((Real.hasDerivAt_log hu.ne').const_mul t)
  refine h.congr_deriv ?_
  simp [phase', div_eq_mul_inv]

theorem continuousOn_phase' (t ω : ℝ) {s : Set ℝ} (hs : s ⊆ Ioi 0) :
    ContinuousOn (phase' t ω) s := by
  unfold phase'
  exact continuousOn_const.sub (continuousOn_const.div continuousOn_id
    fun x hx => (show (0 : ℝ) < x from hs hx).ne')

theorem hasDerivAt_ampH (t ω : ℝ) {u : ℝ} (hu : 0 < u) (hne : ω * u - t ≠ 0) :
    HasDerivAt (ampH t ω) (ampH' t ω u) u := by
  have hs := Real.hasDerivAt_sqrt hu.ne'
  have hl : HasDerivAt (fun x => ω * x - t) ω u := by
    simpa using ((hasDerivAt_id u).const_mul ω).sub_const t
  have h := hs.div hl hne
  refine h.congr_deriv ?_
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ u = r ^ 2 := ⟨√u, Real.sqrt_pos.mpr hu, (Real.sq_sqrt hu.le).symm⟩
  have hsr : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  unfold ampH'
  rw [hsr]
  field_simp
  ring

theorem hasDerivAt_ampK (t ω : ℝ) {u : ℝ} (hu : 0 < u) (hne : ω * u - t ≠ 0) :
    HasDerivAt (ampK t ω) (ampK' t ω u) u := by
  have hs := Real.hasDerivAt_sqrt hu.ne'
  have hl : HasDerivAt (fun x => ω * x - t) ω u := by
    simpa using ((hasDerivAt_id u).const_mul ω).sub_const t
  have hl2 : HasDerivAt (fun x => ω * x + t) ω u := by
    simpa using ((hasDerivAt_id u).const_mul ω).add_const t
  have hnum : HasDerivAt (fun x => -(Real.sqrt x * (ω * x + t)))
      (-(1 / (2 * Real.sqrt u) * (ω * u + t) + Real.sqrt u * ω)) u := (hs.mul hl2).neg
  have hden : HasDerivAt (fun x => 2 * (ω * x - t) ^ 3) (2 * (3 * (ω * u - t) ^ 2 * ω)) u := by
    have := (hl.pow 3).const_mul (2 : ℝ)
    simpa using this
  have hden0 : 2 * (ω * u - t) ^ 3 ≠ 0 := by positivity
  have h := hnum.div hden hden0
  refine h.congr_deriv ?_
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ u = r ^ 2 := ⟨√u, Real.sqrt_pos.mpr hu, (Real.sq_sqrt hu.le).symm⟩
  have hsr : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  unfold ampK'
  rw [hsr]
  field_simp
  ring

theorem amp_eq_ampH_mul (t ω : ℝ) {u : ℝ} (hu : 0 < u) (hne : ω * u - t ≠ 0) :
    1 / Real.sqrt u = ampH t ω u * phase' t ω u := by
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ u = r ^ 2 := ⟨√u, Real.sqrt_pos.mpr hu, (Real.sq_sqrt hu.le).symm⟩
  have hsr : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  have hne' : r ^ 2 * ω - t ≠ 0 := by intro h; apply hne; linarith
  unfold ampH phase'
  rw [hsr]
  field_simp

theorem ampH'_eq_ampK_mul (t ω : ℝ) {u : ℝ} (hu : 0 < u) (hne : ω * u - t ≠ 0) :
    ampH' t ω u = ampK t ω u * phase' t ω u := by
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ u = r ^ 2 := ⟨√u, Real.sqrt_pos.mpr hu, (Real.sq_sqrt hu.le).symm⟩
  have hsr : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  unfold ampH' ampK phase'
  rw [hsr]
  field_simp

/-- `u^(-s) e^{iωu} = u^(-1/2) e^{iΦ(u)}` on the critical line, `u > 0`. -/
theorem cpow_mul_exp_eq (t ω : ℝ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)) * cexp (I * (ω * u : ℝ))
      = ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
    expI, phase, ← Complex.exp_add]
  have hs : (1 / Real.sqrt u : ℝ) = Real.exp (-(1 / 2) * Real.log u) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu, one_div, ← Real.exp_neg]
    ring_nf
  rw [hs, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## Integrability near `0` -/

theorem one_div_sqrt_eq_rpow {u : ℝ} (hu : 0 ≤ u) : 1 / Real.sqrt u = u ^ (-(1 / 2 : ℝ)) := by
  rcases hu.lt_or_eq with hu | hu
  · rw [Real.sqrt_eq_rpow, Real.rpow_neg hu.le, one_div]
  · subst hu; simp

theorem measurable_expI_phase (t ω : ℝ) : Measurable (expI (phase t ω)) := by
  unfold expI phase
  fun_prop

/-- `u^(-1/2) F(u) e^{iΦ(u)}` is interval integrable on `[0, B]` for bounded measurable `F`. -/
theorem intervalIntegrable_weight_mul_expI (t ω : ℝ) {F : ℝ → ℝ} (hF : Measurable F)
    (hF1 : ∀ u, 0 ≤ u → |F u| ≤ 1) {B : ℝ} (hB : 0 ≤ B) :
    IntervalIntegrable (fun u => ((F u / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u) volume 0 B := by
  refine (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (by norm_num)).mono_fun' ?_ ?_
  · exact ((continuous_ofReal.measurable.comp (hF.div Real.continuous_sqrt.measurable)).mul
      (measurable_expI_phase t ω)).aestronglyMeasurable
  · rw [uIoc_of_le hB]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 ≤ u := hu.1.le
    rw [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg u), ← one_div_sqrt_eq_rpow hu0]
    exact div_le_div_of_nonneg_right (hF1 u hu0) (Real.sqrt_nonneg u)

theorem intervalIntegrable_mellin (t ω : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    IntervalIntegrable (fun u => ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u) volume 0 B :=
  intervalIntegrable_weight_mul_expI t ω (F := fun _ => 1) measurable_const
    (fun _ _ => by simp) hB

theorem intervalIntegrable_mellin' (t ω : ℝ) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    IntervalIntegrable (fun u => ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u) volume p q :=
  ((intervalIntegrable_mellin t ω hp).symm).trans (intervalIntegrable_mellin t ω hq)

/-- `‖∫_0^δ u^(-1/2) e^{iΦ}‖ ≤ 2√δ`. -/
theorem norm_integral_mellin_initial_le (t ω : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖∫ u in (0 : ℝ)..δ, ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u‖ ≤ 2 * Real.sqrt δ := by
  have h1 : ‖∫ u in (0 : ℝ)..δ, ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u‖
      ≤ ∫ u in (0 : ℝ)..δ, u ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hδ ?_
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
    filter_upwards with u hu
    rw [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), one_div_sqrt_eq_rpow hu.1.le]
  have h2 : ∫ u in (0 : ℝ)..δ, u ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt δ := by
    rw [integral_rpow (Or.inl (by norm_num)), Real.sqrt_eq_rpow]
    norm_num
    ring
  linarith

/-! ## The tail: uniform first-derivative bound with a damping factor `e^{-εu}` -/

theorem ampH_pos {t ω u : ℝ} (hu : 0 < u) (hne : t < ω * u) : 0 < ampH t ω u := by
  unfold ampH
  exact div_pos (Real.sqrt_pos.mpr hu) (by linarith)

theorem ampH_antitone {t ω B B' : ℝ} (ht : 0 ≤ t) (hB : 0 < B) (hBB' : B ≤ B') (hne : t < ω * B) :
    ampH t ω B' ≤ ampH t ω B := by
  have hB'0 : 0 < B' := lt_of_lt_of_le hB hBB'
  have hω : 0 < ω := by
    by_contra h; nlinarith [not_lt.mp h]
  have hne' : t < ω * B' := by nlinarith
  unfold ampH
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hx := Real.sqrt_pos.mpr hB
  have hy := Real.sqrt_pos.mpr hB'0
  have hxy : Real.sqrt B ≤ Real.sqrt B' := Real.sqrt_le_sqrt hBB'
  have hx2 := Real.sq_sqrt hB.le
  have hy2 := Real.sq_sqrt hB'0.le
  have : (Real.sqrt B - Real.sqrt B') * (ω * Real.sqrt B * Real.sqrt B' + t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have key : Real.sqrt B' * (ω * B - t) - Real.sqrt B * (ω * B' - t)
      = (Real.sqrt B - Real.sqrt B') * (ω * Real.sqrt B * Real.sqrt B' + t) := by
    linear_combination (-ω * Real.sqrt B') * hx2 + (ω * Real.sqrt B) * hy2
  linarith

/-- **Tail bound**: for `t ≥ 0`, `ω > 0`, `ε ≥ 0` and `t/ω < B ≤ B'`,
`‖∫_B^{B'} e^{-εu} u^(-1/2) e^{iΦ(u)} du‖ ≤ 2 √B/(ωB − t)`. -/
theorem norm_integral_tail_le {t ω ε B B' : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hB : 0 < B)
    (hBB' : B ≤ B') (hne : t < ω * B) :
    ‖∫ u in B..B', ((Real.exp (-(ε * u)) / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u‖
      ≤ 2 * ampH t ω B := by
  have hω : 0 < ω := by
    by_contra h; nlinarith [not_lt.mp h]
  have hpos : ∀ u ∈ Icc B B', 0 < u := fun u hu => lt_of_lt_of_le hB hu.1
  have hne' : ∀ u ∈ Icc B B', t < ω * u := fun u hu => by nlinarith [hu.1]
  set h : ℝ → ℝ := fun u => Real.exp (-(ε * u)) * ampH t ω u with hh
  set h' : ℝ → ℝ := fun u => Real.exp (-(ε * u)) * (ampH' t ω u - ε * ampH t ω u) with hh'
  have hderiv : ∀ u ∈ Icc B B', HasDerivAt h (h' u) u := by
    intro u hu
    have h1 : HasDerivAt (fun u => Real.exp (-(ε * u))) (Real.exp (-(ε * u)) * (-ε)) u := by
      have := ((hasDerivAt_id u).const_mul ε).neg.exp
      simpa using this
    have h2 := hasDerivAt_ampH t ω (hpos u hu) (by linarith [hne' u hu])
    refine (h1.mul h2).congr_deriv ?_
    simp only [hh']; ring
  have hh'c : ContinuousOn h' (Icc B B') := by
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.sub
    · unfold ampH'
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu
      have := hpos u hu; have := hne' u hu
      have : 0 < Real.sqrt u := Real.sqrt_pos.mpr (hpos u hu)
      positivity
    · apply ContinuousOn.mul continuousOn_const
      unfold ampH
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu; have := hne' u hu; linarith
  have hg : ∀ u ∈ Icc B B', Real.exp (-(ε * u)) / Real.sqrt u = h u * phase' t ω u := by
    intro u hu
    rw [div_eq_mul_one_div, amp_eq_ampH_mul t ω (hpos u hu) (by linarith [hne' u hu])]
    simp only [hh]; ring
  have hsign : ∀ u ∈ Icc B B', h' u ≤ 0 := by
    intro u hu
    have hu0 := hpos u hu
    have hA : ampH' t ω u ≤ 0 := by
      unfold ampH'
      apply div_nonpos_of_nonpos_of_nonneg
      · have : 0 < ω * u := by positivity
        linarith
      · positivity
    have hB0 : 0 ≤ ampH t ω u := (ampH_pos hu0 (hne' u hu)).le
    simp only [hh']
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    nlinarith
  have hhB : 0 ≤ h B := mul_nonneg (Real.exp_pos _).le (ampH_pos hB hne).le
  have hhB' : 0 ≤ h B' :=
    mul_nonneg (Real.exp_pos _).le (ampH_pos (hpos B' ⟨hBB', le_rfl⟩) (hne' B' ⟨hBB', le_rfl⟩)).le
  have hexp1 : ∀ u, 0 ≤ u → Real.exp (-(ε * u)) ≤ 1 := fun u hu =>
    Real.exp_le_one_iff.mpr (by nlinarith)
  refine norm_integral_le_two_mul_of_monotone_ratio (le_trans hB.le hBB' |> fun _ => hBB')
    (fun u hu => hasDerivAt_phase t ω (hpos u hu)) hderiv
    (continuousOn_phase' t ω fun u hu => hpos u hu) hh'c hg (Or.inr hsign)
    (mul_nonneg hhB hhB') ?_ ?_
  · rw [abs_of_nonneg hhB]
    calc h B ≤ 1 * ampH t ω B :=
          mul_le_mul_of_nonneg_right (hexp1 B hB.le) (ampH_pos hB hne).le
      _ = ampH t ω B := one_mul _
  · rw [abs_of_nonneg hhB']
    calc h B' ≤ 1 * ampH t ω B' :=
          mul_le_mul_of_nonneg_right (hexp1 B' (le_trans hB.le hBB'))
            (ampH_pos (hpos B' ⟨hBB', le_rfl⟩) (hne' B' ⟨hBB', le_rfl⟩)).le
      _ ≤ ampH t ω B := by rw [one_mul]; exact ampH_antitone ht hB hBB' hne

/-! ## The complete integral: a Gamma integral -/

/-- The value of the complete integral `∫_0^∞ u^(-s) e^{iωu} du`: `Γ(1-s) (i/ω)^(1-s)`. -/
def mellinMain (t ω : ℝ) : ℂ :=
  Complex.Gamma (1 - (1 / 2 + (t : ℂ) * I)) * (I / (ω : ℂ)) ^ (1 - (1 / 2 + (t : ℂ) * I))

theorem lapIntegrand_eq (t ω ε : ℝ) {u : ℝ} (hu : 0 < u) :
    LaplaceGamma.lapIntegrand (1 - (1 / 2 + (t : ℂ) * I)) ((ε : ℂ) - (ω : ℂ) * I) u
      = ((Real.exp (-(ε * u)) / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u := by
  unfold LaplaceGamma.lapIntegrand
  have h := cpow_mul_exp_eq t ω hu
  have hexp : cexp (-(((ε : ℂ) - (ω : ℂ) * I) * (u : ℂ)))
      = ((Real.exp (-(ε * u)) : ℝ) : ℂ) * cexp (I * ((ω * u : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [show (1 - (1 / 2 + (t : ℂ) * I)) - 1 = -(1 / 2 + (t : ℂ) * I) by ring, hexp]
  calc (u : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)) * (((Real.exp (-(ε * u)) : ℝ) : ℂ)
        * cexp (I * ((ω * u : ℝ) : ℂ)))
      = ((Real.exp (-(ε * u)) : ℝ) : ℂ)
        * ((u : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)) * cexp (I * ((ω * u : ℝ) : ℂ))) := by ring
    _ = _ := by rw [h]; push_cast; ring

theorem tendsto_lap_value {t ω : ℝ} (hω : 0 < ω) :
    Tendsto (fun ε : ℝ => (1 / ((ε : ℂ) - (ω : ℂ) * I)) ^ (1 - (1 / 2 + (t : ℂ) * I))
        * Complex.Gamma (1 - (1 / 2 + (t : ℂ) * I))) (𝓝[>] 0) (𝓝 (mellinMain t ω)) := by
  have hden : ((0 : ℝ) : ℂ) - (ω : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hω.ne' this
  have hval : 1 / (((0 : ℝ) : ℂ) - (ω : ℂ) * I) = I / (ω : ℂ) := by
    have hωc : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω.ne'
    field_simp
    push_cast
    linear_combination (ω : ℂ) * I_sq
  have hslit : I / (ω : ℂ) ∈ slitPlane := by
    right
    simp [Complex.div_im, hω.ne']
  have hcont : ContinuousAt (fun ε : ℝ => (1 / ((ε : ℂ) - (ω : ℂ) * I)) ^ (1 - (1 / 2 + (t : ℂ) * I))
      * Complex.Gamma (1 - (1 / 2 + (t : ℂ) * I))) 0 := by
    apply ContinuousAt.mul _ continuousAt_const
    apply ContinuousAt.cpow _ continuousAt_const (by rw [hval]; exact hslit)
    exact continuousAt_const.div (by fun_prop) hden
  have := hcont.tendsto
  rw [show (1 / (((0 : ℝ) : ℂ) - (ω : ℂ) * I)) ^ (1 - (1 / 2 + (t : ℂ) * I))
      * Complex.Gamma (1 - (1 / 2 + (t : ℂ) * I)) = mellinMain t ω by
    rw [hval, mellinMain, mul_comm]] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **The complete integral, quantitatively**: for `t ≥ 0`, `0 < B` with `ωB > t`,
`‖∫_0^B u^(-1/2) e^{iΦ(u)} du − Γ(1-s) (i/ω)^(1-s)‖ ≤ 2 √B/(ωB − t)`. -/
theorem norm_integral_mellin_sub_le {t ω B : ℝ} (ht : 0 ≤ t) (hB : 0 < B) (hne : t < ω * B) :
    ‖(∫ u in (0 : ℝ)..B, ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u) - mellinMain t ω‖
      ≤ 2 * ampH t ω B := by
  have hω : 0 < ω := by by_contra h; nlinarith [not_lt.mp h]
  set a : ℂ := 1 - (1 / 2 + (t : ℂ) * I) with ha
  have hare : 0 < a.re := by simp [ha]; norm_num
  set J : ℝ → ℝ → ℂ := fun ε B' =>
    ∫ u in (0 : ℝ)..B', ((Real.exp (-(ε * u)) / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u with hJ
  set L : ℝ → ℂ := fun ε => (1 / ((ε : ℂ) - (ω : ℂ) * I)) ^ a * Complex.Gamma a with hL
  have hFint : ∀ ε : ℝ, 0 ≤ ε → ∀ B' : ℝ, 0 ≤ B' → IntervalIntegrable
      (fun u => ((Real.exp (-(ε * u)) / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u) volume 0 B' := by
    intro ε hε B' hB'
    refine intervalIntegrable_weight_mul_expI t ω (F := fun u => Real.exp (-(ε * u)))
      (by fun_prop) (fun u hu => ?_) hB'
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  -- (a)–(c): for `ε > 0`, `‖J ε B − L ε‖ ≤ 2 h(B)`
  have hstep : ∀ ε : ℝ, 0 < ε → ‖J ε B - L ε‖ ≤ 2 * ampH t ω B := by
    intro ε hε
    have hre : 0 < ((ε : ℂ) - (ω : ℂ) * I).re := by simp [hε]
    have hint := LaplaceGamma.integrableOn_lapIntegrand hare hre
    have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    have hval := LaplaceGamma.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hare hre
    have hcongr : ∀ B' : ℝ, 0 ≤ B' → ∫ u in (0 : ℝ)..B', LaplaceGamma.lapIntegrand a
        ((ε : ℂ) - (ω : ℂ) * I) u = J ε B' := by
      intro B' hB'
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with u hu
      rw [uIoc_of_le hB'] at hu
      exact lapIntegrand_eq t ω ε hu.1
    have hL' : ∫ u in Ioi (0 : ℝ), LaplaceGamma.lapIntegrand a ((ε : ℂ) - (ω : ℂ) * I) u = L ε := by
      rw [hL]; exact hval
    rw [hL'] at hlim
    replace hlim : Tendsto (fun B' => J ε B') atTop (𝓝 (L ε)) := by
      refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with B' hB'
      exact hcongr B' hB'
    have h1 : Tendsto (fun B' => ‖J ε B' - J ε B‖) atTop (𝓝 ‖L ε - J ε B‖) :=
      (hlim.sub_const _).norm
    have h2 : ∀ᶠ B' in atTop, ‖J ε B' - J ε B‖ ≤ 2 * ampH t ω B := by
      filter_upwards [eventually_ge_atTop B] with B' hB'
      rw [hJ]
      simp only
      rw [intervalIntegral.integral_interval_sub_left (hFint ε hε.le B' (by linarith))
        (hFint ε hε.le B hB.le)]
      exact norm_integral_tail_le ht hε.le hB hB' hne
    have := le_of_tendsto h1 h2
    rwa [norm_sub_rev] at this
  -- (d): `‖J 0 B − J ε B‖ ≤ 2 ε B √B`
  have hJ0 : (∫ u in (0 : ℝ)..B, ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u) = J 0 B := by
    rw [hJ]; simp
  have hdiff : ∀ ε : ℝ, 0 < ε → ‖J 0 B - J ε B‖ ≤ ε * B * (2 * Real.sqrt B) := by
    intro ε hε
    rw [hJ]; simp only
    rw [← intervalIntegral.integral_sub (hFint 0 le_rfl B hB.le) (hFint ε hε.le B hB.le)]
    have hbound : ‖∫ u in (0 : ℝ)..B, (((Real.exp (-(0 * u)) / Real.sqrt u : ℝ) : ℂ)
        * expI (phase t ω) u - ((Real.exp (-(ε * u)) / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u)‖
        ≤ ∫ u in (0 : ℝ)..B, ε * B * u ^ (-(1 / 2 : ℝ)) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hB.le ?_
        ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
      filter_upwards with u hu
      have hu0 : 0 < u := hu.1
      rw [← sub_mul, norm_mul, norm_expI, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, ← one_div_sqrt_eq_rpow hu0.le]
      simp only [zero_mul, neg_zero, Real.exp_zero]
      rw [← sub_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg u)]
      have h1 : 0 ≤ 1 - Real.exp (-(ε * u)) := by
        have := Real.exp_le_one_iff.mpr (show -(ε * u) ≤ 0 by nlinarith)
        linarith
      have h2 : 1 - Real.exp (-(ε * u)) ≤ ε * u := by
        have := Real.add_one_le_exp (-(ε * u)); linarith
      rw [abs_of_nonneg h1, div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [hu.2]
    refine hbound.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      Real.sqrt_eq_rpow]
    norm_num
    ring_nf
    simp
  -- (e): let `ε → 0⁺`
  have hlimL := tendsto_lap_value (t := t) hω
  have hR : Tendsto (fun ε : ℝ => ε * B * (2 * Real.sqrt B) + 2 * ampH t ω B + ‖L ε - mellinMain t ω‖)
      (𝓝[>] 0) (𝓝 (0 * B * (2 * Real.sqrt B) + 2 * ampH t ω B + 0)) := by
    refine Tendsto.add (Tendsto.add ?_ tendsto_const_nhds) ?_
    · exact ((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _).mul_const _
    · have := (hlimL.sub_const (mellinMain t ω)).norm
      rw [sub_self, norm_zero] at this
      exact this
  simp only [zero_mul, add_zero, zero_add] at hR
  rw [hJ0]
  refine ge_of_tendsto hR ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  calc ‖J 0 B - mellinMain t ω‖ ≤ ‖J 0 B - J ε B‖ + ‖J ε B - L ε‖ + ‖L ε - mellinMain t ω‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (J 0 B) (J ε B) (mellinMain t ω)
        have h2 := norm_sub_le_norm_sub_add_norm_sub (J ε B) (L ε) (mellinMain t ω)
        linarith
    _ ≤ ε * B * (2 * Real.sqrt B) + 2 * ampH t ω B + ‖L ε - mellinMain t ω‖ := by
        gcongr
        · exact hdiff ε hε'
        · exact hstep ε hε'

/-- **The complete integral**: `∫_0^B u^(-s) e^{iωu} du → Γ(1-s) (i/ω)^(1-s)` as `B → ∞`, for
`t ≥ 0` and `ω > 0`. -/
theorem tendsto_integral_mellin {t ω : ℝ} (ht : 0 ≤ t) (hω : 0 < ω) :
    Tendsto (fun B => ∫ u in (0 : ℝ)..B, ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u) atTop
      (𝓝 (mellinMain t ω)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun B : ℝ => 4 / ω * (1 / Real.sqrt B)) atTop (𝓝 (4 / ω * 0)) := by
    refine Tendsto.const_mul _ ?_
    have := (Real.tendsto_sqrt_atTop).inv_tendsto_atTop
    simp only [one_div]
    exact this
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (2 * t / ω + 1)] with B hB
  have hB0 : 0 < B := by
    have : 0 ≤ 2 * t / ω := by positivity
    linarith
  have hωB : 2 * t + ω ≤ ω * B := by
    have := mul_le_mul_of_nonneg_left hB hω.le
    rw [mul_add, mul_div_cancel₀ _ hω.ne', mul_one] at this
    linarith
  have hne : t < ω * B := by linarith
  refine (norm_integral_mellin_sub_le ht hB0 hne).trans ?_
  have hsq := Real.sqrt_pos.mpr hB0
  have hsq2 := Real.sq_sqrt hB0.le
  unfold ampH
  rw [show 2 * (Real.sqrt B / (ω * B - t)) = 2 * Real.sqrt B / (ω * B - t) by ring]
  rw [div_le_iff₀ (by linarith)]
  have : ω * B - t ≥ ω * B / 2 := by linarith
  have h4 : 4 / ω * (1 / Real.sqrt B) * (ω * B - t) ≥ 4 / ω * (1 / Real.sqrt B) * (ω * B / 2) :=
    mul_le_mul_of_nonneg_left this (by positivity)
  have h5 : 4 / ω * (1 / Real.sqrt B) * (ω * B / 2) = 2 * Real.sqrt B := by
    have hBs : B = Real.sqrt B * Real.sqrt B := (Real.mul_self_sqrt hB0.le).symm
    calc 4 / ω * (1 / Real.sqrt B) * (ω * B / 2)
        = 4 / ω * (1 / Real.sqrt B) * (ω * (Real.sqrt B * Real.sqrt B) / 2) := by rw [← hBs]
      _ = 2 * Real.sqrt B := by field_simp; ring
  linarith

/-! ## The main term is `χ(s) ν^(s-1)` -/

theorem log_I_div {ω : ℝ} (hω : 0 < ω) :
    Complex.log (I / (ω : ℂ)) = ((-Real.log ω : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I := by
  have he : I / (ω : ℂ) = ((ω⁻¹ : ℝ) : ℂ) * I := by push_cast; ring
  apply Complex.ext
  · rw [Complex.log_re, he, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hω), Real.log_inv]
    simp
  · rw [Complex.log_im, he, Complex.arg_real_mul _ (inv_pos.mpr hω), Complex.arg_I]
    simp

theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (r : ℂ) ^ z = cexp ((Real.log r : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), Complex.ofReal_log hr.le]

theorem mellinMain_eq (t : ℝ) {ν : ℝ} (hν : 0 < ν) :
    mellinMain t (2 * Real.pi * ν) = Complex.Gamma (1 - (1 / 2 + (t : ℂ) * I))
      * ((2 * (Real.pi : ℂ)) ^ ((1 / 2 + (t : ℂ) * I) - 1) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
        * cexp (I * Real.pi * (1 - (1 / 2 + (t : ℂ) * I)) / 2)) := by
  have hω : 0 < 2 * Real.pi * ν := by positivity
  have h2π : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  unfold mellinMain
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by simp [Real.pi_ne_zero, hν.ne']), log_I_div hω, h2π,
    ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp hν, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  rw [Real.log_mul (by positivity) hν.ne']
  push_cast
  ring

theorem mellinMain_sub_zetaChi_eq (t : ℝ) {ν : ℝ} (hν : 0 < ν) :
    mellinMain t (2 * Real.pi * ν) - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
      = (2 * (Real.pi : ℂ)) ^ ((1 / 2 + (t : ℂ) * I) - 1) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
        * Complex.Gamma (1 - (1 / 2 + (t : ℂ) * I)) * (I * cexp (I * Real.pi * (1 / 2 + (t : ℂ) * I) / 2)) := by
  rw [mellinMain_eq t hν, zetaChi, Complex.sin]
  have h1 : cexp (I * Real.pi * (1 - (1 / 2 + (t : ℂ) * I)) / 2)
      = I * cexp (-(Real.pi * (1 / 2 + (t : ℂ) * I) / 2 * I)) := by
    rw [show I * Real.pi * (1 - (1 / 2 + (t : ℂ) * I)) / 2
      = (Real.pi / 2 : ℂ) * I + (-(Real.pi * (1 / 2 + (t : ℂ) * I) / 2 * I)) by ring,
      Complex.exp_add, Complex.exp_mul_I]
    simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  rw [h1]
  have h2 : cexp (I * Real.pi * (1 / 2 + (t : ℂ) * I) / 2) = cexp (Real.pi * (1 / 2 + (t : ℂ) * I) / 2 * I) := by
    congr 1; ring
  rw [h2]
  ring_nf

theorem norm_mellinMain_sub_zetaChi_le (t : ℝ) {ν : ℝ} (hν : 0 < ν) :
    ‖mellinMain t (2 * Real.pi * ν) - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)‖
      ≤ ν ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * t)) := by
  rw [mellinMain_sub_zetaChi_eq t hν]
  have h2π : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hre : ((1 / 2 + (t : ℂ) * I) - 1).re = -(1 / 2) := by simp; norm_num
  rw [norm_mul, norm_mul, norm_mul, norm_mul, h2π, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos hν, hre, norm_I, one_mul, Complex.norm_exp]
  have hexp : (I * Real.pi * (1 / 2 + (t : ℂ) * I) / 2).re = -(Real.pi * t / 2) := by
    simp; ring
  rw [hexp]
  have hG : ‖Complex.Gamma (1 - (1 / 2 + (t : ℂ) * I))‖ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * t / 2)) := by
    have h := norm_Gamma_half_add_mul_I_sq (-t)
    rw [show (1 : ℂ) - (1 / 2 + (t : ℂ) * I) = 1 / 2 + ((-t : ℝ) : ℂ) * I by push_cast; ring]
    have hcosh : Real.exp (Real.pi * t) / 2 ≤ Real.cosh (Real.pi * (-t)) := by
      rw [mul_neg, Real.cosh_neg, Real.cosh_eq]
      have := Real.exp_pos (-(Real.pi * t)); linarith
    have hsq : ‖Complex.Gamma (1 / 2 + ((-t : ℝ) : ℂ) * I)‖ ^ 2
        ≤ (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * t / 2))) ^ 2 := by
      rw [h, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
      rw [div_le_iff₀ (Real.cosh_pos _)]
      push_cast
      have he : Real.exp (2 * -(Real.pi * t / 2)) * Real.exp (Real.pi * t) = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      have := mul_le_mul_of_nonneg_left hcosh
        (by positivity : 0 ≤ 2 * Real.pi * Real.exp (2 * -(Real.pi * t / 2)))
      nlinarith [Real.pi_pos]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  calc (2 * Real.pi) ^ (-(1 / 2 : ℝ)) * ν ^ (-(1 / 2 : ℝ)) * ‖Complex.Gamma (1 - (1 / 2 + (t : ℂ) * I))‖
        * Real.exp (-(Real.pi * t / 2))
      ≤ (2 * Real.pi) ^ (-(1 / 2 : ℝ)) * ν ^ (-(1 / 2 : ℝ))
        * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * t / 2))) * Real.exp (-(Real.pi * t / 2)) := by
        gcongr
    _ = ν ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * t)) := by
        have h1 : (2 * Real.pi) ^ (-(1 / 2 : ℝ)) * Real.sqrt (2 * Real.pi) = 1 := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]; norm_num
        have h2 : Real.exp (-(Real.pi * t / 2)) * Real.exp (-(Real.pi * t / 2))
            = Real.exp (-(Real.pi * t)) := by rw [← Real.exp_add]; ring_nf
        calc (2 * Real.pi) ^ (-(1 / 2 : ℝ)) * ν ^ (-(1 / 2 : ℝ))
            * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * t / 2))) * Real.exp (-(Real.pi * t / 2))
            = ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) * Real.sqrt (2 * Real.pi)) * ν ^ (-(1 / 2 : ℝ))
              * (Real.exp (-(Real.pi * t / 2)) * Real.exp (-(Real.pi * t / 2))) := by ring
          _ = _ := by rw [h1, h2, one_mul]

end ZetaMellinPhase

end RiemannHypothesis
