/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZetaMellinPhase

/-!
# Stationary phase for `ζ` on the critical line (the B process, R2)

For `s = 1/2 + it`, `t > 0`, and `ω > 0` write

  `I(a, b) = ∫_a^b u^(-1/2) e^{iΦ(u)} du`,  `Φ(u) = ωu − t log u`,

so that `I(a, b) = ∫_a^b u^(-s) e^{iωu} du`; with `ω = 2πν` the integrand is
`u^(-1/2) e(−(t/2π) log u + νu)`.  The phase is stationary at `u = t/ω`.  Let
`h(u) = √u/(ωu − t)` and `k(u) = −√u (ωu + t)/(2 (ωu − t)³)`, and `E(u) = e^{iΦ(u)}`.

* `norm_integral_add_boundary_le_of_ne` — away from the stationary point, to second order:
  `‖I(p, q) + i (h(q) E(q) − h(p) E(p))‖ ≤ |k p| + |k q| + ∫_p^q |k'|` (any sign of `ω`).
* `norm_integral_initial_add_boundary_le` — the initial piece `[0, a]`, `ωa < t`:
  `‖I(0, a) + i h(a) E(a)‖ ≤ 2 |k(a)|`.
* `norm_mellinMain_sub_integral_sub_boundary_le` — the tail `[b, ∞)`, `ωb > t`:
  `‖Γ(1-s)(i/ω)^(1-s) − I(0, b) − i h(b) E(b)‖ ≤ 2 |k(b)|`.
* `norm_integral_sub_mellinMain_add_boundary_le` — across the stationary point,
  `0 < a < t/ω < b`: `‖I(a, b) − Γ(1-s)(i/ω)^(1-s) + i (h(b) E(b) − h(a) E(a))‖ ≤ 2 (|k a| + |k b|)`.
* `norm_integral_sub_zetaChi_add_boundary_le` — **the evaluation**: with `ω = 2πν`,
  `‖I(a, b) − χ(s) ν^(s-1) + i (h(b) E(b) − h(a) E(a))‖ ≤ 2 (|k a| + |k b|) + ν^(-1/2) e^(-πt)`.

The complete integral `∫_0^∞` is evaluated exactly in `RiemannHypothesis.ZetaMellinPhase` (a Gamma
integral, reached from the Laplace transform by letting the damping tend to `0⁺`), so no Fresnel
integral and no Stirling formula is needed.  Nothing is assumed.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RiemannHypothesis

namespace ZetaMellinPhase

open VanDerCorput Oscillatory

/-- The oscillatory integral `I(p, q) = ∫_p^q u^(-1/2) e^{iΦ(u)} du`. -/
def mI (t ω p q : ℝ) : ℂ := ∫ u in p..q, ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u

/-- The first-order boundary term `h(u) e^{iΦ(u)}`. -/
def bdry (t ω u : ℝ) : ℂ := (ampH t ω u : ℂ) * expI (phase t ω) u

theorem norm_bdry (t ω u : ℝ) : ‖bdry t ω u‖ = |ampH t ω u| := by
  simp [bdry, norm_expI, Complex.norm_real]

theorem continuousOn_ampK' (t ω : ℝ) {S : Set ℝ} (hS : ∀ u ∈ S, 0 < u ∧ ω * u - t ≠ 0) :
    ContinuousOn (ampK' t ω) S := by
  unfold ampK'
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro u hu
  obtain ⟨h1, h2⟩ := hS u hu
  have : 0 < Real.sqrt u := Real.sqrt_pos.mpr h1
  positivity

theorem mI_add (t ω : ℝ) {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    mI t ω p q + mI t ω q r = mI t ω p r :=
  intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_mellin' t ω hp hq)
    (intervalIntegrable_mellin' t ω hq hr)

/-- **Second order away from the stationary point** (any sign of `ω`). -/
theorem norm_integral_add_boundary_le_of_ne {t ω p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hne : ∀ u ∈ Icc p q, ω * u - t ≠ 0) :
    ‖mI t ω p q + I * (bdry t ω q - bdry t ω p)‖
      ≤ |ampK t ω p| + |ampK t ω q| + ∫ u in p..q, |ampK' t ω u| := by
  have hpos : ∀ u ∈ Icc p q, 0 < u := fun u hu => lt_of_lt_of_le hp hu.1
  have h := norm_integral_add_boundary_le hpq (g := fun u => 1 / Real.sqrt u)
    (h := ampH t ω) (h' := ampH' t ω) (k := ampK t ω) (k' := ampK' t ω)
    (Φ := phase t ω) (Φ' := phase' t ω)
    (fun u hu => hasDerivAt_phase t ω (hpos u hu))
    (fun u hu => hasDerivAt_ampH t ω (hpos u hu) (hne u hu))
    (fun u hu => hasDerivAt_ampK t ω (hpos u hu) (hne u hu))
    (continuousOn_phase' t ω fun u hu => hpos u hu)
    (continuousOn_ampK' t ω fun u hu => ⟨hpos u hu, hne u hu⟩)
    (fun u hu => amp_eq_ampH_mul t ω (hpos u hu) (hne u hu))
    (fun u hu => ampH'_eq_ampK_mul t ω (hpos u hu) (hne u hu))
  simpa [mI, bdry] using h

theorem ampK'_nonneg {t ω u : ℝ} (ht : 0 ≤ t) (hω : 0 ≤ ω) (hu : 0 < u) : 0 ≤ ampK' t ω u := by
  unfold ampK'
  have : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  positivity

/-- **Second order, monotone case** (`ω, t ≥ 0`): the remainder is at most `2 (|k p| + |k q|)`. -/
theorem norm_integral_add_boundary_le_of_pos {t ω p q : ℝ} (ht : 0 ≤ t) (hω : 0 ≤ ω) (hp : 0 < p)
    (hpq : p ≤ q) (hne : ∀ u ∈ Icc p q, ω * u - t ≠ 0) :
    ‖mI t ω p q + I * (bdry t ω q - bdry t ω p)‖ ≤ 2 * (|ampK t ω p| + |ampK t ω q|) := by
  have hpos : ∀ u ∈ Icc p q, 0 < u := fun u hu => lt_of_lt_of_le hp hu.1
  have h := norm_integral_add_boundary_le_of_monotone hpq (g := fun u => 1 / Real.sqrt u)
    (h := ampH t ω) (h' := ampH' t ω) (k := ampK t ω) (k' := ampK' t ω)
    (Φ := phase t ω) (Φ' := phase' t ω)
    (fun u hu => hasDerivAt_phase t ω (hpos u hu))
    (fun u hu => hasDerivAt_ampH t ω (hpos u hu) (hne u hu))
    (fun u hu => hasDerivAt_ampK t ω (hpos u hu) (hne u hu))
    (continuousOn_phase' t ω fun u hu => hpos u hu)
    (continuousOn_ampK' t ω fun u hu => ⟨hpos u hu, hne u hu⟩)
    (fun u hu => amp_eq_ampH_mul t ω (hpos u hu) (hne u hu))
    (fun u hu => ampH'_eq_ampK_mul t ω (hpos u hu) (hne u hu))
    (Or.inl fun u hu => ampK'_nonneg ht hω (hpos u hu))
  simpa [mI, bdry] using h

/-! ## Size of `h` and `k` near `0` and near `∞` -/

theorem abs_ampH_le_of_small {t ω u : ℝ} (ht : 0 < t) (hsm : ω * u ≤ t / 2) :
    |ampH t ω u| ≤ 2 * Real.sqrt u / t := by
  unfold ampH
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg u), abs_of_neg (by linarith),
    div_le_div_iff₀ (by linarith) ht]
  have := Real.sqrt_nonneg u
  nlinarith

theorem abs_ampK_le_of_small {t ω u : ℝ} (ht : 0 < t) (hω : 0 ≤ ω) (hu : 0 < u)
    (hsm : ω * u ≤ t / 2) : |ampK t ω u| ≤ 6 * Real.sqrt u / t ^ 2 := by
  unfold ampK
  have hωu : 0 ≤ ω * u := by positivity
  have hneg : ω * u - t < 0 := by linarith
  have hd : 2 * (ω * u - t) ^ 3 < 0 := by
    have : (ω * u - t) ^ 3 < 0 := Odd.pow_neg (by decide) hneg
    linarith
  rw [abs_div, abs_of_nonpos (by have := Real.sqrt_nonneg u; nlinarith), abs_of_neg hd, neg_neg,
    div_le_div_iff₀ (by linarith) (by positivity)]
  have hs := Real.sqrt_nonneg u
  have h1 : (t / 2) ^ 3 ≤ (t - ω * u) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h2 : ω * u + t ≤ 3 * t / 2 := by linarith
  have e : -(2 * (ω * u - t) ^ 3) = 2 * (t - ω * u) ^ 3 := by ring
  rw [e]
  have h3 : Real.sqrt u * (ω * u + t) * t ^ 2 ≤ Real.sqrt u * (3 * t / 2) * t ^ 2 := by
    gcongr
  have h4 : 6 * Real.sqrt u * (2 * (t / 2) ^ 3) ≤ 6 * Real.sqrt u * (2 * (t - ω * u) ^ 3) := by
    gcongr
  nlinarith

theorem ampH_le_of_large {t ω u : ℝ} (hω : 0 < ω) (hu : 0 < u)
    (hlg : 2 * t ≤ ω * u) : |ampH t ω u| ≤ 2 / (ω * Real.sqrt u) := by
  have hs := Real.sqrt_pos.mpr hu
  have hs2 := Real.mul_self_sqrt hu.le
  unfold ampH
  have hpos : 0 < ω * u - t := by nlinarith
  rw [abs_div, abs_of_pos hs, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  nlinarith

theorem abs_ampK_le_of_large {t ω u : ℝ} (ht : 0 ≤ t) (hω : 0 < ω) (hu : 1 ≤ u)
    (hlg : 2 * t ≤ ω * u) : |ampK t ω u| ≤ 6 / (ω ^ 2 * Real.sqrt u) := by
  have hu0 : 0 < u := by linarith
  have hs := Real.sqrt_pos.mpr hu0
  have hs2 := Real.mul_self_sqrt hu0.le
  have hs1 : 1 ≤ Real.sqrt u := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hu
  unfold ampK
  have hpos : 0 < ω * u - t := by nlinarith
  rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (ω * u / 2) ^ 3 ≤ (ω * u - t) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h2 : ω * u + t ≤ 3 * (ω * u) / 2 := by linarith
  -- √u (ωu+t) ω² √u ≤ u · (3/2) ω u ω²  and  6 · 2 (ωu/2)³ = (3/2) ω³ u³
  have h3 : Real.sqrt u * (ω * u + t) * (ω ^ 2 * Real.sqrt u) ≤ u * (3 * (ω * u) / 2) * ω ^ 2 := by
    have : Real.sqrt u * (ω * u + t) * (ω ^ 2 * Real.sqrt u)
        = (Real.sqrt u * Real.sqrt u) * (ω * u + t) * ω ^ 2 := by ring
    rw [this, hs2]; gcongr
  have h4 : u * (3 * (ω * u) / 2) * ω ^ 2 ≤ 6 * (2 * (ω * u / 2) ^ 3) := by
    have : 6 * (2 * (ω * u / 2) ^ 3) = u * (3 * (ω * u) / 2) * ω ^ 2 * u := by ring
    rw [this]
    have : 0 ≤ u * (3 * (ω * u) / 2) * ω ^ 2 := by positivity
    nlinarith
  have h5 : 6 * (2 * (ω * u / 2) ^ 3) ≤ 6 * (2 * (ω * u - t) ^ 3) := by gcongr
  linarith


/-- **The initial piece**: for `t > 0`, `ω ≥ 0` and `0 < a` with `ωa < t`,
`‖I(0, a) + i h(a) e^{iΦ(a)}‖ ≤ 2 |k(a)|`. -/
theorem norm_integral_initial_add_boundary_le {t ω a : ℝ} (ht : 0 < t) (hω : 0 ≤ ω) (ha : 0 < a)
    (hat : ω * a < t) : ‖mI t ω 0 a + I * bdry t ω a‖ ≤ 2 * |ampK t ω a| := by
  set C : ℝ := 2 + 2 / t + 12 / t ^ 2 with hC
  have hlim : Tendsto (fun δ : ℝ => 2 * |ampK t ω a| + C * Real.sqrt δ) (𝓝[>] 0)
      (𝓝 (2 * |ampK t ω a| + C * Real.sqrt 0)) :=
    (((Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds).const_mul C).const_add _
  rw [Real.sqrt_zero, mul_zero, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  have hm : 0 < min a (t / (2 * (ω + 1))) := lt_min ha (by positivity)
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 (min a (t / (2 * (ω + 1)))) :=
    Ioo_mem_nhdsGT hm
  filter_upwards [hev] with δ hδ
  obtain ⟨hδ0, hδm⟩ := hδ
  have hδa : δ < a := lt_of_lt_of_le hδm (min_le_left _ _)
  have hδt : δ < t / (2 * (ω + 1)) := lt_of_lt_of_le hδm (min_le_right _ _)
  have hωδ : ω * δ ≤ t / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hδt
    nlinarith
  have hsplit : mI t ω 0 a + I * bdry t ω a
      = mI t ω 0 δ + (mI t ω δ a + I * (bdry t ω a - bdry t ω δ)) + I * bdry t ω δ := by
    rw [← mI_add t ω le_rfl hδ0.le ha.le]; ring
  have hne : ∀ u ∈ Icc δ a, ω * u - t ≠ 0 := by
    intro u hu
    have : ω * u ≤ ω * a := mul_le_mul_of_nonneg_left hu.2 hω
    linarith
  have h1 : ‖mI t ω 0 δ‖ ≤ 2 * Real.sqrt δ := norm_integral_mellin_initial_le t ω hδ0.le
  have h2 := norm_integral_add_boundary_le_of_pos ht.le hω hδ0 hδa.le hne
  have h3 : ‖I * bdry t ω δ‖ ≤ 2 * Real.sqrt δ / t := by
    rw [norm_mul, norm_I, one_mul, norm_bdry]; exact abs_ampH_le_of_small ht hωδ
  have h4 := abs_ampK_le_of_small ht hω hδ0 hωδ
  rw [hsplit]
  calc ‖mI t ω 0 δ + (mI t ω δ a + I * (bdry t ω a - bdry t ω δ)) + I * bdry t ω δ‖
      ≤ ‖mI t ω 0 δ‖ + ‖mI t ω δ a + I * (bdry t ω a - bdry t ω δ)‖ + ‖I * bdry t ω δ‖ :=
        norm_add₃_le
    _ ≤ 2 * Real.sqrt δ + 2 * (6 * Real.sqrt δ / t ^ 2 + |ampK t ω a|) + 2 * Real.sqrt δ / t := by
        gcongr; linarith
    _ = 2 * |ampK t ω a| + C * Real.sqrt δ := by rw [hC]; ring

/-- **The tail**: for `t ≥ 0`, `ω > 0`, `0 < b` with `ωb > t`,
`‖Γ(1-s)(i/ω)^(1-s) − I(0, b) − i h(b) e^{iΦ(b)}‖ ≤ 2 |k(b)|`. -/
theorem norm_mellinMain_sub_integral_sub_boundary_le {t ω b : ℝ} (ht : 0 ≤ t) (hω : 0 < ω)
    (hb : 0 < b) (hbt : t < ω * b) :
    ‖mellinMain t ω - mI t ω 0 b - I * bdry t ω b‖ ≤ 2 * |ampK t ω b| := by
  set D : ℝ := 6 / ω + 12 / ω ^ 2 with hD
  have hlim : Tendsto (fun B : ℝ => 2 * |ampK t ω b| + D * (Real.sqrt B)⁻¹) atTop
      (𝓝 (2 * |ampK t ω b| + D * 0)) :=
    (Real.tendsto_sqrt_atTop.inv_tendsto_atTop.const_mul D).const_add _
  rw [mul_zero, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (max b (max (2 * t / ω) 1))] with B hB
  have hbB : b ≤ B := le_trans (le_max_left _ _) hB
  have hB1 : 1 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hBt : 2 * t ≤ ω * B := by
    have : 2 * t / ω ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
    rw [div_le_iff₀ hω] at this; linarith
  have hB0 : 0 < B := by linarith
  have hsplit : mellinMain t ω - mI t ω 0 b - I * bdry t ω b
      = -(mI t ω 0 B - mellinMain t ω) + (mI t ω b B + I * (bdry t ω B - bdry t ω b))
        - I * bdry t ω B := by
    rw [← mI_add t ω le_rfl hb.le hB0.le]; ring
  have hne : ∀ u ∈ Icc b B, ω * u - t ≠ 0 := by
    intro u hu
    have : ω * b ≤ ω * u := mul_le_mul_of_nonneg_left hu.1 hω.le
    linarith
  have hBt' : t < ω * B := by
    have : ω * b ≤ ω * B := mul_le_mul_of_nonneg_left hbB hω.le
    linarith
  have h1 : ‖mI t ω 0 B - mellinMain t ω‖ ≤ 2 * ampH t ω B := norm_integral_mellin_sub_le ht hB0 hBt'
  have hH := ampH_le_of_large hω hB0 hBt
  have hHpos := ampH_pos hB0 hBt'
  rw [abs_of_pos hHpos] at hH
  have h2 := norm_integral_add_boundary_le_of_pos ht hω.le hb hbB hne
  have h3 : ‖I * bdry t ω B‖ ≤ 2 / (ω * Real.sqrt B) := by
    rw [norm_mul, norm_I, one_mul, norm_bdry, abs_of_pos hHpos]; exact hH
  have h4 := abs_ampK_le_of_large ht hω hB1 hBt
  have hsB := Real.sqrt_pos.mpr hB0
  rw [hsplit]
  calc ‖-(mI t ω 0 B - mellinMain t ω) + (mI t ω b B + I * (bdry t ω B - bdry t ω b))
        - I * bdry t ω B‖
      ≤ ‖-(mI t ω 0 B - mellinMain t ω)‖ + ‖mI t ω b B + I * (bdry t ω B - bdry t ω b)‖
        + ‖I * bdry t ω B‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 2 * (2 / (ω * Real.sqrt B)) + 2 * (|ampK t ω b| + 6 / (ω ^ 2 * Real.sqrt B))
        + 2 / (ω * Real.sqrt B) := by
        rw [norm_neg]
        gcongr
        · exact h1.trans (by linarith)
        · linarith
    _ = 2 * |ampK t ω b| + D * (Real.sqrt B)⁻¹ := by
        rw [hD]; field_simp; ring

/-- **Across the stationary point**: for `t > 0`, `ω > 0` and `0 < a < t/ω < b`,
`‖I(a, b) − Γ(1-s)(i/ω)^(1-s) + i (h(b) E(b) − h(a) E(a))‖ ≤ 2 (|k(a)| + |k(b)|)`. -/
theorem norm_integral_sub_mellinMain_add_boundary_le {t ω a b : ℝ} (ht : 0 < t) (hω : 0 < ω)
    (ha : 0 < a) (hat : ω * a < t) (hbt : t < ω * b) :
    ‖mI t ω a b - mellinMain t ω + I * (bdry t ω b - bdry t ω a)‖
      ≤ 2 * (|ampK t ω a| + |ampK t ω b|) := by
  have hb : 0 < b := by
    by_contra h; push Not at h; nlinarith
  have hsplit : mI t ω a b - mellinMain t ω + I * (bdry t ω b - bdry t ω a)
      = -(mellinMain t ω - mI t ω 0 b - I * bdry t ω b) - (mI t ω 0 a + I * bdry t ω a) := by
    rw [← mI_add t ω le_rfl ha.le hb.le]; ring
  rw [hsplit]
  have h1 := norm_mellinMain_sub_integral_sub_boundary_le ht.le hω hb hbt
  have h2 := norm_integral_initial_add_boundary_le ht hω.le ha hat
  calc _ ≤ ‖-(mellinMain t ω - mI t ω 0 b - I * bdry t ω b)‖ + ‖mI t ω 0 a + I * bdry t ω a‖ :=
        norm_sub_le _ _
    _ ≤ 2 * |ampK t ω b| + 2 * |ampK t ω a| := by rw [norm_neg]; gcongr
    _ = _ := by ring

/-- **The evaluation (R2)**: for `t > 0`, `ν > 0` and `0 < a < t/(2πν) < b`,
`‖∫_a^b u^(-1/2) e(−(t/2π) log u + νu) du − χ(1/2+it) ν^(-1/2+it) + i (h(b) E(b) − h(a) E(a))‖
  ≤ 2 (|k(a)| + |k(b)|) + ν^(-1/2) e^(-πt)`,
with `ω = 2πν`, `h(u) = √u/(ωu − t)`, `k(u) = −√u (ωu + t)/(2 (ωu − t)³)`, `E(u) = e^{i(ωu − t log u)}`. -/
theorem norm_integral_sub_zetaChi_add_boundary_le {t ν a b : ℝ} (ht : 0 < t) (hν : 0 < ν)
    (ha : 0 < a) (hat : 2 * Real.pi * ν * a < t) (hbt : t < 2 * Real.pi * ν * b) :
    ‖mI t (2 * Real.pi * ν) a b - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
        + I * (bdry t (2 * Real.pi * ν) b - bdry t (2 * Real.pi * ν) a)‖
      ≤ 2 * (|ampK t (2 * Real.pi * ν) a| + |ampK t (2 * Real.pi * ν) b|)
        + ν ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * t)) := by
  have h1 := norm_integral_sub_mellinMain_add_boundary_le ht (by positivity) ha hat hbt
  have h2 := norm_mellinMain_sub_zetaChi_le t hν
  calc _ = ‖(mI t (2 * Real.pi * ν) a b - mellinMain t (2 * Real.pi * ν)
          + I * (bdry t (2 * Real.pi * ν) b - bdry t (2 * Real.pi * ν) a))
          + (mellinMain t (2 * Real.pi * ν)
            - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1))‖ := by
        congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (by gcongr)


end ZetaMellinPhase

end RiemannHypothesis
