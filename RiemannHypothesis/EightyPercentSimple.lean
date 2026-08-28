/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.EightyPercent
import RiemannHypothesis.OffLine

/-!
# Eighty per cent of the distinct zeroes of `ζ` are simple

`RiemannHypothesis.EightyPercent` records two unconditional `80 %` statistics of the zeroes
of `ζ` and of `ξ′`.  This file adds a third, about the *simplicity* of the nontrivial zeroes
of `ζ` themselves:

> **At least 80 % of the distinct nontrivial zeroes of `ζ` are simple.**

The proportion is taken with respect to `N_d`, the number of *distinct* nontrivial zeroes in
the window — the natural denominator for a statement about how many points are simple.

The argument is elementary given Theorem D of `RiemannHypothesis.Zeta23Bridge` (the
Montgomery–Taylor form of Theorem C).  In a window, write `N` for the number of zeroes with
multiplicity, `N_d` for the number of distinct zeroes and `Nˢ` for the number of simple ones.
Each non-simple zero contributes at least `2` to `N`, so

`N ≥ Nˢ + 2·(N_d − Nˢ)`,  i.e.  `2·N_d ≤ Nˢ + N`   (`two_mul_windowCountDistinct_le_add`).

Hence `Nˢ/N_d ≥ 2 − N/N_d`, and any lower bound `c` for `N_d/N` gives `Nˢ/N_d ≥ 2 − 1/c`.
Theorem C (`c = 5/6`) already gives `Nˢ/N_d ≥ 4/5` in the limit
(`four_fifths_simple_among_distinct`), and Theorem D, whose constant
`(3 − 1/c₁*)/2 = 0.83625…` is strictly larger than `5/6`, upgrades this to the `ε`-free
`0.8·N_d ≤ Nˢ` for all large `T` (`eighty_percent_simple_among_distinct`).

The only numerical input is `3/4 < c₁*` (`mtConstant_gt_three_quarters`), which is proved here
from Mathlib's Taylor bounds for `sin` and `cos`.

The last section runs the same argument for the derivative `ξ′` of the completed zeta
function, whose distinctness constant `0.93432` is larger still: at least `92 %` of the
distinct zeroes of `ξ′` are simple
(`ninety_two_percent_simple_among_distinct_xiDeriv`), and for a primitive Dirichlet character
`χ` modulo `q > 1`, where Theorem E supplies the same Montgomery–Taylor constant: at least
`80 %` of the distinct nontrivial zeroes of `L(·, χ)` are simple
(`eighty_percent_simple_among_distinctL`).

Nothing in this file bears on the proportion of zeroes *on the critical line*: raising that
proportion (currently `2/3`, `RiemannHypothesis.Zeta23Bridge.two_thirds_on_critical_line`) to
`80 %` is an open research problem, and no such statement is proved anywhere in this
repository.  The last section writes that open target down as a `Prop`,
`EightyPercentOnCriticalLine`, in the style of `RiemannHypothesis.Partial` — a statement, not a
theorem — together with what it would give: at most a fifth of the zeroes off the line
(`one_fifth_off_critical_line_of_eightyPercent`).
-/

noncomputable section

open Complex Filter Set

namespace RiemannHypothesis

/-! ## The simple zeroes in a window -/

/-- `Nˢ(T₁, T₂)`: the number of *simple* nontrivial zeroes of `ζ` with `T₁ < im ρ ≤ T₂`
(distinct points, each of multiplicity one). -/
def windowCountSimple (T₁ T₂ : ℝ) : ℕ :=
  (windowZeros T₁ T₂ ∩ {ρ | zeroMultiplicity ρ = 1}).ncard

lemma windowCountSimple_eq (T₁ T₂ : ℝ) : windowCountSimple T₁ T₂ = Zeta23.Nsimple T₁ T₂ := by
  simp only [windowCountSimple, Zeta23.Nsimple, windowZeros_eq, zeroMultiplicity]
  rfl

/-- A nontrivial zero has multiplicity at least one. -/
lemma one_le_zeroMultiplicity_of_mem {T₁ T₂ : ℝ} {ρ : ℂ} (h : ρ ∈ windowZeros T₁ T₂) :
    1 ≤ zeroMultiplicity ρ := by
  rw [windowZeros_eq] at h
  exact Zeta23.zetaSeam.one_le_mult ρ h.1

/-! ## The counting inequality `2·N_d ≤ Nˢ + N` -/

/-- **Each non-simple point costs an extra unit of multiplicity.**  For a finite set `S` of
points carrying multiplicities `m ρ ≥ 1`, twice the number of points is at most the number of
*simple* points plus the total multiplicity. -/
lemma two_mul_ncard_le_ncard_simple_add_finsum {S : Set ℂ} (hS : S.Finite) (m : ℂ → ℕ)
    (hm : ∀ ρ ∈ S, 1 ≤ m ρ) :
    2 * S.ncard ≤ (S ∩ {ρ | m ρ = 1}).ncard + ∑ᶠ ρ ∈ S, m ρ := by
  classical
  set F := hS.toFinset with hF
  have hmemF : ∀ ρ, ρ ∈ F ↔ ρ ∈ S := by
    intro ρ; rw [hF, Set.Finite.mem_toFinset]
  have hN : ∑ᶠ ρ ∈ S, m ρ = ∑ ρ ∈ F, m ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hNd : S.ncard = F.card := by
    rw [← Set.ncard_coe_finset, hF, Set.Finite.coe_toFinset]
  have hNs : (S ∩ {ρ | m ρ = 1}).ncard = (F.filter fun ρ => m ρ = 1).card := by
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    congr 1
    ext ρ
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hmemF]
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun ρ => m ρ = 1) m
  have h1 : ∑ ρ ∈ F.filter (fun ρ => m ρ = 1), m ρ = (F.filter fun ρ => m ρ = 1).card := by
    rw [Finset.sum_congr rfl fun ρ hρ => (Finset.mem_filter.mp hρ).2, Finset.sum_const,
      smul_eq_mul, mul_one]
  have h2 : 2 * (F.filter fun ρ => ¬m ρ = 1).card
      ≤ ∑ ρ ∈ F.filter (fun ρ => ¬m ρ = 1), m ρ := by
    calc 2 * (F.filter fun ρ => ¬m ρ = 1).card
        = ∑ _ρ ∈ F.filter (fun ρ => ¬m ρ = 1), 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ ρ ∈ F.filter (fun ρ => ¬m ρ = 1), m ρ := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          obtain ⟨hρF, hρ1⟩ := Finset.mem_filter.mp hρ
          have := hm ρ ((hmemF ρ).mp hρF)
          omega
  have h3 : (F.filter fun ρ => m ρ = 1).card + (F.filter fun ρ => ¬m ρ = 1).card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) fun ρ => m ρ = 1
  omega

/-- **Each non-simple zero costs an extra unit of multiplicity**: in every window,
`2·N_d ≤ Nˢ + N`.  Equivalently `Nˢ ≥ N_d − (N − N_d)`: the number of distinct zeroes that
fail to be simple is at most the multiplicity excess `N − N_d`. -/
lemma two_mul_windowCountDistinct_le_add (T₁ T₂ : ℝ) :
    2 * windowCountDistinct T₁ T₂ ≤ windowCountSimple T₁ T₂ + windowCount T₁ T₂ :=
  two_mul_ncard_le_ncard_simple_add_finsum (windowZeros_finite T₁ T₂) zeroMultiplicity
    fun _ hρ => one_le_zeroMultiplicity_of_mem hρ

/-! ## Four fifths from Theorem C -/

/-- **At least 80 % of the distinct nontrivial zeroes of `ζ` are simple**, in `ε`-form:
for every `ε > 0` and all large `T`, `(4/5 − ε)·N_d(T,2T) ≤ Nˢ(T,2T)`.  A consequence of
Theorem C (`N_d/N ≥ 5/6`). -/
theorem four_fifths_simple_among_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 / 5 - ε) * (windowCountDistinct T (2 * T) : ℝ) ≤ windowCountSimple T (2 * T) := by
  intro ε hε
  have hpos : (0 : ℝ) < 6 + 5 * ε := by linarith
  obtain ⟨T₀, hT₀⟩ := five_sixths_distinct (5 / 6 - 5 / (6 + 5 * ε)) (by
    have h5 : 5 / (6 + 5 * ε) < 5 / 6 := by
      rw [div_lt_div_iff₀ hpos (by norm_num)]; linarith
    linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  rw [sub_sub_cancel] at h
  have hkey : 5 * (windowCount T (2 * T) : ℝ)
      ≤ (6 + 5 * ε) * (windowCountDistinct T (2 * T) : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at h
    linarith
  have hcount : 2 * (windowCountDistinct T (2 * T) : ℝ)
      ≤ (windowCountSimple T (2 * T) : ℝ) + windowCount T (2 * T) := by
    exact_mod_cast two_mul_windowCountDistinct_le_add T (2 * T)
  linarith

/-- **At least 80 % of the distinct nontrivial zeroes of `ζ` are simple**, cumulative form of
`four_fifths_simple_among_distinct`. -/
theorem four_fifths_simple_among_distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 / 5 - ε) * (windowCountDistinct 0 T : ℝ) ≤ windowCountSimple 0 T := by
  intro ε hε
  have hpos : (0 : ℝ) < 6 + 5 * ε := by linarith
  obtain ⟨T₀, hT₀⟩ := five_sixths_distinct_cumulative (5 / 6 - 5 / (6 + 5 * ε)) (by
    have h5 : 5 / (6 + 5 * ε) < 5 / 6 := by
      rw [div_lt_div_iff₀ hpos (by norm_num)]; linarith
    linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  rw [sub_sub_cancel] at h
  have hkey : 5 * (windowCount 0 T : ℝ) ≤ (6 + 5 * ε) * (windowCountDistinct 0 T : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at h
    linarith
  have hcount : 2 * (windowCountDistinct 0 T : ℝ)
      ≤ (windowCountSimple 0 T : ℝ) + windowCount 0 T := by
    exact_mod_cast two_mul_windowCountDistinct_le_add 0 T
  linarith

/-! ## The Montgomery–Taylor constant exceeds `3/4` -/

/-- `1 − x²/2 < cos x` for `x > 0`: the strict form of Mathlib's `one_sub_sq_div_two_le_cos`,
obtained from `sin t < t`. -/
theorem one_sub_sq_div_two_lt_cos {x : ℝ} (hx : 0 < x) : 1 - x ^ 2 / 2 < Real.cos x := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => Real.cos t - (1 - t ^ 2 / 2)) (-Real.sin t + t) t := by
    intro t
    have h1 : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
    have h2 : HasDerivAt (fun t : ℝ => 1 - t ^ 2 / 2) (-t) t :=
      ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).congr_deriv (by
        push_cast; ring)
    exact (h1.sub h2).congr_deriv (by ring)
  have hmono : StrictMonoOn (fun t : ℝ => Real.cos t - (1 - t ^ 2 / 2)) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun t _ => ((hderiv t).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      linarith [Real.sin_lt (Set.mem_Ioi.1 ht)]
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
  simp only [Real.cos_zero] at h
  norm_num at h
  linarith

/-- The sharp cubic lower bound `x − x³/6 < sin x` for `x > 0`.  Mathlib only provides the
weaker `x − x³/4 < sin x`; the sharper form follows by integrating `1 − t²/2 < cos t`. -/
theorem sin_gt_sub_cube_div_six {x : ℝ} (hx : 0 < x) : x - x ^ 3 / 6 < Real.sin x := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.sin t - (t - t ^ 3 / 6))
      (Real.cos t - (1 - 3 * t ^ 2 / 6)) t := by
    intro t
    have hs : HasDerivAt Real.sin (Real.cos t) t := Real.hasDerivAt_sin t
    have hp : HasDerivAt (fun t : ℝ => t - t ^ 3 / 6) (1 - 3 * t ^ 2 / 6) t :=
      ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).congr_deriv (by
        push_cast; ring)
    exact hs.sub hp
  have hmono : StrictMonoOn (fun t : ℝ => Real.sin t - (t - t ^ 3 / 6)) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun t _ => ((hderiv t).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      linarith [one_sub_sq_div_two_lt_cos (Set.mem_Ioi.1 ht)]
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
  simp only [Real.sin_zero] at h
  norm_num at h
  linarith

/-- `tan (1/√2) > 3√2/5`.  Proved from `x − x³/6 < sin x` and Mathlib's Taylor bound for
`cos`; at `x = 1/√2` these give `5·sin x > 55√2/24` and `3√2·cos x ≤ 879√2/384 < 880√2/384`. -/
lemma tan_one_div_sqrt_two_gt : 3 * Real.sqrt 2 / 5 < Real.tan (1 / Real.sqrt 2) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlb : (1.41 : ℝ) < Real.sqrt 2 := by nlinarith [hsq, h2]
  set x : ℝ := 1 / Real.sqrt 2 with hx
  have hxpos : 0 < x := by positivity
  have hx2 : x ^ 2 = 1 / 2 := by
    rw [hx]; field_simp; nlinarith [hsq]
  have hxlt1 : x < 1 := by rw [hx, div_lt_one h2]; linarith
  have hxle : |x| ≤ 1 := by rw [abs_of_pos hxpos]; linarith
  have hsin : x - x ^ 3 / 6 < Real.sin x := sin_gt_sub_cube_div_six hxpos
  have hcosle : Real.cos x ≤ 1 - x ^ 2 / 2 + |x| ^ 4 * (5 / 96) := by
    have := abs_le.mp (Real.cos_bound hxle)
    linarith [this.2]
  have hxabs : |x| = x := abs_of_pos hxpos
  have hcospos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  have hx3 : x ^ 3 = x / 2 := by nlinarith [hx2]
  have hx4 : x ^ 4 = 1 / 4 := by nlinarith [hx2]
  have hxval : x = Real.sqrt 2 / 2 := by
    rw [hx]; field_simp; nlinarith [hsq]
  rw [Real.tan_eq_sin_div_cos, div_lt_div_iff₀ (by norm_num) hcospos]
  rw [hxabs, hx4] at hcosle
  nlinarith [hsin, hcosle, hx3, hxval, h2]

/-- The Montgomery–Taylor constant `c₁* = 0.7532960…` exceeds `3/4`.  This is exactly what
makes Theorem D's distinctness constant `(3 − 1/c₁*)/2` exceed Theorem C's `5/6`. -/
theorem mtConstant_gt_three_quarters : 3 / 4 < mtConstant := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htan := tan_one_div_sqrt_two_gt
  have htanpos : 0 < Real.tan (1 / Real.sqrt 2) := lt_of_le_of_lt (by positivity) htan
  have hden : 0 < 1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) := by positivity
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp; nlinarith [hsq]
  set u : ℝ := Real.tan (1 / Real.sqrt 2) with hu
  rw [mtConstant, ← hu, lt_div_iff₀ hden]
  have h1 : 1 / Real.sqrt 2 * u = Real.sqrt 2 / 2 * u := by rw [hinv]
  have hkey : 6 / 5 < Real.sqrt 2 * u := by nlinarith [htan, hsq, h2]
  linarith [h1, hkey]

/-! ## Eighty per cent, `ε`-free, from Theorem D -/

/-- **At least 80 % of the distinct nontrivial zeroes of `ζ` are simple** (dyadic windows), in
`ε`-free form: for all large `T`, `0.8·N_d(T,2T) ≤ Nˢ(T,2T)`. -/
theorem eighty_percent_simple_among_distinct :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.8 : ℝ) * (windowCountDistinct T (2 * T) : ℝ) ≤ windowCountSimple T (2 * T) := by
  have hc : 3 / 4 < mtConstant := mtConstant_gt_three_quarters
  have hc0 : (0 : ℝ) < mtConstant := by linarith
  have hG : 5 / 6 < 3 / 2 - mtConstant⁻¹ / 2 := by
    have : mtConstant⁻¹ < 4 / 3 := by
      rw [inv_lt_comm₀ hc0 (by norm_num)]; linarith
    linarith
  set ε : ℝ := 3 / 2 - mtConstant⁻¹ / 2 - 5 / 6 with hεdef
  obtain ⟨T₀, hT₀⟩ := montgomery_taylor_distinct ε (by rw [hεdef]; linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hred : 3 / 2 - mtConstant⁻¹ / 2 - ε = 5 / 6 := by rw [hεdef]; ring
  rw [hred] at h
  have hcount : 2 * (windowCountDistinct T (2 * T) : ℝ)
      ≤ (windowCountSimple T (2 * T) : ℝ) + windowCount T (2 * T) := by
    exact_mod_cast two_mul_windowCountDistinct_le_add T (2 * T)
  norm_num
  linarith

/-- **At least 80 % of the distinct nontrivial zeroes of `ζ` are simple**, cumulative form of
`eighty_percent_simple_among_distinct`. -/
theorem eighty_percent_simple_among_distinct_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.8 : ℝ) * (windowCountDistinct 0 T : ℝ) ≤ windowCountSimple 0 T := by
  have hc : 3 / 4 < mtConstant := mtConstant_gt_three_quarters
  have hc0 : (0 : ℝ) < mtConstant := by linarith
  have hG : 5 / 6 < 3 / 2 - mtConstant⁻¹ / 2 := by
    have : mtConstant⁻¹ < 4 / 3 := by
      rw [inv_lt_comm₀ hc0 (by norm_num)]; linarith
    linarith
  set ε : ℝ := 3 / 2 - mtConstant⁻¹ / 2 - 5 / 6 with hεdef
  obtain ⟨T₀, hT₀⟩ := montgomery_taylor_distinct_cumulative ε (by rw [hεdef]; linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hred : 3 / 2 - mtConstant⁻¹ / 2 - ε = 5 / 6 := by rw [hεdef]; ring
  rw [hred] at h
  have hcount : 2 * (windowCountDistinct 0 T : ℝ)
      ≤ (windowCountSimple 0 T : ℝ) + windowCount 0 T := by
    exact_mod_cast two_mul_windowCountDistinct_le_add 0 T
  norm_num
  linarith

/-! ## The eighty per cent as a ratio: `liminf Nˢ/N_d ≥ 4/5` -/

/-- A simple zero is in particular a zero of the window. -/
lemma windowCountSimple_le_windowCountDistinct (T₁ T₂ : ℝ) :
    windowCountSimple T₁ T₂ ≤ windowCountDistinct T₁ T₂ :=
  Set.ncard_le_ncard Set.inter_subset_left (windowZeros_finite T₁ T₂)

/-- The number of distinct nontrivial zeroes of `(0, T]` tends to infinity: the denominator of
the ratio below is eventually positive.  A consequence of `N_d ≥ (2/3)·N` and `N(0,T) → ∞`. -/
lemma tendsto_windowCountDistinct_atTop :
    Tendsto (fun T : ℝ => (windowCountDistinct 0 T : ℝ)) atTop atTop := by
  obtain ⟨T₀, hT₀⟩ := five_sixths_distinct_cumulative (1 / 6) (by norm_num)
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_windowCount_atTop.const_mul_atTop (r := 2 / 3) (by norm_num))
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have h := hT₀ T hT
  norm_num at h ⊢
  linarith

/-- **At least 80 % of the distinct nontrivial zeroes of `ζ` are simple**, as a statement about
the ratio: `liminf_{T→∞} Nˢ(0,T)/N_d(0,T) ≥ 4/5`. -/
theorem four_fifths_le_liminf_windowCountSimple_div_windowCountDistinct :
    4 / 5 ≤ liminf (fun T : ℝ =>
      (windowCountSimple 0 T : ℝ) / (windowCountDistinct 0 T : ℝ)) atTop := by
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun T : ℝ => (windowCountSimple 0 T : ℝ) / (windowCountDistinct 0 T : ℝ)) := by
    refine ⟨1, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with T
    rcases Nat.eq_zero_or_pos (windowCountDistinct 0 T) with h0 | hpos
    · simp [h0]
    · have hposR : (0 : ℝ) < windowCountDistinct 0 T := by exact_mod_cast hpos
      rw [div_le_one hposR]
      exact_mod_cast windowCountSimple_le_windowCountDistinct 0 T
  refine le_liminf_of_le hbdd.isCoboundedUnder_ge ?_
  obtain ⟨T₀, hT₀⟩ := eighty_percent_simple_among_distinct_cumulative
  filter_upwards [eventually_ge_atTop T₀,
    tendsto_windowCountDistinct_atTop.eventually_gt_atTop 0] with T hT hpos
  rw [le_div_iff₀ hpos]
  have h := hT₀ T hT
  norm_num at h ⊢
  linarith

/-! ## The same for `ξ′`: more than 92 % of its distinct zeroes are simple -/

/-- `Nˢ_{ξ′}(T₁,T₂)`: the simple zeroes of `ξ′` in the window `(T₁, T₂]`. -/
def xiDerivWindowCountSimple (T₁ T₂ : ℝ) : ℕ :=
  (xiDerivWindowZeros T₁ T₂ ∩ {ρ | xiDerivMultiplicity ρ = 1}).ncard

lemma xiDerivWindowZeros_finite (T₁ T₂ : ℝ) : (xiDerivWindowZeros T₁ T₂).Finite := by
  rw [xiDerivWindowZeros_eq]
  exact Zeta23.XiPrime.zerosIn_finite T₁ T₂

lemma one_le_xiDerivMultiplicity_of_mem {T₁ T₂ : ℝ} {ρ : ℂ}
    (h : ρ ∈ xiDerivWindowZeros T₁ T₂) : 1 ≤ xiDerivMultiplicity ρ := by
  rw [xiDerivWindowZeros_eq] at h
  rw [xiDerivMultiplicity_eq]
  exact Zeta23.XiPrime.xiDerivZeros₀.one_le_mult ρ h.1

lemma two_mul_xiDerivWindowCountDistinct_le_add (T₁ T₂ : ℝ) :
    2 * xiDerivWindowCountDistinct T₁ T₂
      ≤ xiDerivWindowCountSimple T₁ T₂ + xiDerivWindowCount T₁ T₂ :=
  two_mul_ncard_le_ncard_simple_add_finsum (xiDerivWindowZeros_finite T₁ T₂) xiDerivMultiplicity
    fun _ hρ => one_le_xiDerivMultiplicity_of_mem hρ

/-- **At least 92 % of the distinct zeroes of `ξ′` are simple** (dyadic windows).  From the
`0.93432` distinctness constant of the vendored `Zeta23` library: `2 − 1/0.93432 = 0.9296…`. -/
theorem ninety_two_percent_simple_among_distinct_xiDeriv :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.92 : ℝ) * (xiDerivWindowCountDistinct T (2 * T) : ℝ)
        ≤ xiDerivWindowCountSimple T (2 * T) := by
  obtain ⟨T₀, hT₀⟩ := Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std
  refine ⟨T₀, fun T hT => ?_⟩
  have h := (hT₀ T hT).2
  rw [← xiDerivWindowCount_eq, ← xiDerivWindowCountDistinct_eq] at h
  have hcount : 2 * (xiDerivWindowCountDistinct T (2 * T) : ℝ)
      ≤ (xiDerivWindowCountSimple T (2 * T) : ℝ) + xiDerivWindowCount T (2 * T) := by
    exact_mod_cast two_mul_xiDerivWindowCountDistinct_le_add T (2 * T)
  have hN0 : (0 : ℝ) ≤ (xiDerivWindowCount T (2 * T) : ℝ) := Nat.cast_nonneg _
  norm_num
  linarith

/-- **At least 92 % of the distinct zeroes of `ξ′` are simple**, cumulative form. -/
theorem ninety_two_percent_simple_among_distinct_xiDeriv_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.92 : ℝ) * (xiDerivWindowCountDistinct 0 T : ℝ) ≤ xiDerivWindowCountSimple 0 T := by
  obtain ⟨T₀, hT₀⟩ := Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_cumulative_std
  refine ⟨T₀, fun T hT => ?_⟩
  have h := (hT₀ T hT).2
  rw [← xiDerivWindowCount_eq, ← xiDerivWindowCountDistinct_eq] at h
  have hcount : 2 * (xiDerivWindowCountDistinct 0 T : ℝ)
      ≤ (xiDerivWindowCountSimple 0 T : ℝ) + xiDerivWindowCount 0 T := by
    exact_mod_cast two_mul_xiDerivWindowCountDistinct_le_add 0 T
  have hN0 : (0 : ℝ) ≤ (xiDerivWindowCount 0 T : ℝ) := Nat.cast_nonneg _
  norm_num
  linarith

/-! ## The same for a Dirichlet `L`-function -/

section Dirichlet

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- `Nˢ_χ(T₁, T₂)`: the simple nontrivial zeroes of `L(·, χ)` in the window `(T₁, T₂]`. -/
def windowCountSimpleL (T₁ T₂ : ℝ) : ℕ :=
  (windowZerosL χ T₁ T₂ ∩ {ρ | zeroMultiplicityL χ ρ = 1}).ncard

variable (hq : 1 < q) (hχ : χ.IsPrimitive)

include hq hχ

lemma windowZerosL_finite (T₁ T₂ : ℝ) : (windowZerosL χ T₁ T₂).Finite := by
  have h := Zeta23.ThmE.LSeam_finite_window (χ := χ) hq hχ T₁ T₂
  rw [windowZerosL_eq]
  exact h.subset fun ρ hρ => ⟨hρ.1, hρ.2⟩

lemma one_le_zeroMultiplicityL_of_mem {T₁ T₂ : ℝ} {ρ : ℂ} (h : ρ ∈ windowZerosL χ T₁ T₂) :
    1 ≤ zeroMultiplicityL χ ρ := by
  rw [windowZerosL_eq] at h
  exact Zeta23.ThmE.LSeam_one_le_mult hq hχ ρ h.1

lemma two_mul_windowCountDistinctL_le_add (T₁ T₂ : ℝ) :
    2 * windowCountDistinctL χ T₁ T₂
      ≤ windowCountSimpleL χ T₁ T₂ + windowCountL χ T₁ T₂ :=
  two_mul_ncard_le_ncard_simple_add_finsum (windowZerosL_finite χ hq hχ T₁ T₂)
    (zeroMultiplicityL χ) fun _ hρ => one_le_zeroMultiplicityL_of_mem χ hq hχ hρ

/-- **At least 80 % of the distinct nontrivial zeroes of `L(·, χ)` are simple**, for `χ`
primitive modulo `q > 1`: for all large `T`, `0.8·N_{d,χ}(T,2T) ≤ Nˢ_χ(T,2T)`. -/
theorem eighty_percent_simple_among_distinctL :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.8 : ℝ) * (windowCountDistinctL χ T (2 * T) : ℝ) ≤ windowCountSimpleL χ T (2 * T) := by
  have hc : 3 / 4 < mtConstant := mtConstant_gt_three_quarters
  have hc0 : (0 : ℝ) < mtConstant := by linarith
  have hG : 5 / 6 < 3 / 2 - mtConstant⁻¹ / 2 := by
    have : mtConstant⁻¹ < 4 / 3 := by
      rw [inv_lt_comm₀ hc0 (by norm_num)]; linarith
    linarith
  set ε : ℝ := 3 / 2 - mtConstant⁻¹ / 2 - 5 / 6 with hεdef
  obtain ⟨T₀, hT₀⟩ := dirichlet_montgomery_taylor_distinct χ hq hχ ε (by rw [hεdef]; linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hred : 3 / 2 - mtConstant⁻¹ / 2 - ε = 5 / 6 := by rw [hεdef]; ring
  rw [hred] at h
  have hcount : 2 * (windowCountDistinctL χ T (2 * T) : ℝ)
      ≤ (windowCountSimpleL χ T (2 * T) : ℝ) + windowCountL χ T (2 * T) := by
    exact_mod_cast two_mul_windowCountDistinctL_le_add χ hq hχ T (2 * T)
  norm_num
  linarith

end Dirichlet

/-! ## The open target: eighty per cent *on the critical line* -/

/-- **The eighty per cent statement for the critical line**, as a `Prop`:
`liminf N₀*(T,2T)/N(T,2T) ≥ 4/5`, i.e. at least `80 %` of the nontrivial zeroes of `ζ` lie on
the critical line.  In the style of `RiemannHypothesis.Partial`, this is a *statement only*:
it is **not** proved here, and nothing in this repository proves it.  What is proved is the
weaker `two_thirds_on_critical_line` (`2/3`), and — for the different statistics of simplicity
and distinctness — the `80 %` theorems of this file and of
`RiemannHypothesis.EightyPercent`. -/
def EightyPercentOnCriticalLine : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (4 / 5 - ε) * (windowCount T (2 * T) : ℝ) ≤ windowCountOnLine T (2 * T)

/-- What the open statement would buy: at most a fifth of the zeroes off the critical line.
The hypothesis is `EightyPercentOnCriticalLine`, which is **not** proved here. -/
theorem one_fifth_off_critical_line_of_eightyPercent (h : EightyPercentOnCriticalLine) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (windowCountOffLine T (2 * T) : ℝ) ≤ (1 / 5 + ε) * windowCount T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hsplit : (windowCountOffLine T (2 * T) : ℝ) + windowCountOnLine T (2 * T)
      = windowCountDistinct T (2 * T) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (windowCountOffLine_add_windowCountOnLine T (2 * T))
  have hle : (windowCountDistinct T (2 * T) : ℝ) ≤ windowCount T (2 * T) := by
    exact_mod_cast windowCountDistinct_le_windowCount T (2 * T)
  linarith [hT₀ T hT]

end RiemannHypothesis

end
