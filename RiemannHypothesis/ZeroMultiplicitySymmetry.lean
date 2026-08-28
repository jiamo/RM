/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.OffLineQuadruple
import RiemannHypothesis.Xi
import RiemannHypothesis.Zeta23Bridge

/-!
# The symmetries preserve the multiplicity of a zero

`RiemannHypothesis.ZeroSymmetryCount` and `RiemannHypothesis.OffLineQuadruple` show that the set
of nontrivial zeroes of `ζ` is stable under conjugation `s ↦ conj s`, under the
functional-equation reflection `s ↦ 1 - s`, and hence under the reflection
`criticalReflect s = 1 - conj s` in the critical line — but both files count zeroes *without*
multiplicity, and record that the corresponding statements with multiplicity would need the
orders of vanishing at `ρ` and at its companions to agree.  This file proves exactly that, and
removes the caveat:

* `analyticOrderAt_conj_conj` — a general fact about holomorphic functions: the vanishing order
  of `z ↦ conj (f (conj z))` at `conj z₀` equals the order of `f` at `z₀`;
* `analyticOrderAt_completedRiemannZeta_eq` — inside the critical strip `ζ` and the completed
  zeta function `Λ` vanish to the same order, since they differ by the nonvanishing analytic
  factor `Γ_ℝ`;
* `zeroMultiplicity_conj`, `zeroMultiplicity_one_sub`, `zeroMultiplicity_criticalReflect` —
  **the multiplicity of a zero in the critical strip is unchanged by each of the three
  symmetries**;
* `multCount`, `offLineMultCount` — the counting functions of the zeroes of height at most `T`,
  and of those off the critical line, counted **with multiplicity**;
* `even_multCount` — `N(T)` counted with multiplicity is even;
* `offLineMultCount_eq_four_mul` and `four_dvd_offLineMultCount` — the off-line count with
  multiplicity is four times the count of the upper-left off-line zeroes, hence divisible by `4`.

As everywhere in this repository, nothing here decides whether any off-line zero exists: the
Riemann hypothesis is neither proved nor disproved.
-/

noncomputable section

open Complex Filter

open scoped Topology

namespace RiemannHypothesis

/-! ## Vanishing order under conjugation -/

/-- If `f` is analytic at `z₀`, then `z ↦ conj (f (conj z))` is analytic at `conj z₀`. -/
lemma analyticAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    AnalyticAt ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) ((starRingEnd ℂ) z₀) := by
  obtain ⟨U, hU, hUopen, hz₀⟩ := eventually_nhds_iff.1 hf.eventually_analyticAt
  refine DifferentiableOn.analyticAt (s := (starRingEnd ℂ) ⁻¹' U) ?_ ?_
  · intro w hw
    have hdiff : DifferentiableAt ℂ f ((starRingEnd ℂ) w) := (hU _ hw).differentiableAt
    have := hdiff.conj_conj
    simp only [Complex.conj_conj, Function.comp_def] at this
    exact this.differentiableWithinAt
  · exact (hUopen.preimage (Complex.continuous_conj)).mem_nhds (by simpa using hz₀)

/-- **Vanishing order is preserved by conjugation**: the order of `z ↦ conj (f (conj z))` at
`conj z₀` is the order of `f` at `z₀`. -/
lemma analyticOrderAt_conj_conj (f : ℂ → ℂ) (z₀ : ℂ) :
    analyticOrderAt (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) ((starRingEnd ℂ) z₀)
      = analyticOrderAt f z₀ := by
  have htend : Tendsto (starRingEnd ℂ) (𝓝 ((starRingEnd ℂ) z₀)) (𝓝 z₀) := by
    simpa using (Complex.continuous_conj.tendsto ((starRingEnd ℂ) z₀))
  by_cases hf : AnalyticAt ℂ f z₀
  · rcases eq_or_ne (analyticOrderAt f z₀) ⊤ with htop | hfin
    · rw [htop, analyticOrderAt_eq_top]
      filter_upwards [htend.eventually (analyticOrderAt_eq_top.mp htop)] with w hw
      simp [hw]
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
      obtain ⟨g, hg, hgne, hfg⟩ := (hf.analyticOrderAt_eq_natCast (n := n)).mp hn.symm
      rw [← hn, (analyticAt_conj_conj hf).analyticOrderAt_eq_natCast]
      refine ⟨fun z => (starRingEnd ℂ) (g ((starRingEnd ℂ) z)), analyticAt_conj_conj hg,
        by simpa using hgne, ?_⟩
      filter_upwards [htend.eventually hfg] with w hw
      simp only [smul_eq_mul] at hw ⊢
      rw [hw, map_mul, map_pow, map_sub, Complex.conj_conj]
  · have hnot : ¬ AnalyticAt ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
        ((starRingEnd ℂ) z₀) := by
      intro h
      exact hf (by simpa using analyticAt_conj_conj h)
    rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt hnot]

/-! ## Analyticity of `ζ` and `Λ` -/

lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 1})
    (fun _z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_ne.mem_nhds hs)

lemma analyticAt_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s :=
  DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 0} ∩ {z : ℂ | z ≠ 1})
    (fun _z hz => (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt)
    ((isOpen_ne.inter isOpen_ne).mem_nhds ⟨h0, h1⟩)

/-- Inside the critical strip `ζ` and the completed zeta function vanish to the same order:
they differ by the nonvanishing analytic factor `Γ_ℝ`. -/
lemma analyticOrderAt_completedRiemannZeta_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderAt completedRiemannZeta s = analyticOrderAt riemannZeta s := by
  have hne0 : s ≠ 0 := fun h => by simp [h] at h0
  have hne1 : s ≠ 1 := fun h => by simp [h] at h1
  have hinv : AnalyticAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    DifferentiableOn.analyticAt (s := Set.univ) differentiable_Gammaℝ_inv.differentiableOn
      Filter.univ_mem
  have hev : riemannZeta =ᶠ[𝓝 s] completedRiemannZeta * (fun z : ℂ => (Gammaℝ z)⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hne0] with z hz
    simpa [div_eq_mul_inv] using riemannZeta_def_of_ne_zero hz
  have hzero : analyticOrderAt (fun z : ℂ => (Gammaℝ z)⁻¹) s = 0 :=
    hinv.analyticOrderAt_eq_zero.2 (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h0))
  rw [analyticOrderAt_congr hev,
    analyticOrderAt_mul (analyticAt_completedRiemannZeta hne0 hne1) hinv, hzero, add_zero]

/-! ## The multiplicity of a nontrivial zero under the two symmetries -/

/-- **The multiplicity of a zero is unchanged by conjugation.** -/
theorem zeroMultiplicity_conj {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zeroMultiplicity ((starRingEnd ℂ) s) = zeroMultiplicity s := by
  have hstrip : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : ((starRingEnd ℂ) s) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    simpa using ⟨h0, h1⟩
  have hev : riemannZeta
      =ᶠ[𝓝 ((starRingEnd ℂ) s)] fun z => (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z)) := by
    filter_upwards [hstrip.mem_nhds hmem] with w hw
    rw [riemannZeta_conj_of_mem_strip hw.1 hw.2, Complex.conj_conj]
  unfold zeroMultiplicity
  rw [analyticOrderAt_congr hev, analyticOrderAt_conj_conj]

/-- **The multiplicity of a zero is unchanged by the functional-equation reflection
`s ↦ 1 - s`.** -/
theorem zeroMultiplicity_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zeroMultiplicity (1 - s) = zeroMultiplicity s := by
  have h0' : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h1' : (1 - s).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hcomp : analyticOrderAt (completedRiemannZeta ∘ fun z : ℂ => 1 - z) s
      = analyticOrderAt completedRiemannZeta (1 - s) := by
    refine analyticOrderAt_comp_of_deriv_ne_zero (g := fun z : ℂ => 1 - z) ?_ ?_
    · exact DifferentiableOn.analyticAt (s := Set.univ)
        ((differentiable_const 1).sub differentiable_id).differentiableOn Filter.univ_mem
    · rw [deriv_const_sub, deriv_id'']
      norm_num
  have hfun : (completedRiemannZeta ∘ fun z : ℂ => 1 - z) = completedRiemannZeta := by
    funext z; simpa using completedRiemannZeta_one_sub z
  unfold zeroMultiplicity
  rw [← analyticOrderAt_completedRiemannZeta_eq h0' h1',
    ← analyticOrderAt_completedRiemannZeta_eq h0 h1, ← hcomp, hfun]

/-- **The multiplicity of a zero is unchanged by reflection in the critical line.** -/
theorem zeroMultiplicity_criticalReflect {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zeroMultiplicity (criticalReflect s) = zeroMultiplicity s := by
  have hre : ((starRingEnd ℂ) s).re = s.re := Complex.conj_re s
  rw [criticalReflect, zeroMultiplicity_one_sub (by rw [hre]; exact h0) (by rw [hre]; exact h1),
    zeroMultiplicity_conj h0 h1]

/-! ## Counting the zeroes with multiplicity -/

/-- The number of nontrivial zeroes of height at most `T`, counted **with multiplicity**. -/
def multCount (T : ℝ) : ℕ := ∑ᶠ ρ ∈ nontrivialZeros T, zeroMultiplicity ρ

/-- The number of off-line nontrivial zeroes of height at most `T`, counted **with
multiplicity**. -/
def offLineMultCount (T : ℝ) : ℕ := ∑ᶠ ρ ∈ offLineNontrivialZeros T, zeroMultiplicity ρ

/-- Counted with multiplicity, the zeroes of height at most `T` are twice those in the upper
half-plane. -/
theorem multCount_eq_two_mul (T : ℝ) :
    multCount T = 2 * ∑ᶠ ρ ∈ upperNontrivialZeros T, zeroMultiplicity ρ := by
  have hupfin : (upperNontrivialZeros T).Finite :=
    (finite_nontrivialZeros T).subset fun s hs => hs.1
  have hlowfin : (lowerNontrivialZeros T).Finite :=
    (finite_nontrivialZeros T).subset fun s hs => hs.1
  have hdisj : Disjoint (upperNontrivialZeros T) (lowerNontrivialZeros T) := by
    rw [Set.disjoint_left]
    rintro s ⟨-, hpos⟩ ⟨-, hneg⟩
    linarith
  have hlow : ∑ᶠ ρ ∈ lowerNontrivialZeros T, zeroMultiplicity ρ
      = ∑ᶠ ρ ∈ upperNontrivialZeros T, zeroMultiplicity ρ := by
    rw [← conj_image_upperNontrivialZeros T,
      finsum_mem_image (Set.injOn_of_injective conj_injective_complex)]
    refine finsum_mem_congr rfl fun ρ hρ => ?_
    obtain ⟨⟨-, h0, h1, -⟩, -⟩ := hρ
    exact zeroMultiplicity_conj h0 h1
  rw [multCount, ← union_upper_lower_nontrivialZeros T,
    finsum_mem_union hdisj hupfin hlowfin, hlow]
  ring

/-- **Counted with multiplicity, the number of nontrivial zeroes of height at most `T` is
even.** -/
theorem even_multCount (T : ℝ) : Even (multCount T) := by
  rw [multCount_eq_two_mul T]
  exact even_two_mul _

/-- Counted with multiplicity, the off-line zeroes of height at most `T` are four times those in
the upper half-plane to the left of the critical line. -/
theorem offLineMultCount_eq_four_mul (T : ℝ) :
    offLineMultCount T = 4 * ∑ᶠ ρ ∈ leftUpperNontrivialZeros T, zeroMultiplicity ρ := by
  have hupdisj : Disjoint (upperOffLineNontrivialZeros T) (lowerOffLineNontrivialZeros T) := by
    rw [Set.disjoint_left]
    rintro s ⟨-, -, hpos⟩ ⟨-, -, hneg⟩
    linarith
  have hlrdisj : Disjoint (leftUpperNontrivialZeros T) (rightUpperNontrivialZeros T) := by
    rw [Set.disjoint_left]
    rintro s ⟨-, hleft, -⟩ ⟨-, hright, -⟩
    linarith
  have hlow : ∑ᶠ ρ ∈ lowerOffLineNontrivialZeros T, zeroMultiplicity ρ
      = ∑ᶠ ρ ∈ upperOffLineNontrivialZeros T, zeroMultiplicity ρ := by
    rw [← conj_image_upperOffLineNontrivialZeros T,
      finsum_mem_image (Set.injOn_of_injective conj_injective_complex)]
    refine finsum_mem_congr rfl fun ρ hρ => ?_
    obtain ⟨⟨-, h0, h1, -⟩, -⟩ := hρ
    exact zeroMultiplicity_conj h0 h1
  have hright : ∑ᶠ ρ ∈ rightUpperNontrivialZeros T, zeroMultiplicity ρ
      = ∑ᶠ ρ ∈ leftUpperNontrivialZeros T, zeroMultiplicity ρ := by
    rw [← criticalReflect_image_leftUpperNontrivialZeros T,
      finsum_mem_image (Set.injOn_of_injective criticalReflect_injective)]
    refine finsum_mem_congr rfl fun ρ hρ => ?_
    obtain ⟨⟨-, h0, h1, -⟩, -⟩ := hρ
    exact zeroMultiplicity_criticalReflect h0 h1
  have hupper : ∑ᶠ ρ ∈ upperOffLineNontrivialZeros T, zeroMultiplicity ρ
      = 2 * ∑ᶠ ρ ∈ leftUpperNontrivialZeros T, zeroMultiplicity ρ := by
    rw [← union_left_right_upperOffLineNontrivialZeros T,
      finsum_mem_union hlrdisj (leftUpperNontrivialZeros_finite T)
        (rightUpperNontrivialZeros_finite T), hright]
    ring
  rw [offLineMultCount, ← union_upper_lower_offLineNontrivialZeros T,
    finsum_mem_union hupdisj (upperOffLineNontrivialZeros_finite T)
      (lowerOffLineNontrivialZeros_finite T), hlow, hupper]
  ring

/-- **Counted with multiplicity, the number of off-line nontrivial zeroes of height at most `T`
is divisible by four.** -/
theorem four_dvd_offLineMultCount (T : ℝ) : 4 ∣ offLineMultCount T :=
  ⟨_, offLineMultCount_eq_four_mul T⟩

end RiemannHypothesis
