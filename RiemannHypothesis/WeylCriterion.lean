/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylEquidistribution
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weyl's criterion, and equidistribution of `α n²` modulo one

`RiemannHypothesis.WeylEquidistribution` proves that the quadratic Weyl sums `∑_{n<N} e(hα n²)`
are `o(N)` for every nonzero integer `h`, when `α` is irrational.  Those are precisely the
estimates Weyl's criterion converts into a statement about the *distribution* of the fractional
parts.  This module proves the criterion and draws the conclusion.

Distribution is expressed on the circle `𝕋 = ℝ / ℤ` with its Haar probability measure: a sequence
`x : ℕ → ℝ` is equidistributed modulo one when the averages of every continuous function along
`x` converge to its mean,

    (1/N) ∑_{n<N} f(x n) → ∫ f    for every `f ∈ C(𝕋, ℂ)`.

## Main results

* `EquidistributedMod1`, `WeylSumsVanish` — the two sides of the criterion.
* `equidistributedMod1_iff_weylSumsVanish` — **Weyl's criterion**: a sequence is equidistributed
  modulo one if and only if `‖∑_{n<N} e(m x n)‖ / N → 0` for every nonzero integer `m`.
* `equidistributedMod1_quadratic` — **the fractional parts of `α n²` are equidistributed** for
  every irrational `α`.

## Proof

The set of `f ∈ C(𝕋, ℂ)` whose averages along `x` converge to `∫ f` is a `ℂ`-submodule
(`weylTest`), because both sides are linear in `f`, and it is closed (`isClosed_weylTest`),
because an average and an integral are both `1`-Lipschitz in the uniform norm — a three-epsilon
argument.  It contains every character `fourier m`: for `m = 0` the average is constantly `1`,
which is the integral, and for `m ≠ 0` the average is exactly `(1/N) ∑_{n<N} e(m x n)`, which the
hypothesis sends to `0`, while `∫ fourier m = 0` by direct computation
(`integral_fourier_eq_zero`).  Since the span of the characters is dense in `C(𝕋, ℂ)`
(Stone–Weierstrass, `span_fourier_closure_eq_top`), the submodule is everything.

## Scope

Equidistribution is formulated against continuous test functions, which is the Riesz/portmanteau
form of the statement.  The count of `n < N` with fractional part in a subinterval is not derived
here: it is deduced from equidistribution in `RiemannHypothesis.WeylCount` and
`RiemannHypothesis.WeylCountGeneral`, and `RiemannHypothesis.WeylPortmanteau` proves the converse,
so that the counting statement is itself equivalent to the two notions of this module.  Nothing in
this module concerns `ζ`.
-/

noncomputable section

open Complex Filter Finset Topology MeasureTheory AddCircle

namespace RiemannHypothesis

namespace WeylCriterion

open KusminLandau WeylQuadratic WeylEquidistribution

/-- The period `1` is positive: the instance `haarAddCircle` and `fourier` need. -/
instance instFactZeroLtOneReal : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The circle `ℝ / ℤ`, carrying the Haar probability measure `haarAddCircle`. -/
abbrev Circ := AddCircle (1 : ℝ)

/-- The average of `f` along the first `N` terms of the sequence `x`, read modulo one. -/
def avg (x : ℕ → ℝ) (f : Circ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f ((x n : ℝ) : Circ)

/-- `x : ℕ → ℝ` is equidistributed modulo one: the averages of every continuous function on the
circle along `x` converge to its mean. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ f : C(Circ, ℂ), Tendsto (fun N => avg x f N) atTop (𝓝 (∫ t, f t ∂haarAddCircle))

/-- The exponential sums of `x` at every nonzero frequency exhibit cancellation. -/
def WeylSumsVanish (x : ℕ → ℝ) : Prop :=
  ∀ m : ℤ, m ≠ 0 →
    Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n)‖ / N) atTop (𝓝 0)

/-- The character `fourier m` evaluated at a real number is the exponential `e(m θ)`. -/
theorem fourier_coe_eq_e2pi (m : ℤ) (y : ℝ) : fourier m ((y : ℝ) : Circ) = e2pi ((m : ℝ) * y) := by
  rw [fourier_coe_apply, e2pi]
  congr 1
  push_cast
  ring

/-- A continuous function on the circle is integrable for the Haar probability measure. -/
theorem integrable_contMap (f : C(Circ, ℂ)) : Integrable f haarAddCircle := by
  refine ⟨(map_continuous f).aestronglyMeasurable, ?_⟩
  exact HasFiniteIntegral.of_bounded (C := ‖f‖) (ae_of_all _ fun t => f.norm_coe_le_norm t)

/-- The mean of a nonconstant character vanishes. -/
theorem integral_fourier_eq_zero {m : ℤ} (hm : m ≠ 0) :
    ∫ t : Circ, fourier m t ∂haarAddCircle = 0 := by
  have hpre := AddCircle.intervalIntegral_preimage (1 : ℝ) 0 (fun t : Circ => fourier m t)
  have hvol : (volume : Measure Circ) = haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hvol] at hpre
  rw [← hpre]
  have hc : (2 * Real.pi * Complex.I * m : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, hm, Complex.I_ne_zero]
  have hrewrite : ∀ x : ℝ, fourier m ((x : ℝ) : Circ)
      = Complex.exp ((2 * Real.pi * Complex.I * m : ℂ) * x) := by
    intro x
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  simp only [hrewrite]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((2 * Real.pi * Complex.I * m : ℂ) * ((0 : ℝ) + 1 : ℝ)) = 1 := by
    have : ((2 : ℂ) * Real.pi * Complex.I * m) * ((0 : ℝ) + 1 : ℝ)
        = (m : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have h0 : Complex.exp ((2 * Real.pi * Complex.I * m : ℂ) * ((0 : ℝ) : ℝ)) = 1 := by
    norm_num
  rw [h1, h0]
  simp

/-- Averaging along `x` is `1`-Lipschitz in the uniform norm. -/
theorem dist_avg_le (x : ℕ → ℝ) (f g : C(Circ, ℂ)) (N : ℕ) :
    dist (avg x f N) (avg x g N) ≤ dist f g := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [avg]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ‖∑ n ∈ Finset.range N, (f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ))‖
      ≤ (N : ℝ) * dist f g := by
    have : ∀ n ∈ Finset.range N, ‖f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ)‖ ≤ dist f g := by
      intro n _
      simpa [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := f) (g := g)
        ((x n : ℝ) : Circ)
    calc ‖∑ n ∈ Finset.range N, (f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ))‖
        ≤ ∑ _n ∈ Finset.range N, dist f g := norm_sum_le_of_le _ this
      _ = (N : ℝ) * dist f g := by simp
  have hdiff : avg x f N - avg x g N
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, (f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ)) := by
    simp [avg, Finset.sum_sub_distrib, mul_sub]
  rw [dist_eq_norm, hdiff, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, (f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ))‖
      ≤ (N : ℝ)⁻¹ * ((N : ℝ) * dist f g) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = dist f g := by field_simp

/-- Integration against the Haar probability measure is `1`-Lipschitz in the uniform norm. -/
theorem dist_integral_le (f g : C(Circ, ℂ)) :
    dist (∫ t, f t ∂haarAddCircle) (∫ t, g t ∂haarAddCircle) ≤ dist f g := by
  rw [dist_eq_norm, ← integral_sub (integrable_contMap f) (integrable_contMap g)]
  have hbdd : ∀ t : Circ, ‖f t - g t‖ ≤ dist f g := by
    intro t
    simpa [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) t
  calc ‖∫ t, (f t - g t) ∂haarAddCircle‖
      ≤ dist f g * (haarAddCircle (Set.univ : Set Circ)).toReal :=
        norm_integral_le_of_norm_le_const (ae_of_all _ hbdd)
    _ = dist f g := by simp

/-- The continuous functions whose averages along `x` converge to their mean: a `ℂ`-submodule of
`C(𝕋, ℂ)`. -/
def weylTest (x : ℕ → ℝ) : Submodule ℂ C(Circ, ℂ) where
  carrier := {f | Tendsto (fun N => avg x f N) atTop (𝓝 (∫ t, f t ∂haarAddCircle))}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq] at hf hg ⊢
    have hint : (∫ t, (f + g) t ∂haarAddCircle)
        = (∫ t, f t ∂haarAddCircle) + ∫ t, g t ∂haarAddCircle := by
      simpa using integral_add (integrable_contMap f) (integrable_contMap g)
    have havg : ∀ N, avg x (⇑(f + g)) N = avg x f N + avg x g N := by
      intro N
      simp [avg, Finset.sum_add_distrib, mul_add]
    rw [hint]
    exact (hf.add hg).congr fun N => (havg N).symm
  zero_mem' := by
    have havg : ∀ N, avg x (⇑(0 : C(Circ, ℂ))) N = 0 := by intro N; simp [avg]
    have hint : (∫ t, (0 : C(Circ, ℂ)) t ∂haarAddCircle) = 0 := by simp
    change Tendsto (fun N => avg x (⇑(0 : C(Circ, ℂ))) N) atTop
      (𝓝 (∫ t, (0 : C(Circ, ℂ)) t ∂haarAddCircle))
    rw [hint]
    exact Tendsto.congr (fun N => (havg N).symm) tendsto_const_nhds
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_ofPred_eq] at hf ⊢
    have hint : (∫ t, (c • f) t ∂haarAddCircle) = c • ∫ t, f t ∂haarAddCircle := by
      simpa using integral_smul c (fun t : Circ => f t)
    have havg : ∀ N, avg x (⇑(c • f)) N = c * avg x f N := by
      intro N
      simp only [avg, ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      ring_nf
    rw [hint]
    have := hf.const_mul c
    exact this.congr fun N => (havg N).symm

theorem mem_weylTest_iff {x : ℕ → ℝ} {f : C(Circ, ℂ)} :
    f ∈ weylTest x ↔ Tendsto (fun N => avg x f N) atTop (𝓝 (∫ t, f t ∂haarAddCircle)) :=
  Iff.rfl

/-- The submodule of good test functions is closed: averages and integrals are both `1`-Lipschitz
in the uniform norm. -/
theorem isClosed_weylTest (x : ℕ → ℝ) : IsClosed (weylTest x : Set C(Circ, ℂ)) := by
  refine IsSeqClosed.isClosed ?_
  intro F f hF hconv
  rw [SetLike.mem_coe, mem_weylTest_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 hconv) (ε / 4) (by positivity)
  have hdk : dist (F k) f < ε / 4 := hk k le_rfl
  have hmem : Tendsto (fun N => avg x (F k) N) atTop (𝓝 (∫ t, F k t ∂haarAddCircle)) :=
    mem_weylTest_iff.1 (hF k)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hmem) (ε / 4) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : dist (avg x f N) (avg x (F k) N) ≤ dist f (F k) := dist_avg_le x f (F k) N
  have h2 : dist (avg x (F k) N) (∫ t, F k t ∂haarAddCircle) < ε / 4 := hN₀ N hN
  have h3 : dist (∫ t, F k t ∂haarAddCircle) (∫ t, f t ∂haarAddCircle) ≤ dist (F k) f :=
    dist_integral_le (F k) f
  have hsym : dist f (F k) = dist (F k) f := dist_comm _ _
  calc dist (avg x f N) (∫ t, f t ∂haarAddCircle)
      ≤ dist (avg x f N) (avg x (F k) N) + dist (avg x (F k) N) (∫ t, f t ∂haarAddCircle) :=
        dist_triangle _ _ _
    _ ≤ dist (avg x f N) (avg x (F k) N) + (dist (avg x (F k) N) (∫ t, F k t ∂haarAddCircle)
          + dist (∫ t, F k t ∂haarAddCircle) (∫ t, f t ∂haarAddCircle)) := by
        gcongr
        exact dist_triangle _ _ _
    _ < ε := by rw [hsym] at h1; linarith

/-- Every character lies in the submodule of good test functions, when the Weyl sums vanish. -/
theorem fourier_mem_weylTest {x : ℕ → ℝ} (h : WeylSumsVanish x) (m : ℤ) :
    (fourier m : C(Circ, ℂ)) ∈ weylTest x := by
  rw [mem_weylTest_iff]
  rcases eq_or_ne m 0 with rfl | hm
  · have hint : (∫ t : Circ, fourier 0 t ∂haarAddCircle) = 1 := by
      simp
    have havg : ∀ N : ℕ, 1 ≤ N → avg x (fourier (T := (1 : ℝ)) 0) N = 1 := by
      intro N hN
      have hN0 : (N : ℂ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      simp [avg, hN0]
    rw [hint]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)) (f := (atTop : Filter ℕ)))
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (havg N hN).symm
  · rw [integral_fourier_eq_zero hm]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : ∀ N : ℕ, ‖avg x (fourier (T := (1 : ℝ)) m) N‖
        = ‖∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n)‖ / N := by
      intro N
      rw [avg, norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
      congr 1
      congr 1
      exact Finset.sum_congr rfl fun n _ => fourier_coe_eq_e2pi m (x n)
    exact (h m hm).congr fun N => (heq N).symm

/-- **Weyl's criterion**, the direction that matters: if every nonzero frequency exhibits
cancellation then the sequence is equidistributed modulo one. -/
theorem equidistributedMod1_of_weylSumsVanish {x : ℕ → ℝ} (h : WeylSumsVanish x) :
    EquidistributedMod1 x := by
  intro f
  have hle : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤ weylTest x := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact fourier_mem_weylTest h m
  have hclosed := Submodule.topologicalClosure_minimal _ hle (isClosed_weylTest x)
  rw [span_fourier_closure_eq_top] at hclosed
  exact mem_weylTest_iff.1 (hclosed (Submodule.mem_top))

/-- The converse direction of Weyl's criterion: equidistribution forces cancellation at every
nonzero frequency. -/
theorem weylSumsVanish_of_equidistributedMod1 {x : ℕ → ℝ} (h : EquidistributedMod1 x) :
    WeylSumsVanish x := by
  intro m hm
  have hf := h (fourier m)
  rw [integral_fourier_eq_zero hm, tendsto_zero_iff_norm_tendsto_zero] at hf
  have heq : ∀ N : ℕ, ‖avg x (fourier (T := (1 : ℝ)) m) N‖
      = ‖∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n)‖ / N := by
    intro N
    rw [avg, norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun n _ => fourier_coe_eq_e2pi m (x n)
  exact hf.congr heq

/-- **Weyl's criterion.** -/
theorem equidistributedMod1_iff_weylSumsVanish (x : ℕ → ℝ) :
    EquidistributedMod1 x ↔ WeylSumsVanish x :=
  ⟨weylSumsVanish_of_equidistributedMod1, equidistributedMod1_of_weylSumsVanish⟩

/-- The notion is not vacuous: a constant sequence is *not* equidistributed. -/
theorem not_equidistributedMod1_const_zero : ¬ EquidistributedMod1 (fun _ : ℕ => (0 : ℝ)) := by
  intro h
  have h1 := weylSumsVanish_of_equidistributedMod1 h 1 one_ne_zero
  have heq : ∀ N : ℕ, 1 ≤ N →
      ‖∑ _n ∈ Finset.range N, e2pi (((1 : ℤ) : ℝ) * (0 : ℝ))‖ / N = 1 := by
    intro N hN
    have hN0 : (N : ℝ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    simp [e2pi, hN0]
  have hone : Tendsto
      (fun N : ℕ => ‖∑ _n ∈ Finset.range N, e2pi (((1 : ℤ) : ℝ) * (0 : ℝ))‖ / N) atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ)))
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (heq N hN).symm
  have := tendsto_nhds_unique h1 hone
  norm_num at this

/-- The quadratic Weyl sums of an irrational `α`, at every nonzero frequency, vanish in the
Cesàro sense. -/
theorem weylSumsVanish_quadratic {α : ℝ} (hα : Irrational α) :
    WeylSumsVanish (fun n : ℕ => α * (n : ℝ) ^ 2) := by
  intro m hm
  have hirr : Irrational ((m : ℝ) * α) := hα.intCast_mul hm
  have hmain := tendsto_norm_quadSum_div_atTop hirr
  refine hmain.congr fun N => ?_
  have hsum : quadSum ((m : ℝ) * α) N
      = ∑ n ∈ Finset.range N, e2pi ((m : ℝ) * (α * (n : ℝ) ^ 2)) := by
    rw [quadSum, sum_Ico_int_eq_sum_range]
    simp only [Int.toNat_natCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast
    ring
  rw [hsum]

/-- **The fractional parts of `α n²` are equidistributed** for every irrational `α`: the averages
of every continuous function on the circle along `α n²` converge to its mean. -/
theorem equidistributedMod1_quadratic {α : ℝ} (hα : Irrational α) :
    EquidistributedMod1 (fun n : ℕ => α * (n : ℝ) ^ 2) :=
  equidistributedMod1_of_weylSumsVanish (weylSumsVanish_quadratic hα)

end WeylCriterion

end RiemannHypothesis
