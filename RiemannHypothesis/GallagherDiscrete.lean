/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.DirichletPolyMeanValue

/-!
# Gallagher's lemma and the discrete mean value theorem for Dirichlet polynomials

`RiemannHypothesis/DirichletPolyMeanValue.lean` proves the *continuous* mean value theorem

`∫₀ᵀ ‖D(σ + i t)‖² dt = (T + O(N log N)) ∑_{n ≤ N} ‖a n‖² n^(-2σ)`

for `D(s) = ∑_{1 ≤ n ≤ N} a n n^{-s}`.  The large-values machinery of
`RiemannHypothesis/HalaszMontgomery.lean` needs instead a bound for a *discrete* sum
`∑_r ‖D(σ + i t_r)‖²` over `δ`-separated points `t_r`.  The bridge is Gallagher's Sobolev-type
lemma: if `f` is continuously differentiable and the points `t_r` are `δ`-separated inside
`[A, B]`, then

`δ ∑_r ‖f(t_r)‖² ≤ 2 ∫_A^B ‖f‖² + δ² ∫_A^B ‖f'‖²`.

(The classical form has `1` in place of `2` and a Cauchy–Schwarz cross term; the version proved
here trades the cross term for the constant `2` via `2 x y ≤ δ⁻¹ x² + δ y²`, which is all that is
needed downstream and avoids an appeal to Cauchy–Schwarz for integrals.)

Applied to a Dirichlet polynomial, whose derivative along the vertical line is again a Dirichlet
polynomial — with coefficients `a n log n` — this gives the discrete mean value theorem

`∑_r ‖D(σ + i t_r)‖² ≤ (2/δ + δ (log N)²) (T + 8 N (1 + log N)) ∑_{n ≤ N} ‖a n‖² n^(-2σ)`

for `δ`-separated points in `[δ/2, T - δ/2]`.

## Main results

* `hasDerivAt_normSq_comp` — the derivative of `t ↦ ‖f t‖²`.
* `mul_normSq_le_integral_of_mem_Icc` — the one-interval Sobolev inequality.
* `sum_normSq_le_of_separated` — **Gallagher's lemma**.
* `hasDerivAt_dirichletPoly_line` — the derivative of a Dirichlet polynomial along a vertical
  line: `-i` times the Dirichlet polynomial with coefficients `a n log n`.
* `sum_normSq_dirichletPoly_at_separated_le` — **the discrete mean value theorem**.
* `card_le_of_dirichletPoly_large_separated` — the large values count that follows from it.

## Scope

The bound is the elementary one: its error term inherits the factor `N log N` of the continuous
mean value theorem proved in this repository, rather than the `N` of the Montgomery–Vaughan
theorem.  No zero-density estimate is claimed here.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Finset

namespace RiemannHypothesis

namespace Gallagher

/-! ## The derivative of `‖f‖²` -/

/-- The derivative of `t ↦ ‖f t‖²` is `2 Re(conj (f t) · f' t)`. -/
theorem hasDerivAt_normSq_comp {f f' : ℝ → ℂ} {t : ℝ} (hf : HasDerivAt f (f' t) t) :
    HasDerivAt (fun x => ‖f x‖ ^ 2) (2 * ((starRingEnd ℂ) (f t) * f' t).re) t := by
  have hre : HasDerivAt (fun x => (f x).re) (f' t).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have him : HasDerivAt (fun x => (f x).im) (f' t).im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  have h : HasDerivAt (fun x => (f x).re * (f x).re + (f x).im * (f x).im)
      ((f' t).re * (f t).re + (f t).re * (f' t).re +
        ((f' t).im * (f t).im + (f t).im * (f' t).im)) t := (hre.mul hre).add (him.mul him)
  have heq : (fun x => ‖f x‖ ^ 2) = fun x => (f x).re * (f x).re + (f x).im * (f x).im := by
    funext x
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
  rw [heq]
  convert h using 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The derivative of `‖f‖²` is bounded by `2 ‖f‖ ‖f'‖`. -/
theorem abs_two_mul_re_conj_mul_le (z w : ℂ) :
    |2 * ((starRingEnd ℂ) z * w).re| ≤ 2 * ‖z‖ * ‖w‖ := by
  have h1 : |((starRingEnd ℂ) z * w).re| ≤ ‖(starRingEnd ℂ) z * w‖ := Complex.abs_re_le_norm _
  have h2 : ‖(starRingEnd ℂ) z * w‖ = ‖z‖ * ‖w‖ := by rw [norm_mul, RCLike.norm_conj]
  rw [abs_mul, abs_two]
  nlinarith [h1, h2]

/-! ## The one-interval Sobolev inequality -/

/-- The integral of a real function over a subinterval, in absolute value, is bounded by the
integral of its absolute value over the whole interval. -/
theorem abs_integral_le_integral_abs_sub {h : ℝ → ℝ} (hh : Continuous h) {u v p q : ℝ}
    (hp : p ∈ Set.Icc u v) (hq : q ∈ Set.Icc u v) :
    |∫ x in p..q, h x| ≤ ∫ x in u..v, |h x| := by
  obtain ⟨hpu, hpv⟩ := hp
  obtain ⟨hqu, hqv⟩ := hq
  have hint : IntervalIntegrable (fun x => |h x|) volume u v := hh.abs.intervalIntegrable u v
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc u v)] fun x => |h x| :=
    Filter.Eventually.of_forall fun x => abs_nonneg (h x)
  rcases le_total p q with hpq | hpq
  · calc |∫ x in p..q, h x| ≤ ∫ x in p..q, |h x| :=
          intervalIntegral.abs_integral_le_integral_abs hpq
      _ ≤ ∫ x in u..v, |h x| := integral_mono_interval hpu hpq hqv hnn hint
  · rw [intervalIntegral.integral_symm, abs_neg]
    calc |∫ x in q..p, h x| ≤ ∫ x in q..p, |h x| :=
          intervalIntegral.abs_integral_le_integral_abs hpq
      _ ≤ ∫ x in u..v, |h x| := integral_mono_interval hqu hpq hpv hnn hint

/-- **The one-interval Sobolev inequality.**  If `c` lies in `[u, v]` then
`(v - u) ‖f c‖² ≤ ∫_u^v ‖f‖² + (v - u) ∫_u^v 2 ‖f‖ ‖f'‖`. -/
theorem mul_normSq_le_integral_of_mem_Icc {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {u v c : ℝ} (huv : u ≤ v) (hc : c ∈ Set.Icc u v) :
    (v - u) * ‖f c‖ ^ 2
      ≤ (∫ x in u..v, ‖f x‖ ^ 2) + (v - u) * ∫ x in u..v, 2 * ‖f x‖ * ‖f' x‖ := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  set g' : ℝ → ℝ := fun x => 2 * ((starRingEnd ℂ) (f x) * f' x).re with hg'def
  have hg'c : Continuous g' := by
    simp only [hg'def]
    exact continuous_const.mul
      (Complex.continuous_re.comp ((Complex.continuous_conj.comp hfc).mul hf'))
  have hg : ∀ x, HasDerivAt (fun y => ‖f y‖ ^ 2) (g' x) x := fun x => hasDerivAt_normSq_comp (hf x)
  have hnormsq : Continuous fun x : ℝ => ‖f x‖ ^ 2 := by fun_prop
  have hcross : Continuous fun x : ℝ => 2 * ‖f x‖ * ‖f' x‖ := by fun_prop
  set J := ∫ x in u..v, |g' x| with hJ
  have hJle : J ≤ ∫ x in u..v, 2 * ‖f x‖ * ‖f' x‖ :=
    intervalIntegral.integral_mono_on huv (hg'c.abs.intervalIntegrable u v)
      (hcross.intervalIntegrable u v) fun x _ => abs_two_mul_re_conj_mul_le (f x) (f' x)
  have hkey : ∀ x ∈ Set.Icc u v, ‖f c‖ ^ 2 ≤ ‖f x‖ ^ 2 + J := by
    intro x hx
    have hfund : (∫ y in x..c, g' y) = ‖f c‖ ^ 2 - ‖f x‖ ^ 2 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hg y)
        (hg'c.intervalIntegrable x c)
    have habs : |∫ y in x..c, g' y| ≤ J := abs_integral_le_integral_abs_sub hg'c hx hc
    rw [hfund] at habs
    have h2 := (abs_le.mp habs).2
    linarith
  have hconst : (v - u) * ‖f c‖ ^ 2 = ∫ _x in u..v, ‖f c‖ ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hmono : (∫ _x in u..v, ‖f c‖ ^ 2) ≤ ∫ x in u..v, (‖f x‖ ^ 2 + J) :=
    intervalIntegral.integral_mono_on huv intervalIntegrable_const
      ((hnormsq.add continuous_const).intervalIntegrable u v) hkey
  have hsplit : (∫ x in u..v, (‖f x‖ ^ 2 + J)) = (∫ x in u..v, ‖f x‖ ^ 2) + (v - u) * J := by
    rw [intervalIntegral.integral_add (hnormsq.intervalIntegrable u v)
        intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [hconst]
  refine hmono.trans ?_
  rw [hsplit]
  have hvu : 0 ≤ v - u := by linarith
  nlinarith [hJle]

/-- The one-interval Sobolev inequality, with the cross term split by `2 x y ≤ δ⁻¹ x² + δ y²`. -/
theorem mul_normSq_le_integral_of_mem_Icc' {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {u v c : ℝ} (huv : u < v) (hc : c ∈ Set.Icc u v) :
    (v - u) * ‖f c‖ ^ 2
      ≤ 2 * (∫ x in u..v, ‖f x‖ ^ 2) + (v - u) ^ 2 * ∫ x in u..v, ‖f' x‖ ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hstep := mul_normSq_le_integral_of_mem_Icc hf hf' huv.le hc
  have hd : 0 < v - u := by linarith
  have hnormsq : Continuous fun x : ℝ => ‖f x‖ ^ 2 := by fun_prop
  have hnormsq' : Continuous fun x : ℝ => ‖f' x‖ ^ 2 := by fun_prop
  have hcross : Continuous fun x : ℝ => 2 * ‖f x‖ * ‖f' x‖ := by fun_prop
  have hi1 : IntervalIntegrable (fun x : ℝ => (v - u)⁻¹ * ‖f x‖ ^ 2) volume u v :=
    (continuous_const.mul hnormsq).intervalIntegrable u v
  have hi2 : IntervalIntegrable (fun x : ℝ => (v - u) * ‖f' x‖ ^ 2) volume u v :=
    (continuous_const.mul hnormsq').intervalIntegrable u v
  have hpt : ∀ x ∈ Set.Icc u v, 2 * ‖f x‖ * ‖f' x‖
      ≤ (v - u)⁻¹ * ‖f x‖ ^ 2 + (v - u) * ‖f' x‖ ^ 2 := by
    intro x _
    rw [← sub_nonneg]
    have heq : (v - u)⁻¹ * ‖f x‖ ^ 2 + (v - u) * ‖f' x‖ ^ 2 - 2 * ‖f x‖ * ‖f' x‖
        = (v - u)⁻¹ * (‖f x‖ - (v - u) * ‖f' x‖) ^ 2 := by
      field_simp; ring
    rw [heq]
    positivity
  have hint : (∫ x in u..v, 2 * ‖f x‖ * ‖f' x‖)
      ≤ (v - u)⁻¹ * (∫ x in u..v, ‖f x‖ ^ 2) + (v - u) * ∫ x in u..v, ‖f' x‖ ^ 2 := by
    have h := intervalIntegral.integral_mono_on huv.le (hcross.intervalIntegrable u v)
      (hi1.add hi2) hpt
    rwa [intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  have hmul := mul_le_mul_of_nonneg_left hint hd.le
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hd), one_mul] at hmul
  nlinarith [hmul]

/-! ## Gallagher's lemma -/

/-- The integrals over the `δ`-windows around `δ`-separated points add up to at most the integral
over the enclosing interval. -/
theorem sum_integral_window_le {h : ℝ → ℝ} (hh : Continuous h) (hpos : ∀ x, 0 ≤ h x)
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ A B : ℝ} (hδ : 0 < δ) (hAB : A ≤ B)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (A + δ / 2) (B - δ / 2)) :
    ∑ i ∈ s, (∫ x in (t i - δ / 2)..(t i + δ / 2), h x) ≤ ∫ x in A..B, h x := by
  classical
  set S : ι → Set ℝ := fun i => Set.Ioc (t i - δ / 2) (t i + δ / 2) with hS
  have hsub : ∀ i ∈ s, S i ⊆ Set.Ioc A B := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmem i hi
    exact Set.Ioc_subset_Ioc (by linarith) (by linarith)
  have hdisj : Set.Pairwise (↑s) (Function.onFun Disjoint S) := by
    intro i hi j hj hij
    change Disjoint (S i) (S j)
    rw [Set.disjoint_left]
    intro x hx hx'
    have hsp := hsep i hi j hj hij
    simp only [hS, Set.mem_Ioc] at hx hx'
    rcases abs_cases (t i - t j) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hsp <;>
      linarith [hx.1, hx.2, hx'.1, hx'.2]
  have hmeas : ∀ i ∈ s, MeasurableSet (S i) := fun i _ => measurableSet_Ioc
  have hint : ∀ i ∈ s, IntegrableOn h (S i) volume := fun i _ => hh.integrableOn_Ioc
  have hbi : ∫ x in ⋃ i ∈ s, S i, h x = ∑ i ∈ s, ∫ x in S i, h x :=
    integral_biUnion_finset s hmeas hdisj hint
  have hle : (∫ x in ⋃ i ∈ s, S i, h x) ≤ ∫ x in Set.Ioc A B, h x :=
    setIntegral_mono_set hh.integrableOn_Ioc (Filter.Eventually.of_forall fun x => hpos x)
      (Set.iUnion₂_subset hsub).eventuallyLE
  have hsum : ∑ i ∈ s, (∫ x in (t i - δ / 2)..(t i + δ / 2), h x) = ∑ i ∈ s, ∫ x in S i, h x :=
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_of_le (by linarith)
  rw [intervalIntegral.integral_of_le hAB, hsum, ← hbi]
  exact hle

/-- **Gallagher's lemma.**  For `δ`-separated points `t i` lying in `[A + δ/2, B - δ/2]`,
`δ ∑ ‖f (t i)‖² ≤ 2 ∫_A^B ‖f‖² + δ² ∫_A^B ‖f'‖²`. -/
theorem sum_normSq_le_of_separated {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ A B : ℝ} (hδ : 0 < δ)
    (hAB : A ≤ B) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (A + δ / 2) (B - δ / 2)) :
    δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2
      ≤ 2 * (∫ x in A..B, ‖f x‖ ^ 2) + δ ^ 2 * ∫ x in A..B, ‖f' x‖ ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hnormsq : Continuous fun x : ℝ => ‖f x‖ ^ 2 := by fun_prop
  have hnormsq' : Continuous fun x : ℝ => ‖f' x‖ ^ 2 := by fun_prop
  have hpt : ∀ i ∈ s, δ * ‖f (t i)‖ ^ 2
      ≤ 2 * (∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f x‖ ^ 2)
        + δ ^ 2 * ∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f' x‖ ^ 2 := by
    intro i _
    have hlt : t i - δ / 2 < t i + δ / 2 := by linarith
    have hc : t i ∈ Set.Icc (t i - δ / 2) (t i + δ / 2) := ⟨by linarith, by linarith⟩
    have h := mul_normSq_le_integral_of_mem_Icc' hf hf' hlt hc
    have hδeq : t i + δ / 2 - (t i - δ / 2) = δ := by ring
    rwa [hδeq] at h
  calc δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2 = ∑ i ∈ s, δ * ‖f (t i)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, (2 * (∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f x‖ ^ 2)
          + δ ^ 2 * ∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f' x‖ ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 2 * (∑ i ∈ s, ∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f x‖ ^ 2)
          + δ ^ 2 * ∑ i ∈ s, ∫ x in (t i - δ / 2)..(t i + δ / 2), ‖f' x‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (∫ x in A..B, ‖f x‖ ^ 2) + δ ^ 2 * ∫ x in A..B, ‖f' x‖ ^ 2 := by
        have h1 := sum_integral_window_le hnormsq (fun x => by positivity) hδ hAB hsep hmem
        have h2 := sum_integral_window_le hnormsq' (fun x => by positivity) hδ hAB hsep hmem
        have hδ2 : (0 : ℝ) ≤ δ ^ 2 := by positivity
        nlinarith [h1, h2]

end Gallagher

/-! ## The derivative of a Dirichlet polynomial along a vertical line -/

/-- The coefficients of the derivative of a Dirichlet polynomial: `a n · log n`. -/
def logCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ := (Real.log n : ℂ) * a n

/-- The derivative of a single term of a Dirichlet polynomial along a vertical line. -/
theorem hasDerivAt_cpow_line {n : ℕ} (hn : 1 ≤ n) (σ t : ℝ) :
    HasDerivAt (fun x : ℝ => (n : ℂ) ^ (-((σ : ℂ) + (x : ℂ) * I)))
      ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) * (Real.log n : ℂ) * (-I)) t := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  have h1 : HasDerivAt (fun x : ℝ => ((x : ℂ))) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 := (h1.mul_const I).const_add ((σ : ℂ))
  rw [one_mul] at h2
  have hu : HasDerivAt (fun x : ℝ => -((σ : ℂ) + (x : ℂ) * I)) (-I) t := h2.neg
  have hg := Complex.hasStrictDerivAt_const_cpow (x := (n : ℂ))
    (y := -((σ : ℂ) + (t : ℂ) * I)) (Or.inl hn0)
  have h3 := hg.hasDerivAt.scomp t hu
  simp only [Function.comp_def] at h3
  have heq : (-I : ℂ) • ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) * Complex.log (n : ℂ))
      = (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) * (Real.log n : ℂ) * (-I) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast, smul_eq_mul]; ring
  rw [heq] at h3
  exact h3

/-- Along the vertical line `re s = σ`, the derivative of `t ↦ D(σ + i t)` is `-i` times the
Dirichlet polynomial with coefficients `a n log n`. -/
theorem hasDerivAt_dirichletPoly_line (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    HasDerivAt (fun x : ℝ => dirichletPoly a N ((σ : ℂ) + (x : ℂ) * I))
      (-I * dirichletPoly (logCoeff a) N ((σ : ℂ) + (t : ℂ) * I)) t := by
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      HasDerivAt (fun x : ℝ => a n * (n : ℂ) ^ (-((σ : ℂ) + (x : ℂ) * I)))
        (a n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) * (Real.log n : ℂ) * (-I))) t := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    exact (hasDerivAt_cpow_line hn.1 σ t).const_mul (a n)
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-((σ : ℂ) + (x : ℂ) * I)))
      (∑ n ∈ Finset.Icc 1 N,
        a n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) * (Real.log n : ℂ) * (-I))) t :=
    by
      have hfun : (∑ i ∈ Finset.Icc 1 N, fun x : ℝ => a i * (i : ℂ) ^ (-((σ : ℂ) + (x : ℂ) * I)))
          = fun x : ℝ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-((σ : ℂ) + (x : ℂ) * I)) := by
        funext x
        simp only [Finset.sum_apply]
      exact hfun ▸ HasDerivAt.sum hterm
  have hval : ∑ n ∈ Finset.Icc 1 N,
      a n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) * (Real.log n : ℂ) * (-I))
      = -I * dirichletPoly (logCoeff a) N ((σ : ℂ) + (t : ℂ) * I) := by
    rw [dirichletPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [logCoeff]
    ring
  rw [hval] at hsum
  exact hsum

/-- The Dirichlet polynomial with arbitrary coefficients is continuous along a vertical line. -/
theorem continuous_dirichletPoly_line_coeff (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    Continuous fun x : ℝ => dirichletPoly a N ((σ : ℂ) + (x : ℂ) * I) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_dirichletPoly_line a N σ x).continuousAt

/-- The mean-square weight of the coefficients `a n log n` is at most `(log N)²` times that of
the coefficients `a n`. -/
theorem sum_normSq_logCoeff_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ‖logCoeff a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)
      ≤ Real.log N ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogle : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
  have hnorm : ‖logCoeff a n‖ ^ 2 = Real.log n ^ 2 * ‖a n‖ ^ 2 := by
    simp only [logCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (by linarith) _
  rw [hnorm]
  have hsq : Real.log n ^ 2 ≤ Real.log N ^ 2 := by nlinarith
  have hna : (0 : ℝ) ≤ ‖a n‖ ^ 2 := by positivity
  nlinarith [mul_nonneg hna hpow]

/-- The mean square of a Dirichlet polynomial over `[0, T]`, in the one-sided form used below. -/
theorem integral_normSq_dirichletPoly_le_mvt (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ (T + 8 * (N : ℝ) * (1 + Real.log N))
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  have h := abs_integral_normSq_dirichletPoly_sub_diag_le_mvt a N σ T
  have h2 := (abs_le.mp h).2
  nlinarith [h2]

/-- **The discrete mean value theorem for Dirichlet polynomials.**  For `δ`-separated points
`t i` in `[δ/2, T - δ/2]`,

`∑_i ‖D(σ + i t_i)‖² ≤ (2/δ + δ (log N)²) (T + 8 N (1 + log N)) ∑_{n ≤ N} ‖a n‖² n^(-2σ)`. -/
theorem sum_normSq_dirichletPoly_at_separated_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2)) :
    ∑ i ∈ s, ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2
      ≤ (2 / δ + δ * Real.log N ^ 2) * (T + 8 * (N : ℝ) * (1 + Real.log N))
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  set S := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) with hS
  set E := 8 * (N : ℝ) * (1 + Real.log N) with hE
  have hlogN : 0 ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hN)
  have hE0 : 0 ≤ E := by
    rw [hE]; positivity
  have hS0 : 0 ≤ S := by
    rw [hS]
    refine Finset.sum_nonneg fun n hn => ?_
    have : (0 : ℝ) ≤ (n : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  -- the derivative of the polynomial along the line
  set f : ℝ → ℂ := fun x => dirichletPoly a N ((σ : ℂ) + (x : ℂ) * I) with hf
  set f' : ℝ → ℂ := fun x => -I * dirichletPoly (logCoeff a) N ((σ : ℂ) + (x : ℂ) * I) with hf'
  have hderiv : ∀ x, HasDerivAt f (f' x) x := fun x => hasDerivAt_dirichletPoly_line a N σ x
  have hf'cont : Continuous f' :=
    continuous_const.mul (continuous_dirichletPoly_line_coeff (logCoeff a) N σ)
  have hmem' : ∀ i ∈ s, t i ∈ Set.Icc (0 + δ / 2) (T - δ / 2) := by
    intro i hi
    simpa using hmem i hi
  have hgal := Gallagher.sum_normSq_le_of_separated hderiv hf'cont hδ hT hsep hmem'
  -- the two mean squares
  have hfsq : (∫ x in (0 : ℝ)..T, ‖f x‖ ^ 2) ≤ (T + E) * S :=
    integral_normSq_dirichletPoly_le_mvt a N σ T
  have hnormf' : ∀ x : ℝ, ‖f' x‖ = ‖dirichletPoly (logCoeff a) N ((σ : ℂ) + (x : ℂ) * I)‖ := by
    intro x
    rw [hf']
    simp
  have hf'sq : (∫ x in (0 : ℝ)..T, ‖f' x‖ ^ 2) ≤ (T + E) * (Real.log N ^ 2 * S) := by
    have hcongr : (∫ x in (0 : ℝ)..T, ‖f' x‖ ^ 2)
        = ∫ x in (0 : ℝ)..T, ‖dirichletPoly (logCoeff a) N ((σ : ℂ) + (x : ℂ) * I)‖ ^ 2 := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [hnormf' x]
    rw [hcongr]
    refine le_trans (integral_normSq_dirichletPoly_le_mvt (logCoeff a) N σ T) ?_
    have hTE : 0 ≤ T + E := by linarith
    exact mul_le_mul_of_nonneg_left (sum_normSq_logCoeff_le a N σ) hTE
  -- combine
  have hkey : δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2
      ≤ 2 * ((T + E) * S) + δ ^ 2 * ((T + E) * (Real.log N ^ 2 * S)) := by
    refine hgal.trans ?_
    have hδ2 : (0 : ℝ) ≤ δ ^ 2 := by positivity
    nlinarith [hfsq, hf'sq]
  have hdiv : ∑ i ∈ s, ‖f (t i)‖ ^ 2
      ≤ (2 * ((T + E) * S) + δ ^ 2 * ((T + E) * (Real.log N ^ 2 * S))) / δ := by
    rw [le_div_iff₀ hδ]
    linarith [hkey]
  have hsimp : (2 * ((T + E) * S) + δ ^ 2 * ((T + E) * (Real.log N ^ 2 * S))) / δ
      = (2 / δ + δ * Real.log N ^ 2) * (T + E) * S := by
    field_simp
  rw [hsimp] at hdiv
  exact hdiv

/-- **The large values count at separated points.**  If a Dirichlet polynomial of length `N` has
`‖D(σ + i t_i)‖ ≥ V` at `δ`-separated points `t_i ∈ [δ/2, T - δ/2]`, then the number of such
points is at most `(2/δ + δ (log N)²) (T + 8 N (1 + log N)) ∑ ‖a n‖² n^(-2σ) / V²`. -/
theorem card_le_of_dirichletPoly_large_separated (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T V : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2))
    (hbig : ∀ i ∈ s, V ≤ ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖) :
    (s.card : ℝ)
      ≤ (2 / δ + δ * Real.log N ^ 2) * (T + 8 * (N : ℝ) * (1 + Real.log N))
          * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / V ^ 2 := by
  have hlow : (s.card : ℝ) * V ^ 2
      ≤ ∑ i ∈ s, ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2 := by
    calc (s.card : ℝ) * V ^ 2 = ∑ _i ∈ s, V ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, ‖dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2 :=
          Finset.sum_le_sum fun i hi => by
            have := hbig i hi
            nlinarith [hV.le, norm_nonneg (dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I))]
  have hup := sum_normSq_dirichletPoly_at_separated_le a N σ hδ hT hsep hmem
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < V ^ 2)]
  linarith

end RiemannHypothesis
