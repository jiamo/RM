/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LargeSieve
import RiemannHypothesis.MontgomeryVaughan

/-!
# The cosecant form of the Montgomery–Vaughan inequality

For real points `α_1, …, α_n` that are `δ`-separated *modulo one*, that is
`‖α_r − α_s‖ ≥ δ` for `r ≠ s`, where `‖·‖ = intDist` is the distance to the
nearest integer and `0 < δ ≤ 1/2`, and for complex `u_1, …, u_n`,

  `|∑_{r ≠ s} u_r conj(u_s) / sin π(α_r − α_s)| ≤ δ⁻¹ ∑_r |u_r|²`.

This is the circle form of the generalized Hilbert inequality of H. L. Montgomery and
R. C. Vaughan (*The large sieve*, Mathematika 20 (1973), 119–134; see also Iwaniec–Kowalski,
*Analytic Number Theory*, Lemma 7.8, and Montgomery, *Ten Lectures*, Ch. 7).  It is the input
of the sharp large sieve `RiemannHypothesis.LargeSieveMV.large_sieve_mv`.

## The argument

This is Montgomery and Vaughan's eigenvector argument (route b), rerun with the kernel
`A r s = csc π(α_r − α_s)` (`cscKernel`) in place of `1/(λ_r − λ_s)`; compare
`RiemannHypothesis/MontgomeryVaughan.lean`, whose structure is followed step by step.

* `cscKernel_mul_cscKernel` — the identity `csc a csc b = csc (b − a) (cot a − cot b)`, so
  `∑_r A r s A r t = A s t (c_s − c_t) + 2 A s t cot π(α_s − α_t) + [s = t] b_s`, with
  `c_s = ∑_r cot π(α_r − α_s)` and `b_s = ∑_r A r s²`.
* `csc_eigen_bound` — for an eigenvector `A v = i μ v` the `c`-terms cancel, exactly as in the
  Hilbert case, and `|csc · cot| ≤ csc²` gives `μ² ‖v‖² ≤ 3 ∑_s b_s |v_s|²`.
* `sum_inv_sin_sq_le` — `b_s ≤ 1/(3δ²)`.  This uses the partial-fraction expansion
  `π² csc² πx = ∑_{m ∈ ℤ} (x + m)⁻²` (`hasSum_inv_sq_int`, derived here from Mathlib's
  cotangent expansion `cot_series_rep'` by term-by-term differentiation): the points
  `α_r − α_s + m` are `δ`-separated on the line, so the fibre count of
  `MontgomeryVaughan.colSq_le` bounds the double series by `2 ζ(2)/(π² δ²) = 1/(3δ²)`.
* `csc_eigenvalue_sq_le`, `csc_norm_apply_le` — hence `μ² ≤ δ⁻²`, and the spectral theorem
  gives the operator bound `‖H x‖ ≤ δ⁻¹ ‖x‖` for the Hermitian `H = i A`.
* `cosecantHilbertInequality` — Cauchy–Schwarz.

## Main results

* `RiemannHypothesis.HilbertCosecant.hasSum_inv_sq_int` —
  `∑_{m ∈ ℤ} (x + m)⁻² = π² / sin² πx`.
* `RiemannHypothesis.HilbertCosecant.cosecantHilbertInequality` — the inequality for points
  indexed by `Fin n`.
* `RiemannHypothesis.HilbertCosecant.cosecantHilbertInequality_finset` — the same over a
  finite set of any index type.

No hypothesis is assumed.  The optimality of the constant `δ⁻¹` is not proved here.
-/

open Complex Finset

namespace RiemannHypothesis

namespace HilbertCosecant

open LargeSieve Real

/-! ## The partial-fraction expansion of `csc²` -/

/-- Mathlib's partial-fraction expansion of the cotangent (`cot_series_rep'`), restricted to
real non-integers: `π cot πy − 1/y = ∑_{n ≥ 1} (1/(y − n) + 1/(y + n))`. -/
theorem real_cot_series {y : ℝ} (hy : ∀ m : ℤ, y ≠ m) :
    Real.pi * Real.cos (Real.pi * y) / Real.sin (Real.pi * y) - 1 / y
      = ∑' n : ℕ, (1 / (y - (n + 1)) + 1 / (y + (n + 1))) := by
  have hz : (y : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    exact hy n (by exact_mod_cast hn.symm)
  have h := cot_series_rep' hz
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  convert h using 1
  · rw [Complex.cot_eq_cos_div_sin]
    push_cast
    ring
  · congr 1
    ext n
    push_cast
    ring


/-- `sin πy ≠ 0` off the integers. -/
theorem sin_pi_mul_ne_zero_of_ne_int {y : ℝ} (hy : ∀ m : ℤ, y ≠ m) :
    Real.sin (π * y) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  apply hy m
  have := Real.pi_pos
  field_simp at hm
  linarith

/-- An elementary bound: `1/(y ± k)² ≤ A/k²` uniformly near a non-integer. -/
theorem inv_sq_le_of_far {y k c R : ℝ} (hc : 0 < c) (hk : 1 ≤ k) (hyR : |y| ≤ R)
    (hfar : c ≤ |y - k|) : 1 / (y - k) ^ 2 ≤ (1 + R / c) ^ 2 / k ^ 2 := by
  have hR : 0 ≤ R := (abs_nonneg y).trans hyR
  have hpos : 0 < |y - k| := lt_of_lt_of_le hc hfar
  have h1 : k ≤ (1 + R / c) * |y - k| := by
    have h2 : k ≤ |y - k| + R := by
      have := abs_sub_abs_le_abs_sub k y
      rw [abs_sub_comm k y] at this
      have : |k| = k := abs_of_pos (by linarith)
      linarith [abs_le.mp hyR]
    have h3 : R ≤ R / c * |y - k| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      exact mul_le_mul_of_nonneg_left hfar hR
    nlinarith
  rw [← sq_abs (y - k), div_le_div_iff₀ (pow_pos hpos 2) (pow_pos (by linarith) 2), one_mul,
    ← mul_pow]
  exact pow_le_pow_left₀ (by linarith) h1 2

/-- **The partial-fraction expansion of `π² csc² πx`** on the reals:
`∑_{m ∈ ℤ} (x + m)⁻² = π² / sin² πx` for every real non-integer `x`.  It is obtained by
differentiating `real_cot_series` term by term (`hasDerivAt_tsum_of_isPreconnected`) on a
neighbourhood of `x` that stays away from the integers. -/
theorem hasSum_inv_sq_int {x : ℝ} (hx : ∀ m : ℤ, x ≠ m) :
    HasSum (fun m : ℤ => 1 / (x + m) ^ 2) (π ^ 2 / Real.sin (π * x) ^ 2) := by
  set c : ℝ := |x - round x| with hcdef
  have hcpos : 0 < c := abs_pos.mpr (sub_ne_zero.mpr (hx _))
  have hcle : ∀ m : ℤ, c ≤ |x - m| := fun m => round_le x m
  set t : Set ℝ := Set.Ioo (x - c / 2) (x + c / 2) with htdef
  have hxt : x ∈ t := ⟨by linarith, by linarith⟩
  set R : ℝ := |x| + c with hRdef
  have hfar : ∀ y ∈ t, ∀ m : ℤ, c / 2 ≤ |y - m| := by
    intro y hy m
    obtain ⟨h1, h2⟩ := hy
    have := hcle m
    have h3 : |x - m| ≤ |y - m| + |x - y| := by
      calc |x - m| = |(y - m) + (x - y)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h4 : |x - y| < c / 2 := by rw [abs_lt]; constructor <;> linarith
    linarith
  have hyR : ∀ y ∈ t, |y| ≤ R := by
    intro y hy
    obtain ⟨h1, h2⟩ := hy
    have : |y| ≤ |x| + |y - x| := by
      calc |y| = |x + (y - x)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h4 : |y - x| < c / 2 := by rw [abs_lt]; constructor <;> linarith
    rw [hRdef]; linarith
  have hnotint : ∀ y ∈ t, ∀ m : ℤ, y ≠ m := by
    intro y hy m he
    have := hfar y hy m
    rw [he, sub_self, abs_zero] at this
    linarith
  set g : ℕ → ℝ → ℝ := fun n y => 1 / (y - (n + 1)) + 1 / (y + (n + 1)) with hg
  set g' : ℕ → ℝ → ℝ := fun n y => -(1 / (y - (n + 1)) ^ 2) - 1 / (y + (n + 1)) ^ 2
    with hg'
  set A : ℝ := (1 + R / (c / 2)) ^ 2 with hA
  set u : ℕ → ℝ := fun n => 2 * A * (1 / ((n : ℝ) + 1) ^ 2) with hu
  have hsu : Summable u := by
    have : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    exact this.mul_left _
  have hderiv : ∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have h1 : y - (n + 1) ≠ 0 := by
      intro h; exact hnotint y hy ((n : ℤ) + 1) (by push_cast; linarith)
    have h2 : y + (n + 1) ≠ 0 := by
      intro h; exact hnotint y hy (-((n : ℤ) + 1)) (by push_cast; linarith)
    have d1 : HasDerivAt (fun y : ℝ => y - (n + 1)) 1 y := (hasDerivAt_id y).sub_const _
    have d2 : HasDerivAt (fun y : ℝ => y + (n + 1)) 1 y := (hasDerivAt_id y).add_const _
    have := ((hasDerivAt_const y (1:ℝ)).div d1 h1).add ((hasDerivAt_const y (1:ℝ)).div d2 h2)
    refine (this : HasDerivAt (g n) _ y).congr_deriv ?_
    simp only [hg']
    ring
  have hbound : ∀ n y, y ∈ t → ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hk : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hc2 : (0 : ℝ) < c / 2 := by linarith
    have b1 : 1 / (y - (n + 1)) ^ 2 ≤ A / ((n : ℝ) + 1) ^ 2 :=
      inv_sq_le_of_far (R := R) hc2 hk (hyR y hy) (by simpa using hfar y hy ((n : ℤ) + 1))
    have b2 : 1 / (y + (n + 1)) ^ 2 ≤ A / ((n : ℝ) + 1) ^ 2 := by
      have := inv_sq_le_of_far (y := -y) (R := R) hc2 hk (by rw [abs_neg]; exact hyR y hy) (by
        have h := hfar y hy (-((n : ℤ) + 1))
        push_cast at h
        rw [show -y - ((n : ℝ) + 1) = -(y - -((n : ℝ) + 1)) by ring, abs_neg]; exact h)
      rw [show (-y - ((n : ℝ) + 1)) ^ 2 = (y + (n + 1)) ^ 2 by ring] at this
      exact this
    have p1 : 0 ≤ 1 / (y - (n + 1)) ^ 2 := by positivity
    have p2 : 0 ≤ 1 / (y + (n + 1)) ^ 2 := by positivity
    simp only [hg', hu, Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · have : A / ((n : ℝ) + 1) ^ 2 = A * (1 / ((n : ℝ) + 1) ^ 2) := by ring
      linarith
    · have : A / ((n : ℝ) + 1) ^ 2 = A * (1 / ((n : ℝ) + 1) ^ 2) := by ring
      have : 0 ≤ A * (1 / ((n : ℝ) + 1) ^ 2) := by positivity
      linarith
  have hsum0 : Summable fun n => g n x := by
    have h := real_cot_series hx
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h
    -- a summability fact from the complex version
    have hz : (x : ℂ) ∈ Complex.integerComplement := by
      rw [Complex.mem_integerComplement_iff]
      rintro ⟨n, hn⟩
      exact hx n (by exact_mod_cast hn.symm)
    have hs := summable_cotTerm hz
    apply hns
    have : Summable (fun n : ℕ => ((g n x : ℝ) : ℂ)) := by
      convert hs using 1
      ext n
      simp only [hg, cotTerm]
      push_cast
      ring
    exact (Complex.summable_ofReal).mp this
  have hT := hasDerivAt_tsum_of_isPreconnected hsu isOpen_Ioo (isPreconnected_Ioo) hderiv hbound
    hxt hsum0 hxt
  -- the left side
  have hsin : Real.sin (π * x) ≠ 0 := sin_pi_mul_ne_zero_of_ne_int hx
  have hx0 : x ≠ 0 := by simpa using hx 0
  have hL : HasDerivAt (fun y => π * Real.cos (π * y) / Real.sin (π * y) - 1 / y)
      (-(π ^ 2 / Real.sin (π * x) ^ 2) + 1 / x ^ 2) x := by
    have dsin : HasDerivAt (fun y => Real.sin (π * y)) (Real.cos (π * x) * π) x := by
      have := ((hasDerivAt_id x).const_mul π).sin
      simpa using this
    have dcos :
        HasDerivAt (fun y => π * Real.cos (π * y)) (π * (-Real.sin (π * x) * π)) x := by
      have := ((hasDerivAt_id x).const_mul π).cos
      simpa using this.const_mul π
    have := (dcos.div dsin hsin).sub ((hasDerivAt_const x (1:ℝ)).div (hasDerivAt_id x) hx0)
    refine (this : HasDerivAt (fun y => π * Real.cos (π * y) / Real.sin (π * y) - 1 / y) _
      x).congr_deriv ?_
    have hcs := Real.sin_sq_add_cos_sq (π * x)
    simp only [id]
    field_simp
    linear_combination (-(π ^ 2 * x ^ 2)) * hcs
  have heq : (fun y => π * Real.cos (π * y) / Real.sin (π * y) - 1 / y) =ᶠ[nhds x]
      (fun z => ∑' n, g n z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxt] with y hy
    exact real_cot_series (hnotint y hy)
  have huniq := (hL.congr_of_eventuallyEq heq.symm).unique hT
  -- now assemble the `ℤ`-indexed sum
  have hsg' : Summable fun n => g' n x := (hsu.of_norm_bounded fun n => hbound n x hxt)
  have hp1 : Summable fun n : ℕ => 1 / (x - (n + 1)) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsg'.neg
    simp only [hg', neg_sub, sub_neg_eq_add]
    have : 0 ≤ 1 / (x + (n + 1)) ^ 2 := by positivity
    linarith
  have hp2 : Summable fun n : ℕ => 1 / (x + (n + 1)) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsg'.neg
    simp only [hg', neg_sub, sub_neg_eq_add]
    have : 0 ≤ 1 / (x - (n + 1)) ^ 2 := by positivity
    linarith
  have hZ := HasSum.of_add_one_of_neg_add_one (f := fun m : ℤ => 1 / (x + m) ^ 2)
    (by simpa using hp2.hasSum) (by
      have := hp1.hasSum
      convert this using 2 with n
      push_cast; ring_nf)
  convert hZ using 1
  have htsum : ∑' n, g' n x
      = -(∑' n : ℕ, 1 / (x - (n + 1)) ^ 2) - ∑' n : ℕ, 1 / (x + (n + 1)) ^ 2 := by
    simp only [hg']
    rw [hp1.neg.tsum_sub hp2, tsum_neg]
  rw [htsum] at huniq
  simp only [Int.cast_zero, add_zero, one_div] at hZ huniq ⊢
  linarith


/-! ## The column sums of the squared cosecant kernel -/

/-- For a `δ`-separated finite family of reals and a centre `c` of it,
`∑_{x ≠ c} (λ_c − λ_x)⁻² ≤ 2 ζ(2) δ⁻² = π² / (3 δ²)`. -/
theorem sum_inv_sq_le_of_separated {ι : Type*} [DecidableEq ι] {S : Finset ι} {lam : ι → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |lam x - lam y|) {c : ι}
    (hc : c ∈ S) :
    ∑ x ∈ S.erase c, 1 / (lam c - lam x) ^ 2 ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  have hsep' : WellSpaced.Separated S lam δ := hsep
  set g : ι → ℕ := fun x => ⌊|lam c - lam x| / δ⌋₊ with hg
  have hterm : ∀ x ∈ S.erase c,
      1 / (lam c - lam x) ^ 2 ≤ 1 / δ ^ 2 * (1 / (g x : ℝ) ^ 2) := by
    intro x hx
    have hne : x ≠ c := Finset.ne_of_mem_erase hx
    have hd : δ ≤ |lam c - lam x| := hsep c hc x (Finset.mem_of_mem_erase hx) hne.symm
    have hq : (1 : ℝ) ≤ |lam c - lam x| / δ := by rw [le_div_iff₀ hδ]; linarith
    have hg1 : (1 : ℝ) ≤ g x := by
      have : 1 ≤ g x := Nat.le_floor (by exact_mod_cast hq)
      exact_mod_cast this
    have hgle : (g x : ℝ) * δ ≤ |lam c - lam x| := by
      have := Nat.floor_le (by positivity : (0:ℝ) ≤ |lam c - lam x| / δ)
      rw [le_div_iff₀ hδ] at this; exact this
    rw [show 1 / δ ^ 2 * (1 / (g x : ℝ) ^ 2) = 1 / ((g x : ℝ) * δ) ^ 2 by ring, ← sq_abs]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) hgle 2
  have hsumm : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) := hasSum_zeta_two.summable
  set T := (S.erase c).image g
  calc ∑ x ∈ S.erase c, 1 / (lam c - lam x) ^ 2
      ≤ ∑ x ∈ S.erase c, 1 / δ ^ 2 * (1 / (g x : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = 1 / δ ^ 2 * ∑ k ∈ T, ∑ x ∈ S.erase c with g x = k, (1 / (g x : ℝ) ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to]
        intro x hx; exact Finset.mem_image_of_mem g hx
    _ ≤ 1 / δ ^ 2 * ∑ k ∈ T, 2 * (1 / (k : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
        rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2],
          Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast WellSpaced.card_fiber_le_two hδ hsep' c k
    _ ≤ 1 / δ ^ 2 * (2 * (Real.pi ^ 2 / 6)) := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          (by positivity)
        rw [← hasSum_zeta_two.tsum_eq]
        exact hsumm.sum_le_tsum T (fun _ _ => by positivity)
    _ = Real.pi ^ 2 / (3 * δ ^ 2) := by field_simp; ring

/-- A real number at distance at least `δ > 0` from the integers is not an integer. -/
theorem ne_int_of_le_intDist {θ δ : ℝ} (hδ : 0 < δ) (h : δ ≤ intDist θ) (m : ℤ) :
    θ ≠ m := by
  intro he
  have := intDist_le_abs_sub_int θ m
  rw [he, sub_self, abs_zero] at this
  rw [he] at h
  linarith

/-- **The column sums of `csc²`.**  For points `α_r` that are `δ`-separated modulo one,
`∑_{r ≠ s} csc² π(α_r − α_s) ≤ 1 / (3 δ²)`.  The proof expands
`π² csc² πx = ∑_{m ∈ ℤ} (x + m)⁻²` (`hasSum_inv_sq_int`): the points
`α_r − α_s + m` are `δ`-separated on the line and at distance at least `δ` from `0`, so
`sum_inv_sq_le_of_separated` bounds every finite part of the double series by `π²/(3δ²)`. -/
theorem sum_inv_sin_sq_le {n : ℕ} (α : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ intDist (α r - α s)) (s : Fin n) :
    ∑ r ∈ Finset.univ.erase s, 1 / Real.sin (Real.pi * (α r - α s)) ^ 2
      ≤ 1 / (3 * δ ^ 2) := by
  classical
  set f : Fin n → ℤ → ℝ := fun r m => 1 / (α r - α s + m) ^ 2 with hf
  have hnotint : ∀ r ∈ Finset.univ.erase s, ∀ m : ℤ, α r - α s ≠ m := fun r hr m =>
    ne_int_of_le_intDist hδ (hsep r s (Finset.ne_of_mem_erase hr)) m
  have hHS : ∀ r ∈ Finset.univ.erase s,
      HasSum (f r) (Real.pi ^ 2 / Real.sin (Real.pi * (α r - α s)) ^ 2) :=
    fun r hr => hasSum_inv_sq_int (hnotint r hr)
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hrw : ∀ r ∈ Finset.univ.erase s, 1 / Real.sin (Real.pi * (α r - α s)) ^ 2
      = (1 / Real.pi ^ 2) * ∑' m, f r m := by
    intro r hr
    rw [(hHS r hr).tsum_eq]
    field_simp
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum,
    ← Summable.tsum_finsetSum (fun r hr => (hHS r hr).summable)]
  -- every finite part of the double series is at most `π² / (3 δ²)`
  have hfin : ∀ T : Finset ℤ, ∑ m ∈ T, ∑ r ∈ Finset.univ.erase s, f r m
      ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
    intro T
    set lam : Fin n × ℤ → ℝ := fun p => α p.1 - α s + p.2 with hlam
    set S : Finset (Fin n × ℤ) := insert (s, 0) ((Finset.univ.erase s) ×ˢ T) with hS
    have hsepS : WellSpaced.Separated S lam δ := by
      intro p _ q _ hpq
      by_cases h1 : p.1 = q.1
      · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
        have hdiff : lam p - lam q = ((p.2 - q.2 : ℤ) : ℝ) := by
          simp only [hlam, h1]; push_cast; ring
        rw [hdiff]
        have : (1 : ℝ) ≤ |((p.2 - q.2 : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h2)
        linarith
      · have hdiff : lam p - lam q = (α p.1 - α q.1) - ((q.2 - p.2 : ℤ) : ℝ) := by
          simp only [hlam]; push_cast; ring
        rw [hdiff]
        exact (hsep p.1 q.1 h1).trans (intDist_le_abs_sub_int _ _)
    have hcS : ((s, 0) : Fin n × ℤ) ∈ S := Finset.mem_insert_self _ _
    have hkey := sum_inv_sq_le_of_separated hδ hsepS hcS
    have hnot : ((s, 0) : Fin n × ℤ) ∉ (Finset.univ.erase s) ×ˢ T := by
      simp
    rw [hS, Finset.erase_insert hnot, Finset.sum_product] at hkey
    rw [Finset.sum_comm]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun m _ => ?_) hkey
    simp only [hf, hlam]
    rw [show (α s - α s + ((0 : ℤ) : ℝ) - (α r - α s + m)) = -(α r - α s + m) by
      push_cast; ring,
      neg_sq]
  have hnn : 0 ≤ fun m => ∑ r ∈ Finset.univ.erase s, f r m :=
    fun m => Finset.sum_nonneg fun r _ => by positivity
  have htsum := Real.tsum_le_of_sum_le hnn hfin
  calc 1 / Real.pi ^ 2 * ∑' m, ∑ r ∈ Finset.univ.erase s, f r m
      ≤ 1 / Real.pi ^ 2 * (Real.pi ^ 2 / (3 * δ ^ 2)) :=
        mul_le_mul_of_nonneg_left htsum (by positivity)
    _ = 1 / (3 * δ ^ 2) := by field_simp

/-! ## The cosecant and cotangent kernels -/

variable {n : ℕ}

/-- The cosecant kernel `csc π(α_r − α_s)`.  On the diagonal it is `1 / sin 0 = 0`. -/
noncomputable def cscKernel (α : Fin n → ℝ) (r s : Fin n) : ℝ :=
  1 / Real.sin (Real.pi * (α r - α s))

/-- The cotangent kernel `cot π(α_r − α_s)`.  On the diagonal it is `cos 0 / sin 0 = 0`. -/
noncomputable def cotKernel (α : Fin n → ℝ) (r s : Fin n) : ℝ :=
  Real.cos (Real.pi * (α r - α s)) / Real.sin (Real.pi * (α r - α s))

lemma cscKernel_self (α : Fin n → ℝ) (r : Fin n) : cscKernel α r r = 0 := by
  simp [cscKernel]

lemma cotKernel_self (α : Fin n → ℝ) (r : Fin n) : cotKernel α r r = 0 := by
  simp [cotKernel]

lemma cscKernel_swap (α : Fin n → ℝ) (r s : Fin n) :
    cscKernel α s r = - cscKernel α r s := by
  unfold cscKernel
  rw [← neg_sub, mul_neg, Real.sin_neg, div_neg]

lemma cotKernel_swap (α : Fin n → ℝ) (r s : Fin n) :
    cotKernel α s r = - cotKernel α r s := by
  unfold cotKernel
  rw [← neg_sub, mul_neg, Real.sin_neg, Real.cos_neg, div_neg]

/-- `|csc · cot| ≤ csc²`, because `|cos| ≤ 1`. -/
lemma abs_csc_mul_cot_le (α : Fin n → ℝ) (r s : Fin n) :
    |cscKernel α r s * cotKernel α r s| ≤ cscKernel α r s ^ 2 := by
  unfold cscKernel cotKernel
  set x := Real.pi * (α r - α s)
  rw [show 1 / Real.sin x * (Real.cos x / Real.sin x) = Real.cos x * (1 / Real.sin x) ^ 2 by ring,
    abs_mul, abs_of_nonneg (sq_nonneg (1 / Real.sin x))]
  exact mul_le_of_le_one_left (sq_nonneg _) (Real.abs_cos_le_one x)

/-- The cosecant identity `csc a csc b = csc (b − a) (cot a − cot b)`, with its two correction
terms at `r = s` and `r = t`. -/
lemma cscKernel_mul_cscKernel {α : Fin n → ℝ}
    (hinj : ∀ r s, r ≠ s → Real.sin (Real.pi * (α r - α s)) ≠ 0)
    (r : Fin n) {s t : Fin n} (hst : s ≠ t) :
    cscKernel α r s * cscKernel α r t
      = cscKernel α s t * (cotKernel α r s - cotKernel α r t)
        + (if r = s then cscKernel α s t * cotKernel α s t else 0)
        + (if r = t then cscKernel α s t * cotKernel α s t else 0) := by
  by_cases hrs : r = s
  · subst hrs
    simp [cscKernel_self, cotKernel_self, hst]
  by_cases hrt : r = t
  · subst hrt
    simp [cscKernel_self, cotKernel_self, hrs, cotKernel_swap α r s]
  simp only [hrs, hrt, if_false, add_zero]
  have h1 := hinj _ _ hrs
  have h2 := hinj _ _ hrt
  have h3 := hinj _ _ hst
  unfold cscKernel cotKernel
  have hsub : Real.pi * (α s - α t) = Real.pi * (α r - α t) - Real.pi * (α r - α s) := by ring
  rw [hsub, Real.sin_sub] at h3 ⊢
  generalize Real.pi * (α r - α s) = A at *
  generalize Real.pi * (α r - α t) = B at *
  have h3' : Real.sin B * Real.cos A - Real.sin A * Real.cos B ≠ 0 := by
    rwa [mul_comm (Real.sin A)]
  field_simp

/-- `c_s = ∑_r cot π(α_r − α_s)`. -/
noncomputable def cotColSum (α : Fin n → ℝ) (s : Fin n) : ℝ := ∑ r, cotKernel α r s

/-- `b_s = ∑_r csc² π(α_r − α_s)`. -/
noncomputable def cscColSq (α : Fin n → ℝ) (s : Fin n) : ℝ := ∑ r, cscKernel α r s ^ 2

/-- Summed over `r`, the cosecant identity holds for all `s`, `t`. -/
lemma sum_cscKernel_mul_cscKernel {α : Fin n → ℝ}
    (hinj : ∀ r s, r ≠ s → Real.sin (Real.pi * (α r - α s)) ≠ 0) (s t : Fin n) :
    ∑ r, cscKernel α r s * cscKernel α r t
      = cscKernel α s t * (cotColSum α s - cotColSum α t)
        + 2 * (cscKernel α s t * cotKernel α s t)
        + (if s = t then cscColSq α s else 0) := by
  by_cases hst : s = t
  · subst hst
    simp [cscKernel_self, cscColSq, sq]
  rw [Finset.sum_congr rfl fun r _ => cscKernel_mul_cscKernel hinj r hst]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hst, if_false, cotColSum]
  ring

/-- The heart of the argument, as in `MontgomeryVaughan.eigen_bound`: for an eigenvector
`A v = i μ v` of the real skew-symmetric matrix `A = (csc π(α_r − α_s))`, the terms with the
cotangent column sums cancel and `μ² ‖v‖² ≤ 3 ∑_s b_s |v_s|²`. -/
theorem csc_eigen_bound {α : Fin n → ℝ}
    (hinj : ∀ r s, r ≠ s → Real.sin (Real.pi * (α r - α s)) ≠ 0)
    (v : Fin n → ℂ) (μ : ℝ)
    (hv : ∀ r, ∑ s, (cscKernel α r s : ℂ) * v s = I * μ * v r) :
    μ ^ 2 * ∑ r, ‖v r‖ ^ 2 ≤ 3 * ∑ s, cscColSq α s * ‖v s‖ ^ 2 := by
  set K : Fin n → Fin n → ℝ := cscKernel α with hK
  set C : Fin n → Fin n → ℝ := cotKernel α with hC
  set a := cotColSum α with ha
  set b := cscColSq α with hb
  have hvc : ∀ r, ∑ s, (K r s : ℂ) * (starRingEnd ℂ) (v s)
      = -(I * μ) * (starRingEnd ℂ) (v r) := by
    intro r
    have := congrArg (starRingEnd ℂ) (hv r)
    simpa [map_sum, map_mul, Complex.conj_ofReal, Complex.conj_I] using this
  have hcol : ∀ t, ∑ s, (K s t : ℂ) * v s = -(I * μ * v t) := by
    intro t
    rw [← hv t, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hK, cscKernel_swap α t s]; push_cast; ring
  have hnorm : ∀ r, v r * (starRingEnd ℂ) (v r) = ((‖v r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hL : (∑ r, (∑ s, (K r s : ℂ) * v s) * (starRingEnd ℂ) (∑ t, (K r t : ℂ) * v t))
      = ((μ ^ 2 * ∑ r, ‖v r‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hv r, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have := hnorm r
    push_cast at this
    linear_combination (μ:ℂ)^2 * this - (μ:ℂ)^2 * v r * (starRingEnd ℂ) (v r) * Complex.I_sq
  have hE : (∑ r, (∑ s, (K r s : ℂ) * v s) * (starRingEnd ℂ) (∑ t, (K r t : ℂ) * v t))
      = ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((∑ r, K r s * K r t : ℝ) : ℂ) := by
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hX1 : ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a s : ℂ))
      = ∑ s, (a s : ℂ) * (-(I * μ)) * ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    have := hvc s
    rw [← hnorm s]
    calc ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a s : ℂ))
        = v s * (a s : ℂ) * ∑ t, (K s t : ℂ) * (starRingEnd ℂ) (v t) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => ?_; ring
      _ = _ := by rw [this]; ring
  have hX2 : ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a t : ℂ))
      = ∑ s, (a s : ℂ) * (-(I * μ)) * ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have := hcol t
    rw [← hnorm t]
    calc ∑ s, v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a t : ℂ))
        = (starRingEnd ℂ) (v t) * (a t : ℂ) * ∑ s, (K s t : ℂ) * v s := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring
      _ = _ := by rw [this]; ring
  have hmain : ((μ ^ 2 * ∑ r, ‖v r‖ ^ 2 : ℝ) : ℂ)
      = 2 * ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t * C s t : ℝ) : ℂ)
        + ((∑ s, b s * ‖v s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hL, hE]
    have hterm : ∀ s t, v s * (starRingEnd ℂ) (v t) * ((∑ r, K r s * K r t : ℝ) : ℂ)
        = v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a s : ℂ))
          - v s * (starRingEnd ℂ) (v t) * ((K s t : ℂ) * (a t : ℂ))
          + 2 * (v s * (starRingEnd ℂ) (v t) * ((K s t * C s t : ℝ) : ℂ))
          + (if s = t then ((b s * ‖v s‖ ^ 2 : ℝ) : ℂ) else 0) := by
      intro s t
      have hst : ∑ r, K r s * K r t
          = K s t * (a s - a t) + 2 * (K s t * C s t) + (if s = t then b s else 0) :=
        sum_cscKernel_mul_cscKernel hinj s t
      rw [hst]
      split_ifs with h
      · subst h
        rw [show ((b s * ‖v s‖ ^ 2 : ℝ) : ℂ)
            = (b s : ℂ) * ((‖v s‖ ^ 2 : ℝ) : ℂ) by
            push_cast; ring,
          ← hnorm s]
        push_cast; ring
      · push_cast; ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, hX1, hX2, ← Finset.mul_sum]
    push_cast
    ring
  have hKs : ∀ s t, K s t ^ 2 = K t s ^ 2 := fun s t => by
    rw [hK, cscKernel_swap α s t, neg_sq]
  have h1 : ∑ s, ∑ t, K s t ^ 2 * ‖v s‖ ^ 2 = ∑ s, b s * ‖v s‖ ^ 2 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun t _ => hKs s t
  have h2 : ∑ s, ∑ t, K s t ^ 2 * ‖v t‖ ^ 2 = ∑ t, b t * ‖v t‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_mul]
    rfl
  have hY : (∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t * C s t : ℝ) : ℂ)).re
      ≤ ∑ s, b s * ‖v s‖ ^ 2 := by
    calc (∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t * C s t : ℝ) : ℂ)).re
        ≤ ∑ s, ∑ t, K s t ^ 2 * ((‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2) := by
          rw [Complex.re_sum]
          refine Finset.sum_le_sum fun s _ => ?_
          rw [Complex.re_sum]
          refine Finset.sum_le_sum fun t _ => ?_
          rw [Complex.re_mul_ofReal]
          have hab := abs_csc_mul_cot_le α s t
          have hw : 0 ≤ (‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2 := by positivity
          have hz :
              |(v s * (starRingEnd ℂ) (v t)).re| ≤ (‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2 := by
            refine (Complex.abs_re_le_norm _).trans ?_
            rw [norm_mul, RCLike.norm_conj]
            nlinarith [sq_nonneg (‖v s‖ - ‖v t‖)]
          set w := (‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2
          set z := (v s * (starRingEnd ℂ) (v t)).re
          set p := K s t * C s t
          calc z * p ≤ |z * p| := le_abs_self _
            _ = |z| * |p| := abs_mul _ _
            _ ≤ w * K s t ^ 2 := mul_le_mul hz hab (abs_nonneg _) hw
            _ = K s t ^ 2 * w := mul_comm _ _
      _ = (∑ s, ∑ t, K s t ^ 2 * ‖v s‖ ^ 2
            + ∑ s, ∑ t, K s t ^ 2 * ‖v t‖ ^ 2) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
      _ = ∑ s, b s * ‖v s‖ ^ 2 := by rw [h1, h2]; ring
  have hre := congrArg Complex.re hmain
  rw [Complex.ofReal_re, Complex.add_re, Complex.ofReal_re] at hre
  have h2' : (2 * ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t * C s t : ℝ) : ℂ)).re
      = 2 * (∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((K s t * C s t : ℝ) : ℂ)).re := by
    simp
  rw [h2'] at hre
  linarith

/-- Every eigenvalue `i μ` of `A = (csc π(α_r − α_s))` has `μ² ≤ δ⁻²`. -/
theorem csc_eigenvalue_sq_le {α : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ intDist (α r - α s))
    (v : Fin n → ℂ) (μ : ℝ) (hv0 : ∃ r, v r ≠ 0)
    (hv : ∀ r, ∑ s, (cscKernel α r s : ℂ) * v s = I * μ * v r) :
    μ ^ 2 ≤ (δ⁻¹) ^ 2 := by
  have hinj : ∀ r s, r ≠ s → Real.sin (Real.pi * (α r - α s)) ≠ 0 := fun r s h =>
    sin_pi_mul_ne_zero_of_ne_int (ne_int_of_le_intDist hδ (hsep r s h))
  have h1 := csc_eigen_bound hinj v μ hv
  have hcol : ∀ s, cscColSq α s ≤ 1 / (3 * δ ^ 2) := by
    intro s
    have h := sum_inv_sin_sq_le α hδ hδ2 hsep s
    have hsplit : cscColSq α s = ∑ r ∈ Finset.univ.erase s, cscKernel α r s ^ 2 := by
      unfold cscColSq
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      simp [cscKernel]
    rw [hsplit]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun r _ => ?_) h
    simp [cscKernel]
  have h2 : 3 * ∑ s, cscColSq α s * ‖v s‖ ^ 2 ≤ (δ⁻¹) ^ 2 * ∑ r, ‖v r‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have h3 : 3 * cscColSq α s ≤ (δ⁻¹) ^ 2 := by
      have := hcol s
      rw [inv_pow, ← one_div]
      calc 3 * cscColSq α s ≤ 3 * (1 / (3 * δ ^ 2)) := by linarith
        _ = 1 / δ ^ 2 := by field_simp
    nlinarith [sq_nonneg ‖v s‖]
  obtain ⟨r0, hr0⟩ := hv0
  have hpos : 0 < ∑ r, ‖v r‖ ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun r => ‖v r‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ r0))
  exact le_of_mul_le_mul_right (h1.trans h2) hpos

/-! ## The spectral theorem -/

/-- The Hermitian matrix `H = i A`, `H r s = i csc π(α_r − α_s)`. -/
noncomputable def cscMatrix (α : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun r s => I * (cscKernel α r s : ℂ)

lemma cscMatrix_isHermitian (α : Fin n → ℝ) : (cscMatrix α).IsHermitian := by
  ext r s
  simp only [cscMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, cscKernel_swap α r s]
  push_cast; ring

lemma toEuclideanLin_csc_apply (α : Fin n → ℝ) (x : EuclideanSpace ℂ (Fin n)) (r : Fin n) :
    (Matrix.toEuclideanLin (cscMatrix α) x).ofLp r
      = I * ∑ s, (cscKernel α r s : ℂ) * x.ofLp s := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, cscMatrix, Finset.mul_sum, mul_assoc]

/-- A bound `μ² ≤ C` on the eigenvalues of `A` gives `‖H x‖² ≤ C ‖x‖²`. -/
lemma csc_norm_apply_le {α : Fin n → ℝ} (C : ℝ)
    (heig : ∀ (v : Fin n → ℂ) (μ : ℝ), (∃ r, v r ≠ 0) →
      (∀ r, ∑ s, (cscKernel α r s : ℂ) * v s = I * μ * v r) → μ ^ 2 ≤ C)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin (cscMatrix α) x‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
  set T := Matrix.toEuclideanLin (cscMatrix α)
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (cscMatrix_isHermitian α)
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by simp
  set b := hT.eigenvectorBasis hn
  set ν := hT.eigenvalues hn
  have hν : ∀ i, ν i ^ 2 ≤ C := by
    intro i
    have hu := hT.apply_eigenvectorBasis hn i
    rw [← neg_sq]
    refine heig (b i).ofLp (-ν i) ?_ ?_
    · by_contra h
      push Not at h
      have : b i = 0 := by ext r; simp [h r]
      have h1 := b.orthonormal.1 i
      rw [this, norm_zero] at h1
      exact zero_ne_one h1
    · intro r
      have := congrArg (fun y : EuclideanSpace ℂ (Fin n) => y.ofLp r) hu
      simp only [toEuclideanLin_csc_apply, T] at this
      rw [PiLp.smul_apply] at this
      push_cast
      linear_combination
        (-I) * this + (∑ s, (cscKernel α r s : ℂ) * (b i).ofLp s) * Complex.I_sq
  have hrepr : ∀ i, b.repr (T x) i = (ν i : ℂ) * b.repr x i := by
    intro i
    rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, ← hT,
      hT.apply_eigenvectorBasis hn i, inner_smul_left, RCLike.conj_ofReal]
    rfl
  rw [← b.repr.norm_map (T x), ← b.repr.norm_map x, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hrepr, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_right (hν i) (by positivity)

/-! ## The theorem -/

/-- **The cosecant form of the Montgomery–Vaughan inequality.**  For real points `α_r` that are
`δ`-separated modulo one (`‖α_r − α_s‖ ≥ δ` for `r ≠ s`, with `0 < δ ≤ 1/2`) and
complex `u_r`,

`|∑_{r ≠ s} u_r conj(u_s) / sin π(α_r − α_s)| ≤ δ⁻¹ ∑_r |u_r|²`. -/
theorem cosecantHilbertInequality {n : ℕ} (α : Fin n → ℝ) (u : Fin n → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ r s : Fin n, r ≠ s → δ ≤ intDist (α r - α s)) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (α r - α s)) : ℂ)‖
      ≤ δ⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
  set T := Matrix.toEuclideanLin (cscMatrix α)
  set xe : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 u
  have hop : ‖T xe‖ ≤ δ⁻¹ * ‖xe‖ := by
    have h := csc_norm_apply_le (α := α) ((δ⁻¹) ^ 2)
      (fun v μ hv0 hv => csc_eigenvalue_sq_le hδ hδ2 hsep v μ hv0 hv) xe
    rw [← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  have hxe : ‖xe‖ ^ 2 = ∑ r, ‖u r‖ ^ 2 := EuclideanSpace.norm_sq_eq xe
  have hform : ∑ r, ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) /
      (Real.sin (Real.pi * (α r - α s)) : ℂ) = I * inner ℂ (T xe) xe := by
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [toEuclideanLin_csc_apply]
    have hdiag : ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) /
        (Real.sin (Real.pi * (α r - α s)) : ℂ)
        = ∑ s, u r * (starRingEnd ℂ) (u s) * (cscKernel α r s : ℂ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      simp only [cscKernel_self, Complex.ofReal_zero, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [cscKernel]
      push_cast
      ring
    rw [hdiag]
    have hx : ∀ i, xe.ofLp i = u i := fun i => rfl
    simp only [RCLike.inner_apply, map_mul, map_sum, Complex.conj_I, Complex.conj_ofReal, hx]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    linear_combination (u r * (starRingEnd ℂ) (u s) * (cscKernel α r s : ℂ)) * Complex.I_sq
  rw [hform, norm_mul, Complex.norm_I, one_mul, ← hxe]
  calc ‖inner ℂ (T xe) xe‖ ≤ ‖T xe‖ * ‖xe‖ := norm_inner_le_norm _ _
    _ ≤ δ⁻¹ * ‖xe‖ * ‖xe‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = δ⁻¹ * ‖xe‖ ^ 2 := by ring

/-- **The cosecant inequality over a finite set**, the form used by the large sieve: for a
finite set `s` and points `t i`, `i ∈ s`, that are `δ`-separated modulo one,
`|∑_{i ≠ j ∈ s} x_i conj(x_j) / sin π(t_i − t_j)| ≤ δ⁻¹ ∑_{i ∈ s} |x_i|²`. -/
theorem cosecantHilbertInequality_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : ι → ℝ) (x : ι → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ intDist (t i - t j)) :
    ‖∑ i ∈ s, ∑ j ∈ s.erase i,
        x i * (starRingEnd ℂ) (x j) / (Real.sin (Real.pi * (t i - t j)) : ℂ)‖
      ≤ δ⁻¹ * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  set e := s.equivFin
  set α : Fin s.card → ℝ := fun k => t (e.symm k) with hα
  set u : Fin s.card → ℂ := fun k => x (e.symm k) with hu
  have hre : ∀ {M : Type} [AddCommMonoid M] (g : ι → M),
      ∑ i ∈ s, g i = ∑ k, g (e.symm k) := by
    intro M _ g
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp e.symm (fun i => g i)).symm
  have hsepα : ∀ r q : Fin s.card, r ≠ q → δ ≤ intDist (α r - α q) := by
    intro r q hrq
    exact hsep _ (e.symm r).2 _ (e.symm q).2 (fun h => hrq (e.symm.injective (Subtype.ext h)))
  have hmain := cosecantHilbertInequality α u hδ hδ2 hsepα
  set F : ι → ι → ℂ := fun i j =>
    x i * (starRingEnd ℂ) (x j) / (Real.sin (Real.pi * (t i - t j)) : ℂ) with hF
  have hdiag : ∀ i, F i i = 0 := fun i => by simp [hF]
  have hL : ∑ i ∈ s, ∑ j ∈ s.erase i, F i j
      = ∑ r, ∑ q ∈ Finset.univ.erase r,
          u r * (starRingEnd ℂ) (u q) / (Real.sin (Real.pi * (α r - α q)) : ℂ) := by
    have h1 : ∑ i ∈ s, ∑ j ∈ s.erase i, F i j = ∑ i ∈ s, ∑ j ∈ s, F i j :=
      Finset.sum_congr rfl fun i _ => Finset.sum_erase s (hdiag i)
    have h2 : ∀ r : Fin s.card, ∑ q ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u q) / (Real.sin (Real.pi * (α r - α q)) : ℂ)
        = ∑ q, F (e.symm r) (e.symm q) :=
      fun r => Finset.sum_erase _ (by simp [hu, hα])
    rw [h1, Finset.sum_congr rfl fun r _ => h2 r, hre]
    exact Finset.sum_congr rfl fun r _ => hre _
  have hR : ∑ r, ‖u r‖ ^ 2 = ∑ i ∈ s, ‖x i‖ ^ 2 := (hre (fun i => ‖x i‖ ^ 2)).symm
  rw [hL, ← hR]
  exact hmain

end HilbertCosecant

end RiemannHypothesis
