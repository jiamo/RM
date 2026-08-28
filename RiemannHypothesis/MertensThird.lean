/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.MertensSecond

/-!
# Mertens' third theorem, in bounded form

`∏_{p ≤ x} (1 − 1/p)⁻¹ ≍ log x`.  The sharp form of Mertens' third theorem says that the
ratio tends to `e^γ`; what is proved here is that the ratio is bounded above and below by
positive absolute constants, which is what follows from Mertens' second theorem
(`RiemannHypothesis.mertens_second`) without any further analytic input.

The bridge is the elementary two-sided estimate `t ≤ −log(1 − t) ≤ t + 2t²` for `0 < t ≤ 1/2`,
summed over the primes `p ≤ x` with `t = 1/p`; the quadratic error is absorbed by
`∑_{n ≥ 2} 1/n² ≤ 1` (`RiemannHypothesis.sum_inv_sq_le`).

## Main results

* `neg_log_one_sub_bounds` : `t ≤ −log(1 − t) ≤ t + 2t²` for `0 < t ≤ 1/2`.
* `mertens_third` : `|log ∏_{p ≤ x} (1 − 1/p)⁻¹ − log log x| ≤ 54` for `x ≥ 4`.
* `mertens_third_bounds` : `e^{−54} log x ≤ ∏_{p ≤ x} (1 − 1/p)⁻¹ ≤ e^{54} log x` for `x ≥ 4`.
-/

noncomputable section

open Filter Finset Real

namespace RiemannHypothesis

/-- The Mertens product `∏_{p ≤ x} (1 − 1/p)⁻¹`. -/
def primeProd (x : ℝ) : ℝ := ∏ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}, (1 - 1 / (p : ℝ))⁻¹

/-- `t ≤ −log(1 − t) ≤ t + 2t²` for `0 < t ≤ 1/2`. -/
lemma neg_log_one_sub_bounds {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    t ≤ -Real.log (1 - t) ∧ -Real.log (1 - t) ≤ t + 2 * t ^ 2 := by
  have h1 : (0 : ℝ) < 1 - t := by linarith
  refine ⟨?_, ?_⟩
  · have h := Real.log_le_sub_one_of_pos h1
    linarith
  · have h := Real.log_le_sub_one_of_pos (x := (1 - t)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have he : (1 - t)⁻¹ - 1 = t / (1 - t) := by field_simp; ring
    rw [he] at h
    have h2 : t / (1 - t) ≤ t + 2 * t ^ 2 := by
      rw [div_le_iff₀ h1]
      nlinarith [mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ 1 - 2 * t)]
    linarith

/-- Each factor of the Mertens product is positive. -/
private lemma one_sub_inv_prime_pos {p : ℕ} (hp : p.Prime) : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have : 1 / (p : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num) hp2
  linarith

/-- The logarithm of the Mertens product is `∑_{p ≤ x} −log(1 − 1/p)`. -/
lemma log_primeProd_eq (x : ℝ) :
    Real.log (primeProd x)
      = ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}, -Real.log (1 - 1 / (p : ℝ)) := by
  unfold primeProd
  rw [Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => Real.log_inv _
  · intro p hp
    exact inv_ne_zero (ne_of_gt (one_sub_inv_prime_pos (Finset.mem_filter.1 hp).2))

/-- The Mertens product is positive. -/
lemma primeProd_pos (x : ℝ) : 0 < primeProd x :=
  Finset.prod_pos fun _ hp => inv_pos.2 (one_sub_inv_prime_pos (Finset.mem_filter.1 hp).2)

/-- `0 ≤ log ∏_{p ≤ x} (1 − 1/p)⁻¹ − ∑_{p ≤ x} 1/p ≤ 2`. -/
lemma log_primeProd_sub_primeRecipSum_bounds (x : ℝ) :
    0 ≤ Real.log (primeProd x) - primeRecipSum x ∧
      Real.log (primeProd x) - primeRecipSum x ≤ 2 := by
  rw [log_primeProd_eq]
  unfold primeRecipSum
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime},
      0 ≤ -Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) ∧
        -Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) ≤ 2 * (1 / (p : ℝ)) ^ 2 := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.1 hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have ht0 : (0 : ℝ) < 1 / (p : ℝ) := by positivity
    have ht : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    obtain ⟨hlo, hhi⟩ := neg_log_one_sub_bounds ht0 ht
    exact ⟨by linarith, by linarith⟩
  refine ⟨Finset.sum_nonneg fun p hp => (hterm p hp).1, ?_⟩
  have hsub : {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime} ⊆ Finset.Icc 2 ⌊x⌋₊ := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact Finset.mem_Icc.2 ⟨hp.2.two_le, hp.1.2⟩
  calc ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime},
        (-Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))
      ≤ ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}, 2 * (1 / (p : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun p hp => (hterm p hp).2
    _ ≤ ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 2 * (1 / (n : ℝ)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ = 2 * ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / (n : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by rw [div_pow]; norm_num
    _ ≤ 2 * 1 := by linarith [sum_inv_sq_le ⌊x⌋₊]
    _ = 2 := by norm_num

/-- **Mertens' third theorem**, in bounded form:
`log ∏_{p ≤ x} (1 − 1/p)⁻¹ = log log x + O(1)`. -/
theorem mertens_third {x : ℝ} (hx : 4 ≤ x) :
    |Real.log (primeProd x) - Real.log (Real.log x)| ≤ 54 := by
  obtain ⟨h0, h2⟩ := log_primeProd_sub_primeRecipSum_bounds x
  have hm := mertens_second hx
  rw [abs_le] at hm ⊢
  constructor <;> linarith [hm.1, hm.2]

/-- **Mertens' third theorem**, in product form: the Mertens product is bounded above and
below by absolute constant multiples of `log x`.  The sharp constant `e^γ` is not proved. -/
theorem mertens_third_bounds {x : ℝ} (hx : 4 ≤ x) :
    Real.exp (-54) * Real.log x ≤ primeProd x ∧
      primeProd x ≤ Real.exp 54 * Real.log x := by
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hP : 0 < primeProd x := primeProd_pos x
  have h := mertens_third hx
  rw [abs_le] at h
  constructor
  · calc Real.exp (-54) * Real.log x
        = Real.exp (-54) * Real.exp (Real.log (Real.log x)) := by rw [Real.exp_log hlogx]
      _ = Real.exp (-54 + Real.log (Real.log x)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log (primeProd x)) := Real.exp_le_exp.2 (by linarith [h.1])
      _ = primeProd x := Real.exp_log hP
  · calc primeProd x = Real.exp (Real.log (primeProd x)) := (Real.exp_log hP).symm
      _ ≤ Real.exp (54 + Real.log (Real.log x)) := Real.exp_le_exp.2 (by linarith [h.2])
      _ = Real.exp 54 * Real.exp (Real.log (Real.log x)) := Real.exp_add _ _
      _ = Real.exp 54 * Real.log x := by rw [Real.exp_log hlogx]

end RiemannHypothesis
