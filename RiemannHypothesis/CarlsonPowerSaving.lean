/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.CarlsonDensity

/-!
# A power saving in the density theorem: `N(σ, T) = O(T^(1−c))`

`RiemannHypothesis/CarlsonDensity.lean` proves Carlson's density theorem in its qualitative
form `N(σ, T) = o(T)`: for every `ε > 0` the count is at most `ε T` for large `T`.  There the
mollifier length `y` is chosen from `ε` and then held fixed.  This file lets the length grow
with the height, `y ≈ T^γ`, and quantifies every step, which turns the `o(T)` into a genuine
power saving

`N(σ, T) ≤ C T^(1 − c)`

for constants `c > 0` and `C` depending only on `σ`.

## The quantitative chain

Everything is the Carlson argument again, with the `ε`'s replaced by explicit powers.

* `exists_sum_Ioc_divisorCount_sq_le_rpow` — the arithmetic input with a rate:
  `∑_{y < m ≤ M} d(m)² m^{−2σ} ≤ D y^{−(σ₀ − 1/2)}` for `σ ≥ σ₀ > 1/2`.  Splitting off
  `m^{−a}` with `a = σ₀ + 1/2 ∈ (1, 2σ₀)` leaves `m^{−(σ₀ − 1/2)} ≤ y^{−(σ₀ − 1/2)}`, and the
  remaining series converges.
* `exists_integral_normSq_mollified_partialSum_sub_one_le_rpow` — the Montgomery–Vaughan mean
  value theorem applied to `M_y P_K − 1` at the Carlson length `K = ⌈b^α⌉`, in the form
  `≤ C (b y^{−(σ₀−1/2)} + y b^(α(3/2−σ₀)))`, with `α (3/2 − σ₀) < 1`.
* `exists_integral_normSq_zeta_sub_partialSum_le_rpow` — the Euler–Maclaurin half, `≤ E b^β`
  with `β = 2α(1 − σ₀) < 1`.
* `exists_integral_normSq_zeta_mul_mollifier_sub_one_le_rpow` — the two halves combined:
  `∫_a^b ‖ζ M_y − 1‖² ≤ C (b y^{−(σ₀−1/2)} + b^(1−c))` whenever `y ≤ 4 b^γ`.
* `exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le_rpow` — the same on circles.

`RiemannHypothesis/CarlsonDensityPowerSaving.lean` feeds the last of these into the Jensen
counting inequality and deduces the power saving `N(σ, T) = O(T^(1−c))` itself.

The balancing that the companion file then performs is: with `y ≈ T^γ` and the parameter
`λ = T^{c'}` of the logarithmic majorant, `θ = σ₀ − 1/2`, the three terms of the counting
inequality are `λ T^{1−γθ}`, `T/λ` and `T/y`, all of them `T^{1−c'}`.

## Scope

The exponents are explicit in `θ = σ₀ − 1/2` — `1 − θ/2` for the Montgomery–Vaughan half,
`≤ 1 − θ` for the Euler–Maclaurin half, mollifier length `4 b^{θ/8}`, saving `3θ/8` — but the
constants in front are not.  Every bound here is a mean square; no zero is counted in this
file, and the Riemann hypothesis is neither proved nor disproved.
-/

noncomputable section

open Complex Real MeasureTheory Metric Filter Set Finset

namespace RiemannHypothesis

/-! ## The arithmetic input, with a rate -/

/-- **`∑_{y < m ≤ M} d(m)² m^{−2σ} ≤ D y^{−(σ₀ − 1/2)}`** for every `σ ≥ σ₀ > 1/2`: the tail of
the divisor-square series decays like a power of the mollifier length. -/
theorem sum_Icc_divisorCount_sq_rpow_le_tsum {a : ℝ} (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a)
      = ∑ n ∈ Finset.range M, (divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-a) := by
  refine Finset.sum_nbij' (i := fun m => m - 1) (j := fun n => n + 1) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    simp only [Finset.mem_range]
    omega
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    show m - 1 + 1 = m
    omega
  · intro n _
    show n + 1 - 1 = n
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    have e1 : m - 1 + 1 = m := by omega
    have e2 : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      have h : ((m - 1 + 1 : ℕ) : ℝ) = (m : ℝ) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) e1
      push_cast at h ⊢
      linarith
    rw [e1, e2]

theorem exists_sum_Ioc_divisorCount_sq_le_rpow {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ y M : ℕ, 1 ≤ y →
      ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
        ≤ D * (y : ℝ) ^ (-(σ₀ - 1 / 2)) := by
  classical
  set a : ℝ := σ₀ + 1 / 2 with hadef
  have ha1 : 1 < a := by rw [hadef]; linarith
  set g : ℕ → ℝ := fun n => (divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-a) with hg
  have hgsum : Summable g := summable_divisorCount_sq_rpow ha1
  have hgnn : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    have hpow : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-a) := Real.rpow_nonneg (by positivity) _
    rw [hg]; positivity
  set D : ℝ := (∑' n : ℕ, g n) + 1 with hD
  have hD0 : 0 < D := by
    have : 0 ≤ ∑' n : ℕ, g n := tsum_nonneg hgnn
    rw [hD]; linarith
  refine ⟨D, hD0, fun σ hσ y M hy => ?_⟩
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hθ0 : 0 < σ₀ - 1 / 2 := by linarith
  have hypow : (0 : ℝ) < (y : ℝ) ^ (-(σ₀ - 1 / 2)) := Real.rpow_pos_of_pos hy0 _
  -- termwise: peel off `m^{-a}` and bound the rest by `y^{-(σ₀ - 1/2)}`
  have hstep : ∀ m ∈ Finset.Ioc y M,
      (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
        ≤ ((divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a)) * (y : ℝ) ^ (-(σ₀ - 1 / 2)) := by
    intro m hm
    obtain ⟨hym, _⟩ := Finset.mem_Ioc.mp hm
    have hm1 : 1 ≤ m := by omega
    have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hym' : (y : ℝ) ≤ (m : ℝ) := by exact_mod_cast hym.le
    have e1 : (m : ℝ) ^ (-a) * (m : ℝ) ^ (-(σ₀ - 1 / 2)) = (m : ℝ) ^ (-2 * σ₀) := by
      rw [← Real.rpow_add hm0]
      congr 1
      rw [hadef]; ring
    have e2 : (m : ℝ) ^ (-2 * σ) ≤ (m : ℝ) ^ (-2 * σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hm1' (by linarith)
    have e3 : (m : ℝ) ^ (-(σ₀ - 1 / 2)) ≤ (y : ℝ) ^ (-(σ₀ - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos hy0 hym' (by linarith)
    have hd : (0 : ℝ) ≤ (divisorCount m : ℝ) ^ 2 := by positivity
    have hma : (0 : ℝ) < (m : ℝ) ^ (-a) := Real.rpow_pos_of_pos hm0 _
    calc (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
        ≤ (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₀) := by
          exact mul_le_mul_of_nonneg_left e2 hd
      _ = (divisorCount m : ℝ) ^ 2 * ((m : ℝ) ^ (-a) * (m : ℝ) ^ (-(σ₀ - 1 / 2))) := by rw [e1]
      _ ≤ (divisorCount m : ℝ) ^ 2 * ((m : ℝ) ^ (-a) * (y : ℝ) ^ (-(σ₀ - 1 / 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ hd
          exact mul_le_mul_of_nonneg_left e3 hma.le
      _ = ((divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a)) * (y : ℝ) ^ (-(σ₀ - 1 / 2)) := by ring
  -- the weights sum to at most `D`
  have hweights : ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a) ≤ D := by
    have hsub : ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a)
        ≤ ∑ m ∈ Finset.Icc 1 M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        simp only [Finset.mem_Ioc] at hm
        simp only [Finset.mem_Icc]
        omega
      · intro m _ _
        have hp : (0 : ℝ) ≤ (m : ℝ) ^ (-a) := Real.rpow_nonneg (by positivity) _
        positivity
    have hre := sum_Icc_divisorCount_sq_rpow_le_tsum (a := a) M
    have hle : ∑ n ∈ Finset.range M, g n ≤ ∑' n : ℕ, g n :=
      Summable.sum_le_tsum _ (fun i _ => hgnn i) hgsum
    rw [hre] at hsub
    rw [hD]
    have : ∑ n ∈ Finset.range M, (divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-a)
        = ∑ n ∈ Finset.range M, g n := rfl
    rw [this] at hsub
    linarith
  calc ∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
      ≤ ∑ m ∈ Finset.Ioc y M,
          ((divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a)) * (y : ℝ) ^ (-(σ₀ - 1 / 2)) :=
        Finset.sum_le_sum hstep
    _ = (∑ m ∈ Finset.Ioc y M, (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-a))
          * (y : ℝ) ^ (-(σ₀ - 1 / 2)) := by rw [← Finset.sum_mul]
    _ ≤ D * (y : ℝ) ^ (-(σ₀ - 1 / 2)) := mul_le_mul_of_nonneg_right hweights hypow.le

/-! ## The mean square of the mollified partial sum, with a rate -/

/-- **The Montgomery–Vaughan mean value theorem at the Carlson length, quantitatively.**
The exponent is explicit: `γ = α (3/2 − σ₀) = 1 − (σ₀ − 1/2)/2`, so the saving `1 − γ` is
half of `θ = σ₀ − 1/2`. -/
theorem exists_integral_normSq_mollified_partialSum_sub_one_le_rpow {σ₀ : ℝ}
    (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ γ < 1 ∧ γ ≤ 1 - (σ₀ - 1 / 2) / 2 ∧
      ∀ σ : ℝ, σ₀ ≤ σ → ∀ (y : ℕ) (b : ℝ), 1 ≤ y → 6 ≤ b →
      (y : ℝ) ≤ b →
        (∫ t in (0 : ℝ)..b, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
            dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
          ≤ C * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2)) + (y : ℝ) * b ^ γ) := by
  classical
  obtain ⟨S, hS0, hSbd⟩ := exists_sum_divisorCount_sq_mul_le h0 h1
  obtain ⟨D, hD0, hDbd⟩ := exists_sum_Ioc_divisorCount_sq_le_rpow h0
  set e : ℝ := 3 / 2 - σ₀ with hedef
  have he0 : 0 < e := by rw [hedef]; linarith
  have he1 : e ≤ 1 := by rw [hedef]; linarith
  set α : ℝ := carlsonExponent σ₀ with hαdef
  have hα1 : 1 < α := one_lt_carlsonExponent h0 h1
  set γ : ℝ := α * e with hγdef
  have hγ1 : γ < 1 := by
    rw [hγdef, hαdef, hedef]
    exact carlsonExponent_mul_lt_one h0 h1
  have hγ0 : 0 < γ := by rw [hγdef]; nlinarith only [hα1, he0]
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) e
  have hγexp : γ = 1 - (σ₀ - 1 / 2) / 2 := by
    have hne : (3 / 2 - σ₀) ≠ 0 := by intro h; linarith
    have hne2 : (3 - 2 * σ₀) ≠ 0 := by intro h; linarith
    rw [hγdef, hαdef, hedef, carlsonExponent]
    field_simp
    ring
  refine ⟨58 * (D + S * (2 : ℝ) ^ e), γ, by positivity, hγ0, hγ1, hγexp.le, ?_⟩
  intro σ hσ y b hy1 hb6 hby
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hKceil : truncationLength σ₀ b = ⌈b ^ α⌉₊ := by rw [truncationLength, hαdef]
  set K : ℕ := truncationLength σ₀ b with hKdef
  clear_value K
  have hbα0 : (0 : ℝ) < b ^ α := Real.rpow_pos_of_pos hb0 α
  have hbb : b ≤ b ^ α := by
    have h := Real.rpow_le_rpow_of_exponent_le hb1 hα1.le
    rwa [Real.rpow_one] at h
  have hbα1 : (1 : ℝ) ≤ b ^ α := le_trans hb1 hbb
  have hKge : b ^ α ≤ (K : ℝ) := by rw [hKceil]; exact Nat.le_ceil _
  have hKle : (K : ℝ) ≤ b ^ α + 1 := by
    rw [hKceil]; exact le_of_lt (Nat.ceil_lt_add_one hbα0.le)
  have hyKR : (y : ℝ) ≤ (K : ℝ) := le_trans (le_trans hby hbb) hKge
  have hyK : y ≤ K := by exact_mod_cast hyKR
  have hcongr : (∫ t in (0 : ℝ)..b, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        dirichletPoly (fun _ => 1) K ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      = ∫ t in (0 : ℝ)..b, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [dirichletPoly_one_eq_sum]
  rw [hcongr]
  refine (integral_normSq_mollified_partialSum_sub_one_le_mv hy1 hyK σ hb6).trans ?_
  have hsplit : ∑ m ∈ Finset.Ioc y (y * K),
        (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (b + m)
      = b * (∑ m ∈ Finset.Ioc y (y * K), (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ))
        + ∑ m ∈ Finset.Ioc y (y * K),
            (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hsplit]
  -- the tail of the divisor sum, with its rate
  have hT1 : ∑ m ∈ Finset.Ioc y (y * K), (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ)
      ≤ D * (y : ℝ) ^ (-(σ₀ - 1 / 2)) := hDbd σ hσ y (y * K) hy1
  -- the weighted divisor sum
  have hT2 : ∑ m ∈ Finset.Ioc y (y * K),
        (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ)
      ≤ S * (((y * K : ℕ) : ℝ)) ^ e := by
    have s1 : ∑ m ∈ Finset.Ioc y (y * K),
          (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ)
        ≤ ∑ m ∈ Finset.Icc 1 (y * K),
          (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        simp only [Finset.mem_Ioc] at hm
        simp only [Finset.mem_Icc]
        omega
      · intro m _ _
        have hp : (0 : ℝ) ≤ (m : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (by positivity) _
        positivity
    exact s1.trans (hSbd σ hσ (y * K))
  have hyKcast : (((y * K : ℕ)) : ℝ) = (y : ℝ) * (K : ℝ) := by push_cast; ring
  have hyKb : (y : ℝ) * (K : ℝ) ≤ (2 * (y : ℝ)) * b ^ α := by
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := by linarith
    have q1 : (y : ℝ) * (K : ℝ) ≤ (y : ℝ) * (b ^ α + 1) := mul_le_mul_of_nonneg_left hKle hy0
    have q2 : (y : ℝ) * 1 ≤ (y : ℝ) * b ^ α := mul_le_mul_of_nonneg_left hbα1 hy0
    nlinarith only [q1, q2]
  have hye : (y : ℝ) ^ e ≤ (y : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hyR he1
    rwa [Real.rpow_one] at h
  have hpowyK : (((y * K : ℕ)) : ℝ) ^ e ≤ (2 : ℝ) ^ e * (y : ℝ) * b ^ γ := by
    rw [hyKcast]
    have hbase : (0 : ℝ) < 2 * (y : ℝ) := by linarith
    calc ((y : ℝ) * (K : ℝ)) ^ e ≤ ((2 * (y : ℝ)) * b ^ α) ^ e :=
          Real.rpow_le_rpow (by positivity) hyKb he0.le
      _ = (2 * (y : ℝ)) ^ e * (b ^ α) ^ e := Real.mul_rpow hbase.le hbα0.le
      _ = ((2 : ℝ) ^ e * (y : ℝ) ^ e) * b ^ (α * e) := by
          rw [← Real.rpow_mul hb0.le, Real.mul_rpow (by norm_num) (by linarith)]
      _ ≤ ((2 : ℝ) ^ e * (y : ℝ)) * b ^ γ := by
          rw [hγdef]
          gcongr
      _ = (2 : ℝ) ^ e * (y : ℝ) * b ^ γ := by ring
  have hstep2 : ∑ m ∈ Finset.Ioc y (y * K),
        (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ) * (m : ℝ)
      ≤ S * ((2 : ℝ) ^ e * (y : ℝ) * b ^ γ) :=
    hT2.trans (mul_le_mul_of_nonneg_left hpowyK hS0.le)
  have hstep1 : b * (∑ m ∈ Finset.Ioc y (y * K),
        (divisorCount m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ))
      ≤ b * (D * (y : ℝ) ^ (-(σ₀ - 1 / 2))) := mul_le_mul_of_nonneg_left hT1 hb0.le
  have hyneg : (0 : ℝ) ≤ (y : ℝ) ^ (-(σ₀ - 1 / 2)) :=
    Real.rpow_nonneg (by linarith) _
  have hbγ : (0 : ℝ) ≤ b ^ γ := Real.rpow_nonneg hb0.le _
  have hu : (0 : ℝ) ≤ b * (y : ℝ) ^ (-(σ₀ - 1 / 2)) := by positivity
  have hv : (0 : ℝ) ≤ (y : ℝ) * b ^ γ := by positivity
  have hDv : (0 : ℝ) ≤ D * ((y : ℝ) * b ^ γ) := mul_nonneg hD0.le hv
  have hSu : (0 : ℝ) ≤ (S * (2 : ℝ) ^ e) * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2))) :=
    mul_nonneg (mul_nonneg hS0.le h2e.le) hu
  have hfinal : 58 * (b * (D * (y : ℝ) ^ (-(σ₀ - 1 / 2))) + S * ((2 : ℝ) ^ e * (y : ℝ) * b ^ γ))
      ≤ 58 * (D + S * (2 : ℝ) ^ e) * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2)) + (y : ℝ) * b ^ γ) := by
    nlinarith only [hDv, hSu]
  linarith only [hstep1, hstep2, hfinal]

/-! ## The Euler–Maclaurin half, with a rate -/

set_option maxHeartbeats 1000000 in
-- the proof carries a large context (Euler–Maclaurin constants, three exponent thresholds)
/-- **The mean square of `ζ − P_K` at the Carlson length is `O(b^β)` with `β < 1`.**
The exponent is explicit enough for the bookkeeping downstream: `β = 2α(1 − σ₀) ≤ 1 − θ` with
`θ = σ₀ − 1/2`. -/
theorem exists_integral_normSq_zeta_sub_partialSum_le_rpow {σ₀ : ℝ} (h0 : 1 / 2 < σ₀)
    (h1 : σ₀ < 1) :
    ∃ E β : ℝ, 0 < E ∧ 0 < β ∧ β < 1 ∧ β ≤ 1 - (σ₀ - 1 / 2) ∧ ∃ b₀ : ℝ, 6 ≤ b₀ ∧
      ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 6 → ∀ a b : ℝ, 1 ≤ a → a ≤ b → b₀ ≤ b →
        (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
          ≤ E * b ^ β := by
  have hσ₀₀ : (0 : ℝ) < σ₀ := by linarith
  set α := carlsonExponent σ₀ with hαdef
  have hα1 : 1 < α := one_lt_carlsonExponent h0 h1
  have hα10 : (0 : ℝ) < α - 1 := by linarith
  have hαmul : α * (3 / 2 - σ₀) < 1 := carlsonExponent_mul_lt_one h0 h1
  set β := 2 * α * (1 - σ₀) with hβdef
  have hβ1 : β < 1 := by rw [hβdef]; nlinarith
  have hβ0 : 0 < β := by rw [hβdef]; nlinarith
  have hβle : β ≤ 1 - (σ₀ - 1 / 2) := by
    have hu : (0 : ℝ) < 3 / 2 - σ₀ := by linarith
    have hv : (3 / 2 - σ₀) * (1 / (3 / 2 - σ₀)) = 1 := mul_one_div_cancel (ne_of_gt hu)
    have hvpos : (0 : ℝ) < 1 / (3 / 2 - σ₀) := by positivity
    rw [hβdef, hαdef, carlsonExponent]
    nlinarith [hv, hu, hvpos]
  set m : ℕ := max 1 ⌈(α * (1 - σ₀) + 1) / (α - 1)⌉₊ with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmbig : α * (1 - σ₀) + 1 ≤ (α - 1) * m := by
    have hceil : (α * (1 - σ₀) + 1) / (α - 1) ≤ (⌈(α * (1 - σ₀) + 1) / (α - 1)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hmm : ((⌈(α * (1 - σ₀) + 1) / (α - 1)⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast le_max_right 1 ⌈(α * (1 - σ₀) + 1) / (α - 1)⌉₊
    have := (div_le_iff₀ hα10).mp (hceil.trans hmm)
    linarith
  clear_value β m
  obtain ⟨C, hC0, hCbd⟩ :=
    exists_norm_riemannZeta_sub_dirichletPoly_le_em_uniform m hm1 hσ₀₀
  set E : ℝ := C * (1 + (2 + (m : ℝ)) ^ m) with hEdef
  have hE0 : 0 < E := by
    have : (0 : ℝ) < (2 + (m : ℝ)) ^ m := by positivity
    rw [hEdef]; nlinarith
  clear_value E
  refine ⟨18 + 2 * E ^ 2, β, by positivity, hβ0, hβ1, hβle,
    max 6 ((2 : ℝ) ^ (1 / (α - 1))), le_max_left _ _, ?_⟩
  intro σ hσ hσ6 a b ha hab hb
  have hb6 : (6 : ℝ) ≤ b := (le_max_left _ _).trans hb
  have hbpow2 : (2 : ℝ) ^ (1 / (α - 1)) ≤ b := (le_max_right _ _).trans hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  set N : ℕ := truncationLength σ₀ b with hNdef
  have hKceil : N = ⌈b ^ α⌉₊ := by rw [hNdef, truncationLength, hαdef]
  clear_value N α
  have hbα0 : (0 : ℝ) < b ^ α := Real.rpow_pos_of_pos hb0 α
  have hbb : b ≤ b ^ α := by
    have h := Real.rpow_le_rpow_of_exponent_le hb1 hα1.le
    rwa [Real.rpow_one] at h
  have hbα1 : (1 : ℝ) ≤ b ^ α := le_trans hb1 hbb
  have hsplit : b ^ α = b ^ (α - 1) * b := by
    conv_lhs => rw [show α = (α - 1) + 1 by ring]
    rw [Real.rpow_add hb0, Real.rpow_one]
  have hbpow : (2 : ℝ) ≤ b ^ (α - 1) := by
    have h := Real.rpow_le_rpow (by positivity) hbpow2 hα10.le
    rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ (ne_of_gt hα10),
      Real.rpow_one] at h
  have h2b : 2 * b ≤ b ^ α := by
    rw [hsplit]
    nlinarith only [hbpow, hb0]
  have hKge : b ^ α ≤ (N : ℝ) := by rw [hKceil]; exact Nat.le_ceil _
  have hKle : (N : ℝ) ≤ b ^ α + 1 := by
    rw [hKceil]; exact le_of_lt (Nat.ceil_lt_add_one hbα0.le)
  have hK1R : (1 : ℝ) ≤ (N : ℝ) := le_trans hbα1 hKge
  have hK1 : 1 ≤ N := by exact_mod_cast hK1R
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have h6bm : (0 : ℝ) ≤ 6 + b + (m : ℝ) := by linarith
  set A : ℝ := ((N : ℝ) + 1) ^ (1 - σ₀) with hAdef
  set B : ℝ := C * ((N : ℝ) ^ (-σ₀)
    + (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))) with hBdef
  have hA0 : 0 ≤ A := Real.rpow_nonneg (by linarith) _
  have hB0 : 0 ≤ B := by
    have e1 : (0 : ℝ) ≤ (N : ℝ) ^ (-σ₀) := Real.rpow_nonneg hN0.le _
    have e2 : (0 : ℝ) ≤ (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ)) :=
      mul_nonneg (pow_nonneg h6bm m) (Real.rpow_nonneg hN0.le _)
    rw [hBdef]; nlinarith
  clear_value A B
  -- the pointwise bound
  have hpt : ∀ t ∈ Set.Icc a b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ 2 * A ^ 2 * (1 / t ^ 2) + 2 * B ^ 2 := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans ha ht.1
    have htb : t ≤ b := ht.2
    have htabs : |t| = t := abs_of_nonneg (by linarith)
    have hNt : σ + |t| ≤ (N : ℝ) := by rw [htabs]; linarith
    have hem := hCbd σ hσ N hK1 t (by rw [htabs]; linarith) hNt
    have hnorm : t ≤ ‖((σ : ℂ) + (t : ℂ) * I) - 1‖ := by
      have h := Complex.abs_im_le_norm (((σ : ℂ) + (t : ℂ) * I) - 1)
      have him : (((σ : ℂ) + (t : ℂ) * I) - 1).im = t := by simp
      rw [him, htabs] at h
      exact h
    have hterm1 : ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖ ≤ A / t := by
      have hnum : ((N : ℝ) + 1) ^ (1 - σ) ≤ A := by
        rw [hAdef]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hnum0 : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ (1 - σ) := Real.rpow_nonneg (by linarith) _
      have hstep : ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
          ≤ ((N : ℝ) + 1) ^ (1 - σ) / t :=
        div_le_div_of_nonneg_left hnum0 (by linarith) hnorm
      exact hstep.trans (by gcongr)
    have hterm2 : C * ((N : ℝ) ^ (-σ) + (σ + |t| + (m : ℝ)) ^ m
        * (N : ℝ) ^ (1 - σ - (m : ℝ))) ≤ B := by
      have e1 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ₀) :=
        Real.rpow_le_rpow_of_exponent_le hK1R (by linarith)
      have e2 : (σ + |t| + (m : ℝ)) ^ m ≤ (6 + b + (m : ℝ)) ^ m :=
        pow_le_pow_left₀ (by rw [htabs]; linarith) (by rw [htabs]; linarith) m
      have e3 : (N : ℝ) ^ (1 - σ - (m : ℝ)) ≤ (N : ℝ) ^ (1 - σ₀ - (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hK1R (by linarith)
      have e4 := mul_le_mul e2 e3 (Real.rpow_nonneg hN0.le _)
        (pow_nonneg h6bm m)
      rw [hBdef]
      exact mul_le_mul_of_nonneg_left (add_le_add e1 e4) hC0.le
    have hle : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A / t + B :=
      hem.trans (add_le_add hterm1 hterm2)
    have ht0 : (0 : ℝ) < t := by linarith
    have hdiv : (A / t) ^ 2 = A ^ 2 * (1 / t ^ 2) := by field_simp
    have hexp2 : (A / t + B) ^ 2 ≤ 2 * (A / t) ^ 2 + 2 * B ^ 2 := by
      nlinarith [sq_nonneg (A / t - B)]
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ (A / t + B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ ≤ 2 * (A / t) ^ 2 + 2 * B ^ 2 := hexp2
      _ = 2 * A ^ 2 * (1 / t ^ 2) + 2 * B ^ 2 := by rw [hdiv]; ring
  -- integrate
  have hcontLHS : ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact (continuousOn_normSq_riemannZeta_sub_dirichletPoly_line σ N).mono
      fun t ht => le_trans ha ht.1
  have hiL : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume a b :=
    hcontLHS.intervalIntegrable
  have hi1 : IntervalIntegrable (fun t : ℝ => 2 * A ^ 2 * (1 / t ^ 2)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine continuousOn_const.mul (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans ha ht.1
    positivity
  have hi2 : IntervalIntegrable (fun _ : ℝ => 2 * B ^ 2) volume a b := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hiL (hi1.add hi2) hpt
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul]
  set X : ℝ := ∫ t in a..b, 1 / t ^ 2 with hXdef
  have hX1 : X ≤ 1 := integral_inv_sq_le_one ha hab
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    refine intervalIntegral.integral_nonneg hab fun t ht => ?_
    have ht1 : (1 : ℝ) ≤ t := le_trans ha ht.1
    positivity
  clear_value X
  -- the two constants
  have h3 : (3 : ℝ) ^ (1 - σ₀) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith : (1 - σ₀) ≤ 1)
    rwa [Real.rpow_one] at h
  have hNA : (N : ℝ) + 1 ≤ 3 * b ^ α := by linarith
  have hAle : A ≤ 3 * b ^ (α * (1 - σ₀)) := by
    calc A = ((N : ℝ) + 1) ^ (1 - σ₀) := hAdef
      _ ≤ (3 * b ^ α) ^ (1 - σ₀) :=
          Real.rpow_le_rpow (by linarith) hNA (by linarith)
      _ = (3 : ℝ) ^ (1 - σ₀) * (b ^ α) ^ (1 - σ₀) := Real.mul_rpow (by norm_num) hbα0.le
      _ = (3 : ℝ) ^ (1 - σ₀) * b ^ (α * (1 - σ₀)) := by rw [← Real.rpow_mul hb0.le]
      _ ≤ 3 * b ^ (α * (1 - σ₀)) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hb0.le _)
  have hA2 : A ^ 2 ≤ 9 * b ^ β := by
    have hpow : (b ^ (α * (1 - σ₀))) ^ 2 = b ^ β := by
      rw [← Real.rpow_natCast (b ^ (α * (1 - σ₀))) 2, ← Real.rpow_mul hb0.le, hβdef]
      congr 1
      push_cast
      ring
    calc A ^ 2 ≤ (3 * b ^ (α * (1 - σ₀))) ^ 2 := pow_le_pow_left₀ hA0 hAle 2
      _ = 9 * (b ^ (α * (1 - σ₀))) ^ 2 := by ring
      _ = 9 * b ^ β := by rw [hpow]
  have hBle : B ≤ E * b ^ (-σ₀) := by
    have ebα : ((b : ℝ) ^ α) ^ (-σ₀) ≤ b ^ (-σ₀) := by
      rw [← Real.rpow_mul hb0.le]
      exact Real.rpow_le_rpow_of_exponent_le hb1 (by nlinarith only [hα1, hσ₀₀])
    have e1 : (N : ℝ) ^ (-σ₀) ≤ b ^ (-σ₀) :=
      (Real.rpow_le_rpow_of_nonpos hbα0 hKge (by linarith)).trans ebα
    have e2 : (6 + b + (m : ℝ)) ^ m ≤ (2 + (m : ℝ)) ^ m * b ^ (m : ℝ) := by
      have hle : 6 + b + (m : ℝ) ≤ (2 + (m : ℝ)) * b := by
        nlinarith only [mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ))
          (by linarith only [hb1] : (0 : ℝ) ≤ b - 1), hb6]
      calc (6 + b + (m : ℝ)) ^ m ≤ ((2 + (m : ℝ)) * b) ^ m := pow_le_pow_left₀ h6bm hle m
        _ = (2 + (m : ℝ)) ^ m * b ^ m := mul_pow _ _ _
        _ = (2 + (m : ℝ)) ^ m * b ^ (m : ℝ) := by rw [Real.rpow_natCast]
    have e3 : (N : ℝ) ^ (1 - σ₀ - (m : ℝ)) ≤ b ^ (α * (1 - σ₀ - (m : ℝ))) := by
      have h := Real.rpow_le_rpow_of_nonpos hbα0 hKge (by linarith : (1 : ℝ) - σ₀ - (m : ℝ) ≤ 0)
      rwa [← Real.rpow_mul hb0.le] at h
    have hexp : (m : ℝ) + α * (1 - σ₀ - (m : ℝ)) ≤ -σ₀ := by
      nlinarith only [hmbig, h1, h0]
    have e4 : b ^ (m : ℝ) * b ^ (α * (1 - σ₀ - (m : ℝ))) ≤ b ^ (-σ₀) := by
      rw [← Real.rpow_add hb0]
      exact Real.rpow_le_rpow_of_exponent_le hb1 hexp
    have hprod : (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))
        ≤ (2 + (m : ℝ)) ^ m * b ^ (-σ₀) := by
      calc (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))
          ≤ ((2 + (m : ℝ)) ^ m * b ^ (m : ℝ)) * b ^ (α * (1 - σ₀ - (m : ℝ))) :=
            mul_le_mul e2 e3 (Real.rpow_nonneg hN0.le _) (by positivity)
        _ = (2 + (m : ℝ)) ^ m * (b ^ (m : ℝ) * b ^ (α * (1 - σ₀ - (m : ℝ)))) := by ring
        _ ≤ (2 + (m : ℝ)) ^ m * b ^ (-σ₀) := mul_le_mul_of_nonneg_left e4 (by positivity)
    have hsum : (N : ℝ) ^ (-σ₀)
        + (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))
        ≤ (1 + (2 + (m : ℝ)) ^ m) * b ^ (-σ₀) := by nlinarith only [e1, hprod]
    calc B = C * ((N : ℝ) ^ (-σ₀)
            + (6 + b + (m : ℝ)) ^ m * (N : ℝ) ^ (1 - σ₀ - (m : ℝ))) := hBdef
      _ ≤ C * ((1 + (2 + (m : ℝ)) ^ m) * b ^ (-σ₀)) :=
          mul_le_mul_of_nonneg_left hsum hC0.le
      _ = E * b ^ (-σ₀) := by rw [hEdef]; ring
  have hB2 : B ^ 2 ≤ E ^ 2 / b := by
    have hsq : (E * b ^ (-σ₀)) ^ 2 = E ^ 2 * b ^ (-(2 * σ₀)) := by
      rw [mul_pow, ← Real.rpow_natCast (b ^ (-σ₀)) 2, ← Real.rpow_mul hb0.le]
      congr 2
      push_cast
      ring
    have h3' : b ^ (-(2 * σ₀)) ≤ b ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    have h4' : b ^ (-(1 : ℝ)) = 1 / b := by
      rw [Real.rpow_neg hb0.le, Real.rpow_one, one_div]
    calc B ^ 2 ≤ (E * b ^ (-σ₀)) ^ 2 := pow_le_pow_left₀ hB0 hBle 2
      _ = E ^ 2 * b ^ (-(2 * σ₀)) := hsq
      _ ≤ E ^ 2 * (1 / b) := by rw [← h4']; exact mul_le_mul_of_nonneg_left h3' (by positivity)
      _ = E ^ 2 / b := by ring
  have hAX : 2 * A ^ 2 * X ≤ 18 * b ^ β := by
    have hA2nn : (0 : ℝ) ≤ 2 * A ^ 2 := by positivity
    calc 2 * A ^ 2 * X ≤ 2 * A ^ 2 * 1 := mul_le_mul_of_nonneg_left hX1 hA2nn
      _ = 2 * A ^ 2 := by ring
      _ ≤ 18 * b ^ β := by linarith only [hA2]
  have hBb : (b - a) * (2 * B ^ 2) ≤ 2 * E ^ 2 := by
    have hstep1 : (b - a) * (2 * B ^ 2) ≤ b * (2 * B ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith only [ha] : b - a ≤ b) (by positivity)
    have hstep2 : b * (2 * B ^ 2) ≤ b * (2 * (E ^ 2 / b)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hB2]) hb0.le
    have hstep3 : b * (2 * (E ^ 2 / b)) = 2 * E ^ 2 := by
      field_simp
    linarith only [hstep1, hstep2, hstep3]
  have hbβ1 : (1 : ℝ) ≤ b ^ β := Real.one_le_rpow hb1 hβ0.le
  have hE2 : 2 * E ^ 2 ≤ 2 * E ^ 2 * b ^ β := by nlinarith only [hbβ1, hE0]
  linarith only [hAX, hBb, hE2]

/-! ## The mollified mean square with a growing mollifier -/

/-- A convenient smallness fact: for `b ≥ 16` and an exponent `g ≤ 1/4` one has
`4 b^g ≤ b`.  This is what lets a mollifier of length `y ≤ 4 b^γ` still satisfy `y ≤ b`. -/
theorem four_mul_rpow_le_self {b g : ℝ} (hb : 16 ≤ b) (hg : g ≤ 1 / 4) :
    4 * b ^ g ≤ b := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have h1 : b ^ g ≤ b ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 hg
  have hu0 : (0 : ℝ) ≤ b ^ (1 / 4 : ℝ) := Real.rpow_nonneg hb0.le _
  have hu4 : (b ^ (1 / 4 : ℝ)) ^ 4 = b := by
    rw [← Real.rpow_natCast (b ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hb0.le]
    norm_num
  have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hu2 : (2 : ℝ) ≤ b ^ (1 / 4 : ℝ) := by
    rw [← h16]
    exact Real.rpow_le_rpow (by norm_num) hb (by norm_num)
  have hcube : (8 : ℝ) ≤ (b ^ (1 / 4 : ℝ)) ^ 3 :=
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (b ^ (1 / 4 : ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) hu2 3
  have hupos : (0 : ℝ) < b ^ (1 / 4 : ℝ) := by linarith
  have h4u : 4 * b ^ (1 / 4 : ℝ) ≤ (b ^ (1 / 4 : ℝ)) ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hcube hupos.le
    nlinarith only [hmul, hupos]
  linarith only [hu4, h1, h4u]

set_option maxHeartbeats 1000000 in
-- the proof carries the two halves of the Carlson decomposition and their exponent bookkeeping
/-- **The mean square of `ζ M_y − 1` for a mollifier length that may grow with the height.**
The first term is the arithmetic saving `y^{−(σ₀−1/2)}`, the second a fixed power saving.
Both exponents are explicit in `θ = σ₀ − 1/2`: the mollifier may have length up to `4 b^{θ/8}`
and the power saving is at least `3θ/8`. -/
theorem exists_integral_normSq_zeta_mul_mollifier_sub_one_le_rpow {σ₀ : ℝ} (h0 : 1 / 2 < σ₀)
    (h1 : σ₀ < 1) :
    ∃ C c γ : ℝ, 0 < C ∧ 0 < c ∧ c < 1 ∧ 0 < γ ∧ 3 * (σ₀ - 1 / 2) / 8 ≤ c ∧
      γ = (σ₀ - 1 / 2) / 8 ∧ ∃ b₀ : ℝ, 6 ≤ b₀ ∧
      ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 6 → ∀ y : ℕ, 1 ≤ y → ∀ a b : ℝ, 1 ≤ a → a ≤ b → b₀ ≤ b →
        (y : ℝ) ≤ 4 * b ^ γ →
        (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
            Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
          ≤ C * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2)) + b ^ (1 - c)) := by
  obtain ⟨C₁, γ₁, hC₁0, hγ₁0, hγ₁1, hγ₁le, hMV⟩ :=
    exists_integral_normSq_mollified_partialSum_sub_one_le_rpow h0 h1
  obtain ⟨E, β, hE0, hβ0, hβ1, hβle, b₀E, hb₀E6, hEM⟩ :=
    exists_integral_normSq_zeta_sub_partialSum_le_rpow h0 h1
  -- the mollifier exponent, chosen explicitly in terms of `θ = σ₀ − 1/2`
  set γ : ℝ := (σ₀ - 1 / 2) / 8 with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; linarith
  have hγ14 : γ ≤ 1 / 4 := by rw [hγdef]; linarith
  have hsum1 : γ + γ₁ ≤ 1 - 3 * (σ₀ - 1 / 2) / 8 := by rw [hγdef]; linarith
  have hsum2 : 2 * γ + β ≤ 1 - 3 * (σ₀ - 1 / 2) / 4 := by rw [hγdef]; linarith
  set e : ℝ := max (γ + γ₁) (2 * γ + β) with hedef
  have hele : e ≤ 1 - 3 * (σ₀ - 1 / 2) / 8 := by
    rw [hedef]
    exact max_le hsum1 (by linarith)
  have he1 : e < 1 := by linarith
  have he0 : 0 < e := lt_of_lt_of_le (by linarith : (0 : ℝ) < γ + γ₁) (le_max_left _ _)
  refine ⟨10 * C₁ + 32 * E, 1 - e, γ, by positivity, by linarith, by linarith, hγ0,
    by linarith, hγdef,
    max b₀E 16, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro σ hσ hσ6 y hy1 a b ha hab hb hyb
  have hb16 : (16 : ℝ) ≤ b := le_trans (le_max_right _ _) hb
  have hbE : b₀E ≤ b := le_trans (le_max_left _ _) hb
  have hb6 : (6 : ℝ) ≤ b := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hybb : (y : ℝ) ≤ b := le_trans hyb (four_mul_rpow_le_self hb16 hγ14)
  have hσ0 : (0 : ℝ) < σ := by linarith
  -- the continuity facts
  have hcM : Continuous (fun t : ℝ => Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I)) :=
    continuous_mollifier_line y σ
  have hcF : Continuous (fun t : ℝ => ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) :=
    (((hcM.mul (continuous_dirichletPoly_line (truncationLength σ₀ b))).sub
      continuous_const).norm).pow 2
  have hcL : ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) (Set.Ici 1) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have h' := congrArg Complex.im h
      simp at h'
      linarith
    have hline : ContinuousAt (fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) t := by fun_prop
    have hz : ContinuousAt (fun u : ℝ => riemannZeta ((σ : ℂ) + (u : ℂ) * I)) t :=
      ContinuousAt.comp (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (g := riemannZeta)
        ((differentiableAt_riemannZeta hne).continuousAt) hline
    exact ((((hz.mul hcM.continuousAt).sub continuousAt_const).norm).pow 2).continuousWithinAt
  have hcG : ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (Set.Ici 1) :=
    continuousOn_normSq_riemannZeta_sub_dirichletPoly_line σ (truncationLength σ₀ b)
  -- the pointwise bound
  have hpt : ∀ t ∈ Set.Icc a b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2
      ≤ 2 * ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2
        + 2 * (y : ℝ) ^ 2 * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t _
    have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
    have hM : ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I)‖ ≤ (y : ℝ) :=
      norm_mollifier_le_length y (by rw [hre]; linarith)
    have hid : riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1
        = (Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
            dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1)
          + Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
            (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
              - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)) := by
      ring
    rw [hid]
    set U : ℝ := ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ with hUdef
    set V : ℝ := ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ with hVdef
    have hprod : ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
        (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I))‖
        ≤ (y : ℝ) * V := by
      rw [norm_mul, hVdef]
      exact mul_le_mul_of_nonneg_right hM (norm_nonneg _)
    have hsum : ‖(Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1)
        + Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I))‖
        ≤ U + (y : ℝ) * V :=
      (norm_add_le (Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1)
        (Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) (truncationLength σ₀ b)
              ((σ : ℂ) + (t : ℂ) * I)))).trans (add_le_add (le_refl U) hprod)
    have hU0 : 0 ≤ U := norm_nonneg _
    have hV0 : 0 ≤ V := norm_nonneg _
    calc ‖(Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1)
        + Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (riemannZeta ((σ : ℂ) + (t : ℂ) * I)
            - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2
        ≤ (U + (y : ℝ) * V) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsum 2
      _ ≤ 2 * U ^ 2 + 2 * (y : ℝ) ^ 2 * V ^ 2 := by
          nlinarith only [sq_nonneg (U - (y : ℝ) * V)]
  -- integrability
  have hiL : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hcL.mono fun t ht => le_trans ha ht.1
  have hiF : IntervalIntegrable (fun t : ℝ => 2 * ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      volume a b := (hcF.const_smul (2 : ℝ)).intervalIntegrable a b
  have hiG : IntervalIntegrable (fun t : ℝ => 2 * (y : ℝ) ^ 2 *
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.mul (hcG.mono fun t ht => le_trans ha ht.1)
  have hmain := intervalIntegral.integral_mono_on hab hiL (hiF.add hiG) hpt
  rw [intervalIntegral.integral_add hiF hiG, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmain
  -- the two integral bounds
  have hI1 : (∫ t in a..b, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      ≤ C₁ * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2)) + (y : ℝ) * b ^ γ₁) := by
    refine le_trans ?_ (hMV σ hσ y b hy1 hb6 hybb)
    refine intervalIntegral.integral_mono_interval (by linarith) hab le_rfl ?_
      (hcF.intervalIntegrable 0 b)
    filter_upwards with t
    simp only [Pi.zero_apply]
    positivity
  have hI2 : (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ E * b ^ β := hEM σ hσ hσ6 a b ha hab hbE
  -- the exponent bookkeeping
  have hQ0 : (0 : ℝ) ≤ b ^ e := Real.rpow_nonneg hb0.le _
  have hpow1 : (y : ℝ) * b ^ γ₁ ≤ 4 * b ^ e := by
    calc (y : ℝ) * b ^ γ₁ ≤ (4 * b ^ γ) * b ^ γ₁ :=
          mul_le_mul_of_nonneg_right hyb (Real.rpow_nonneg hb0.le _)
      _ = 4 * (b ^ γ * b ^ γ₁) := by ring
      _ = 4 * b ^ (γ + γ₁) := by rw [← Real.rpow_add hb0]
      _ ≤ 4 * b ^ e :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hb1 (le_max_left _ _)) (by norm_num)
  have hpow2 : (y : ℝ) ^ 2 * b ^ β ≤ 16 * b ^ e := by
    have hy2 : (y : ℝ) ^ 2 ≤ 16 * b ^ (2 * γ) := by
      have hstep : (y : ℝ) ^ 2 ≤ (4 * b ^ γ) ^ 2 := pow_le_pow_left₀ hy0.le hyb 2
      have heq : (4 * b ^ γ) ^ 2 = 16 * b ^ (2 * γ) := by
        rw [mul_pow, ← Real.rpow_natCast (b ^ γ) 2, ← Real.rpow_mul hb0.le]
        norm_num [mul_comm]
      linarith
    calc (y : ℝ) ^ 2 * b ^ β ≤ (16 * b ^ (2 * γ)) * b ^ β :=
          mul_le_mul_of_nonneg_right hy2 (Real.rpow_nonneg hb0.le _)
      _ = 16 * b ^ (2 * γ + β) := by rw [mul_assoc, ← Real.rpow_add hb0]
      _ ≤ 16 * b ^ e :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hb1 (le_max_right _ _)) (by norm_num)
  -- assemble
  have hexp : (1 : ℝ) - (1 - e) = e := by ring
  rw [hexp]
  have hP0 : (0 : ℝ) ≤ b * (y : ℝ) ^ (-(σ₀ - 1 / 2)) := by positivity
  have hs1 : 2 * (∫ t in a..b, ‖Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
      dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      ≤ 2 * C₁ * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2))) + 8 * C₁ * b ^ e := by
    have hmul := mul_le_mul_of_nonneg_left hpow1 (by positivity : (0 : ℝ) ≤ 2 * C₁)
    linarith only [mul_le_mul_of_nonneg_left hI1 (by norm_num : (0 : ℝ) ≤ 2), hmul]
  have hs2 : 2 * (y : ℝ) ^ 2 * (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
      - dirichletPoly (fun _ => 1) (truncationLength σ₀ b) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 32 * E * b ^ e := by
    have hfac : (0 : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hpow2 (by positivity : (0 : ℝ) ≤ 2 * E)
    linarith only [mul_le_mul_of_nonneg_left hI2 hfac, hmul]
  have hCP : (0 : ℝ) ≤ C₁ * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2))) := mul_nonneg hC₁0.le hP0
  have hEP : (0 : ℝ) ≤ E * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2))) := mul_nonneg hE0.le hP0
  have hCQ : (0 : ℝ) ≤ C₁ * b ^ e := mul_nonneg hC₁0.le hQ0
  linarith only [hmain, hs1, hs2, hCP, hEP, hCQ]

/-! ## The circle averages -/

/-- **The vertical integral of the circle averages of `‖F_y − 1‖²`, quantitatively.**
All three exponents are explicit in `θ₀ = min (5/2 − R) (1/4)`, the distance from the critical
line that the circles of radius `R` leave available: `θ = θ₀`, `c ≥ 3θ₀/8` and `γ = θ₀/8`. -/
theorem exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le_rpow {R : ℝ}
    (hR0 : 0 < R) (hR : R < 5 / 2) :
    ∃ C c θ γ : ℝ, 0 < C ∧ 0 < c ∧ c < 1 ∧ 0 < θ ∧ 0 < γ ∧
      θ = min (5 / 2 - R) (1 / 4) ∧ 3 * min (5 / 2 - R) (1 / 4) / 8 ≤ c ∧
      γ = min (5 / 2 - R) (1 / 4) / 8 ∧ ∃ b₀ : ℝ, 4 ≤ b₀ ∧
      ∀ y : ℕ, 1 ≤ y → ∀ a b : ℝ, 4 ≤ a → a ≤ b → b₀ ≤ b → (y : ℝ) ≤ 2 * b ^ γ →
        (∫ u in a..b, circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2)
            ((3 : ℂ) + (u : ℂ) * I) R)
          ≤ C * (b * (y : ℝ) ^ (-θ) + b ^ (1 - c)) := by
  have hRabs : |R| < 5 / 2 := by rwa [abs_of_pos hR0]
  set σ₀ : ℝ := min (3 - R) (3 / 4) with hσ₀
  have hσ₀0 : 1 / 2 < σ₀ := lt_min (by linarith) (by norm_num)
  have hσ₀1 : σ₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨C₁, c, γ₁, hC₁0, hc0, hc1, hγ₁0, hcle, hγ₁eq, b₁, hb₁6, hbd⟩ :=
    exists_integral_normSq_zeta_mul_mollifier_sub_one_le_rpow hσ₀0 hσ₀1
  have hγmin : min γ₁ 1 ≤ γ₁ := min_le_left _ _
  have hγ1le : min γ₁ 1 ≤ 1 := min_le_right _ _
  have hγmin0 : 0 < min γ₁ 1 := lt_min hγ₁0 one_pos
  -- `σ₀ − 1/2 = min (5/2 − R) (1/4)`, and both mean-square exponents are explicit in it
  have hθeq : σ₀ - 1 / 2 = min (5 / 2 - R) (1 / 4) := by
    rw [hσ₀]
    rcases le_total (3 - R) (3 / 4) with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]; ring
    · rw [min_eq_right h, min_eq_right (by linarith)]; norm_num
  have hγ₁eq' : γ₁ = min (5 / 2 - R) (1 / 4) / 8 := by rw [hγ₁eq, hθeq]
  have hγ₁small : γ₁ ≤ 1 := by
    rw [hγ₁eq']
    have : min (5 / 2 - R) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    linarith
  refine ⟨2 * C₁, c, σ₀ - 1 / 2, min γ₁ 1, by positivity, hc0, hc1, by linarith, hγmin0,
    hθeq, by rw [← hθeq]; linarith, by rw [min_eq_left hγ₁small]; exact hγ₁eq',
    max (b₁ + 5 / 2) 5, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro y hy1 a b ha hab hb hyb
  have hbb₁ : b₁ + 5 / 2 ≤ b := le_trans (le_max_left _ _) hb
  have hb5 : (5 : ℝ) ≤ b := le_trans (le_max_right _ _) hb
  have hb4 : (4 : ℝ) ≤ b := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1R : (1 : ℝ) ≤ b := by linarith
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  set K : ℝ := 2 * C₁ * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2)) + b ^ (1 - c)) with hK
  -- the inner estimate, for a fixed angle
  have hinner : ∀ w : ℝ, (∫ u in a..b, mollifiedCircleIntegrandSq y R w u) ≤ K := by
    intro w
    have hs : ∀ u : ℝ, circleMap ((3 : ℂ) + (u : ℂ) * I) R w
        = ((3 + R * Real.cos w : ℝ) : ℂ) + ((u + R * Real.sin w : ℝ) : ℂ) * I := by
      intro u
      simp only [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
    have hEq : (∫ u in a..b, mollifiedCircleIntegrandSq y R w u)
        = ∫ u in a..b, ‖riemannZeta (((3 + R * Real.cos w : ℝ) : ℂ)
              + ((u + R * Real.sin w : ℝ) : ℂ) * I) *
            Mollifier.mollifier y (((3 + R * Real.cos w : ℝ) : ℂ)
              + ((u + R * Real.sin w : ℝ) : ℂ) * I) - 1‖ ^ 2 := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [mollifiedCircleIntegrandSq, hs u, mollifiedZeta]
    have hshift : (∫ u in a..b, ‖riemannZeta (((3 + R * Real.cos w : ℝ) : ℂ)
            + ((u + R * Real.sin w : ℝ) : ℂ) * I) *
          Mollifier.mollifier y (((3 + R * Real.cos w : ℝ) : ℂ)
            + ((u + R * Real.sin w : ℝ) : ℂ) * I) - 1‖ ^ 2)
        = ∫ v in (a + R * Real.sin w)..(b + R * Real.sin w),
            ‖riemannZeta (((3 + R * Real.cos w : ℝ) : ℂ) + (v : ℂ) * I) *
              Mollifier.mollifier y (((3 + R * Real.cos w : ℝ) : ℂ) + (v : ℂ) * I) - 1‖ ^ 2 := by
      rw [← intervalIntegral.integral_comp_add_right
        (fun v : ℝ => ‖riemannZeta (((3 + R * Real.cos w : ℝ) : ℂ) + (v : ℂ) * I) *
          Mollifier.mollifier y (((3 + R * Real.cos w : ℝ) : ℂ) + (v : ℂ) * I) - 1‖ ^ 2)
        (R * Real.sin w)]
    have hR' : |R| = R := abs_of_pos hR0
    have hsin : |R * Real.sin w| ≤ |R| := by
      rw [abs_mul]
      calc |R| * |Real.sin w| ≤ |R| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one w) (abs_nonneg R)
        _ = |R| := mul_one _
    have hcos : |R * Real.cos w| ≤ |R| := by
      rw [abs_mul]
      calc |R| * |Real.cos w| ≤ |R| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one w) (abs_nonneg R)
        _ = |R| := mul_one _
    rw [hR'] at hsin hcos
    have hsin' := neg_abs_le (R * Real.sin w)
    have hsin'' := le_abs_self (R * Real.sin w)
    have hcos' := neg_abs_le (R * Real.cos w)
    have hcos'' := le_abs_self (R * Real.cos w)
    have habs1 : R * Real.sin w ≤ R := le_trans hsin'' hsin
    have habs2 : -R ≤ R * Real.sin w := by
      have := abs_le.mp hsin
      linarith [this.1]
    have hlow : (1 : ℝ) ≤ a + R * Real.sin w := by linarith
    have hleσ : σ₀ ≤ 3 + R * Real.cos w := by
      have h1 : σ₀ ≤ 3 - R := min_le_left _ _
      have := abs_le.mp hcos
      linarith [this.1]
    have hupσ : 3 + R * Real.cos w ≤ 6 := by
      have := abs_le.mp hcos
      linarith [this.2]
    have hb₁le : b₁ ≤ b + R * Real.sin w := by linarith
    have hb'low : b / 2 ≤ b + R * Real.sin w := by linarith
    have hb'1 : (1 : ℝ) ≤ b + R * Real.sin w := by linarith
    have hb'up : b + R * Real.sin w ≤ 2 * b := by linarith
    -- the mollifier length is still admissible at the shifted endpoint
    have hq0 : (0 : ℝ) ≤ (b / 2) ^ (min γ₁ 1) := Real.rpow_nonneg (by linarith) _
    have h2γ : (2 : ℝ) ^ (min γ₁ 1) ≤ 2 := by
      calc (2 : ℝ) ^ (min γ₁ 1) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le one_le_two hγ1le
        _ = 2 := Real.rpow_one 2
    have hsplit : b ^ (min γ₁ 1) = 2 ^ (min γ₁ 1) * (b / 2) ^ (min γ₁ 1) := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      congr 1
      ring
    have hstep1 : (y : ℝ) ≤ 4 * (b / 2) ^ (min γ₁ 1) := by
      nlinarith only [hyb, hsplit, h2γ, hq0]
    have hstep2 : (b / 2) ^ (min γ₁ 1) ≤ (b + R * Real.sin w) ^ γ₁ := by
      calc (b / 2) ^ (min γ₁ 1) ≤ (b + R * Real.sin w) ^ (min γ₁ 1) :=
            Real.rpow_le_rpow (by linarith) hb'low hγmin0.le
        _ ≤ (b + R * Real.sin w) ^ γ₁ := Real.rpow_le_rpow_of_exponent_le hb'1 hγmin
    have hycond : (y : ℝ) ≤ 4 * (b + R * Real.sin w) ^ γ₁ := by linarith
    have hle := hbd (3 + R * Real.cos w) hleσ hupσ y hy1 (a + R * Real.sin w)
      (b + R * Real.sin w) hlow (by linarith) hb₁le hycond
    -- and the shifted right endpoint costs at most a factor two
    have hyneg : (0 : ℝ) ≤ (y : ℝ) ^ (-(σ₀ - 1 / 2)) := Real.rpow_nonneg (by linarith) _
    have hterm1 : (b + R * Real.sin w) * (y : ℝ) ^ (-(σ₀ - 1 / 2))
        ≤ 2 * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2))) := by nlinarith only [hb'up, hyneg]
    have hterm2 : (b + R * Real.sin w) ^ (1 - c) ≤ 2 * b ^ (1 - c) := by
      have e1 : (b + R * Real.sin w) ^ (1 - c) ≤ (2 * b) ^ (1 - c) :=
        Real.rpow_le_rpow (by linarith) hb'up (by linarith)
      have e2 : (2 * b) ^ (1 - c) = 2 ^ (1 - c) * b ^ (1 - c) :=
        Real.mul_rpow (by norm_num) hb0.le
      have e3 : (2 : ℝ) ^ (1 - c) ≤ 2 := by
        calc (2 : ℝ) ^ (1 - c) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
          _ = 2 := Real.rpow_one 2
      have e4 : (0 : ℝ) ≤ b ^ (1 - c) := Real.rpow_nonneg hb0.le _
      nlinarith only [e1, e2, e3, e4]
    rw [hEq, hshift]
    calc (∫ v in (a + R * Real.sin w)..(b + R * Real.sin w),
          ‖riemannZeta (((3 + R * Real.cos w : ℝ) : ℂ) + (v : ℂ) * I) *
            Mollifier.mollifier y (((3 + R * Real.cos w : ℝ) : ℂ) + (v : ℂ) * I) - 1‖ ^ 2)
        ≤ C₁ * ((b + R * Real.sin w) * (y : ℝ) ^ (-(σ₀ - 1 / 2))
            + (b + R * Real.sin w) ^ (1 - c)) := hle
      _ ≤ C₁ * (2 * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2))) + 2 * b ^ (1 - c)) :=
          mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hC₁0.le
      _ = K := by rw [hK]; ring
  -- Fubini and the outer estimate
  have hswap : (∫ u in a..b, ∫ w in (0 : ℝ)..(2 * π), mollifiedCircleIntegrandSq y R w u)
      = ∫ w in (0 : ℝ)..(2 * π), ∫ u in a..b, mollifiedCircleIntegrandSq y R w u := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hpi]
    have h1 : ∀ u : ℝ, (∫ w in (0 : ℝ)..(2 * π), mollifiedCircleIntegrandSq y R w u)
        = ∫ w in Set.Ioc 0 (2 * π), mollifiedCircleIntegrandSq y R w u := fun _ =>
      intervalIntegral.integral_of_le hpi
    simp only [h1]
    have h2 : ∀ w : ℝ, (∫ u in a..b, mollifiedCircleIntegrandSq y R w u)
        = ∫ u in Set.Ioc a b, mollifiedCircleIntegrandSq y R w u := fun _ =>
      intervalIntegral.integral_of_le hab
    simp only [h2]
    exact (integral_integral_swap
      (integrable_uncurry_mollifiedCircleIntegrandSq y hRabs ha)).symm
  have hrewrite : (∫ u in a..b,
        circleAverage (fun z => ‖mollifiedZeta y z - 1‖ ^ 2) ((3 : ℂ) + (u : ℂ) * I) R)
      = (2 * π)⁻¹ * ∫ u in a..b, ∫ w in (0 : ℝ)..(2 * π),
          mollifiedCircleIntegrandSq y R w u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u _ => circleAverage_normSq_mollifiedZeta_sub_one_eq
  have houter : (∫ w in (0 : ℝ)..(2 * π), ∫ u in a..b, mollifiedCircleIntegrandSq y R w u)
      ≤ 2 * π * K := by
    have hintθ : IntervalIntegrable
        (fun w : ℝ => ∫ u in a..b, mollifiedCircleIntegrandSq y R w u) volume 0 (2 * π) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
      have hprod := (integrable_uncurry_mollifiedCircleIntegrandSq y hRabs (a := a) (b := b)
        ha).integral_prod_left
      have h2 : (fun w : ℝ => ∫ u in a..b, mollifiedCircleIntegrandSq y R w u)
          = fun w : ℝ => ∫ u in Set.Ioc a b, mollifiedCircleIntegrandSq y R w u := by
        funext w
        exact intervalIntegral.integral_of_le hab
      rw [h2]
      exact hprod
    have h := intervalIntegral.integral_mono_on hpi hintθ
      (intervalIntegrable_const (c := K)) (fun w _ => hinner w)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    exact h
  rw [hrewrite, hswap]
  have hstep : (2 * π)⁻¹ * (∫ w in (0 : ℝ)..(2 * π), ∫ u in a..b,
        mollifiedCircleIntegrandSq y R w u)
      ≤ (2 * π)⁻¹ * (2 * π * K) :=
    mul_le_mul_of_nonneg_left houter (by positivity)
  have hsimp : (2 * π)⁻¹ * (2 * π * K) = K := by
    field_simp
  linarith only [hstep, hsimp]

end RiemannHypothesis
