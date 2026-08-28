/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.DirichletPolyMeanSquare
import RiemannHypothesis.NearLine

/-!
# The mean square of `ζ` on a vertical line inside the critical strip

For `σ > 1` the mean square `∫₀ᵀ ‖ζ(σ + i t)‖² dt` is `ζ(2σ) T + O(1)`, and that is proved in
`RiemannHypothesis.MeanSquare` from the absolutely convergent Dirichlet series.  Inside the
critical strip there is no absolutely convergent series to expand, and the classical route is
to replace `ζ` by a Dirichlet polynomial of length `N` — here through the Euler–Maclaurin
representation of `RiemannHypothesis.EulerMaclaurin` — and to apply the mean value theorem for
Dirichlet polynomials of `RiemannHypothesis.DirichletPolyMeanSquare`.

This file carries that programme out and proves

`∫₀ᵀ ‖ζ(σ + i t)‖² dt = O_σ(T)`   for fixed `2/3 < σ < 1`.

The exponent `2/3` is exactly what the *zeroth order* Euler–Maclaurin expansion gives.  The
two competing requirements on the length `N` of the Dirichlet polynomial are

* the tail `∑_{n ≥ N} eulerTerm n s` is `O(‖s‖ N^(-σ))`, and its mean square over `[0, T]` is
  `O(T³ N^(-2σ))`, which is `O(T)` only when `N ≥ T^(1/σ)`;
* the off-diagonal term in the mean value theorem is `O(N^(2-2σ) log N)`, which is `O(T)` only
  when `N^(2-2σ)` is `O(T^(1-ε))`.

Both hold simultaneously exactly when `(2 - 2σ)/σ < 1`, that is `σ > 2/3`.  Reaching every
`σ > 1/2` — the classical theorem of Bohr and Landau, and the input to the zero-density
theorems — requires the higher-order Euler–Maclaurin expansion (`k` Bernoulli terms give
`σ > (k+2)/(2k+3)`), which is not formalized here.

## Main results

* `sum_Icc_rpow_neg_le` : `∑_{n ≤ M} n^(-q) ≤ 1 + M^(1-q)/(1-q)` for `0 ≤ q < 1`.
* `offDiagSum_one_le` : the off-diagonal term of the mean value theorem for the Dirichlet
  polynomial `∑_{n ≤ N} n^(-s)` is `O_σ(N^(2-2σ) (1 + log N))`.
* `norm_riemannZeta_sub_dirichletPoly_le` : the Euler–Maclaurin bound for the difference
  between `ζ(σ + i t)` and the Dirichlet polynomial `∑_{n ≤ N} n^(-σ-i t)`.
* `exists_integral_normSq_riemannZeta_le` : **the mean square bound**
  `∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C_σ T` for `2/3 < σ < 1` and `T ≥ 1`.
* `exists_integral_norm_riemannZeta_le` : the first moment `∫₀ᵀ ‖ζ(σ + i t)‖ dt` is `O_σ(T)`.
* `exists_volume_norm_riemannZeta_ge_le` : the large values estimate, that the set of
  `t ∈ (0, T]` with `‖ζ(σ + i t)‖ ≥ V` has measure `O_σ(T / V²)`.
-/

noncomputable section

open Complex Finset MeasureTheory

namespace RiemannHypothesis

/-! ## Elementary sums -/

/-- The truncated `q`-series with `0 ≤ q < 1`, by comparison with the integral. -/
theorem sum_Icc_rpow_neg_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-q) ≤ 1 + (M : ℝ) ^ (1 - q) / (1 - q) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Nat.cast_zero,
      Real.zero_rpow (ne_of_gt (by linarith : (0 : ℝ) < 1 - q))]
    norm_num
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-q)) (Set.Icc ((1 : ℕ) : ℝ) ((M : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Icc, Nat.cast_one] at hx hy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hsum := hanti.sum_le_integral_Ico hM
  have hint : ∫ x in ((1 : ℕ) : ℝ)..((M : ℕ) : ℝ), x ^ (-q)
      = ((M : ℝ) ^ (1 - q) - 1) / (1 - q) := by
    rw [integral_rpow (Or.inl (by linarith))]
    norm_num
    rw [show -q + 1 = 1 - q by ring]
  have hre : ∑ i ∈ Finset.Ico 1 M, ((i : ℝ) + 1) ^ (-q)
      = ∑ n ∈ Finset.Icc 2 M, (n : ℝ) ^ (-q) := by
    rw [show Finset.Icc 2 M = Finset.Ico 2 (M + 1) by ext n; simp]
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1) fun i _ => ?_
    push_cast
    ring_nf
  have hsplit : ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-q)
      = 1 + ∑ n ∈ Finset.Icc 2 M, (n : ℝ) ^ (-q) := by
    rw [show Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) by ext n; simp [Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp)]
    norm_num
  rw [hsplit]
  have hle : ∑ n ∈ Finset.Icc 2 M, (n : ℝ) ^ (-q) ≤ ((M : ℝ) ^ (1 - q) - 1) / (1 - q) := by
    rw [← hre, ← hint]
    simpa using hsum
  have h2 : ((M : ℝ) ^ (1 - q) - 1) / (1 - q) ≤ (M : ℝ) ^ (1 - q) / (1 - q) := by
    gcongr; linarith
  linarith

/-- For `0 ≤ a < 1` the function `T ↦ T^a (1 + log T)` is `O(T)`. -/
theorem exists_rpow_mul_one_add_log_le {a : ℝ} (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → T ^ a * (1 + Real.log T) ≤ C * T := by
  set ε : ℝ := (1 - a) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  refine ⟨1 + 1 / ε, by positivity, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog : Real.log T ≤ T ^ ε / ε := Real.log_le_rpow_div hT0.le hε0
  have hTa : T ^ a ≤ T := by
    calc T ^ a ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = T := Real.rpow_one T
  have hTae : T ^ (a + ε) ≤ T := by
    calc T ^ (a + ε) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by rw [hε]; linarith)
      _ = T := Real.rpow_one T
  have hpos : (0 : ℝ) ≤ T ^ a := Real.rpow_nonneg hT0.le _
  have hsplit : T ^ a * (1 + Real.log T) ≤ T ^ a * (1 + T ^ ε / ε) := by gcongr
  have hmul : T ^ a * (1 + T ^ ε / ε) = T ^ a + T ^ (a + ε) / ε := by
    rw [Real.rpow_add hT0]; ring
  rw [hmul] at hsplit
  have hdiv : T ^ (a + ε) / ε ≤ T / ε := by gcongr
  have h2 : T / ε = (1 / ε) * T := by ring
  linarith

/-! ## The off-diagonal sum -/

/-- The inner sum of the off-diagonal estimate: for `1 ≤ m ≤ N`,
`∑_{n ≤ N, n ≠ m} n^(-σ)/|n - m| ≤ (6 + 2/(1-σ)) m^(-σ) (1 + log N)`. -/
theorem sum_rpow_neg_div_abs_sub_le {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N m : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≠ m), (n : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)|
      ≤ (6 + 2 / (1 - σ)) * (m : ℝ) ^ (-σ) * (1 + Real.log N) := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans hm hmN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hmrpow : (0 : ℝ) < (m : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hm0 _
  have h1σ : (0 : ℝ) < 1 - σ := by linarith
  set S := (Finset.Icc 1 N).filter (fun n => n ≠ m) with hS
  rw [← Finset.sum_filter_add_sum_filter_not S (fun n => 2 * n ≤ m)]
  have hpart1 : ∑ n ∈ S.filter (fun n => 2 * n ≤ m), (n : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)|
      ≤ (2 / (m : ℝ)) * (1 + (m : ℝ) ^ (1 - σ) / (1 - σ)) := by
    have hstep : ∀ n ∈ S.filter (fun n => 2 * n ≤ m),
        (n : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)| ≤ (2 / (m : ℝ)) * (n : ℝ) ^ (-σ) := by
      intro n hn
      simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨⟨hn1, hnN⟩, hne⟩, h2n⟩ := hn
      have hnr : (2 : ℝ) * n ≤ m := by exact_mod_cast h2n
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have habs : (m : ℝ) / 2 ≤ |(n : ℝ) - (m : ℝ)| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ))]
        linarith
      have habs0 : (0 : ℝ) < |(n : ℝ) - (m : ℝ)| := by linarith
      have hrp := Real.rpow_pos_of_pos hnpos (-σ)
      rw [div_le_iff₀ habs0]
      calc (n : ℝ) ^ (-σ) = (2 / (m : ℝ)) * (n : ℝ) ^ (-σ) * ((m : ℝ) / 2) := by field_simp
        _ ≤ (2 / (m : ℝ)) * (n : ℝ) ^ (-σ) * |(n : ℝ) - (m : ℝ)| :=
            mul_le_mul_of_nonneg_left habs (by positivity)
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum]
    have hsub : S.filter (fun n => 2 * n ≤ m) ⊆ Finset.Icc 1 m := by
      intro n hn
      simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    have hmono : ∑ n ∈ S.filter (fun n => 2 * n ≤ m), (n : ℝ) ^ (-σ)
        ≤ ∑ n ∈ Finset.Icc 1 m, (n : ℝ) ^ (-σ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Real.rpow_nonneg (by positivity) _)
    exact mul_le_mul_of_nonneg_left (hmono.trans (sum_Icc_rpow_neg_le h0.le h1 m))
      (by positivity)
  have hpart2 : ∑ n ∈ S.filter (fun n => ¬ (2 * n ≤ m)), (n : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)|
      ≤ 4 * (m : ℝ) ^ (-σ) * (1 + Real.log N) := by
    have hstep : ∀ n ∈ S.filter (fun n => ¬ (2 * n ≤ m)),
        (n : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)|
          ≤ 2 * (m : ℝ) ^ (-σ) * (1 / |(m : ℝ) - (n : ℝ)|) := by
      intro n hn
      simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨⟨hn1, hnN⟩, hne⟩, h2n⟩ := hn
      have hnr : (m : ℝ) ≤ 2 * n := by
        have : m ≤ 2 * n := by omega
        exact_mod_cast this
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hhalf : (m : ℝ) / 2 ≤ (n : ℝ) := by linarith
      have hrp : (n : ℝ) ^ (-σ) ≤ ((m : ℝ) / 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
      have heq : ((m : ℝ) / 2) ^ (-σ) = (m : ℝ) ^ (-σ) * (2 : ℝ) ^ σ := by
        rw [Real.div_rpow hm0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      have h2s : (2 : ℝ) ^ σ ≤ 2 := by
        calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
          _ = 2 := Real.rpow_one 2
      have hb : (n : ℝ) ^ (-σ) ≤ 2 * (m : ℝ) ^ (-σ) := by
        refine hrp.trans ?_
        rw [heq]
        nlinarith [hmrpow]
      rw [abs_sub_comm, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right hb (by positivity)
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum]
    have hmono : ∑ n ∈ S.filter (fun n => ¬ (2 * n ≤ m)), 1 / |(m : ℝ) - (n : ℝ)|
        ≤ ∑ n ∈ S, 1 / |(m : ℝ) - (n : ℝ)| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => by positivity)
    have hkey : ∑ n ∈ S, 1 / |(m : ℝ) - (n : ℝ)| ≤ 2 * (1 + Real.log N) :=
      sum_inv_abs_sub_le hm hmN
    nlinarith [hmono.trans hkey, hmrpow]
  have hfinal : (2 / (m : ℝ)) * (1 + (m : ℝ) ^ (1 - σ) / (1 - σ))
      ≤ (2 + 2 / (1 - σ)) * (m : ℝ) ^ (-σ) := by
    have hinv : (1 : ℝ) / (m : ℝ) ≤ (m : ℝ) ^ (-σ) := by
      rw [show (1 : ℝ) / (m : ℝ) = (m : ℝ) ^ (-(1 : ℝ)) by rw [Real.rpow_neg_one]; ring]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
    have hmul : (1 / (m : ℝ)) * (m : ℝ) ^ (1 - σ) = (m : ℝ) ^ (-σ) := by
      rw [show (1 : ℝ) / (m : ℝ) = (m : ℝ) ^ (-(1 : ℝ)) by rw [Real.rpow_neg_one]; ring,
        ← Real.rpow_add hm0]
      ring_nf
    have hsplit : (2 / (m : ℝ)) * (1 + (m : ℝ) ^ (1 - σ) / (1 - σ))
        = 2 * (1 / (m : ℝ)) + (2 / (1 - σ)) * ((1 / (m : ℝ)) * (m : ℝ) ^ (1 - σ)) := by
      field_simp
    rw [hsplit, hmul]
    have hc : (0 : ℝ) < 2 / (1 - σ) := by positivity
    nlinarith [hmrpow]
  have hsum : (2 + 2 / (1 - σ)) * (m : ℝ) ^ (-σ) + 4 * (m : ℝ) ^ (-σ) * (1 + Real.log N)
      ≤ (6 + 2 / (1 - σ)) * (m : ℝ) ^ (-σ) * (1 + Real.log N) := by
    nlinarith [mul_nonneg (mul_nonneg hmrpow.le (by positivity : (0 : ℝ) ≤ 2 + 2 / (1 - σ)))
      hlogN]
  linarith

/-- **The off-diagonal term of the mean value theorem for `∑_{n ≤ N} n^(-s)`** is
`O_σ(N^(2-2σ) (1 + log N))` for `1/2 ≤ σ < 1`.  The endpoint `σ = 1/2`, where the bound reads
`O(N (1 + log N))`, is the case used on the critical line. -/
theorem offDiagSum_one_le' {σ : ℝ} (h0 : 1 / 2 ≤ σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      offDiagSum (fun _ => 1) N σ ≤ C * (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) := by
  classical
  have hσ0 : (0 : ℝ) < σ := by linarith
  have h1σ : (0 : ℝ) < 1 - σ := by linarith
  have h2σ : (0 : ℝ) < 2 - 2 * σ := by linarith
  set K : ℝ := 6 + 2 / (1 - σ) with hKdef
  have hK : (0 : ℝ) < K := by rw [hKdef]; positivity
  refine ⟨4 * K * (1 + 1 / (2 - 2 * σ)), by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  set L : ℝ := 1 + Real.log N with hLdef
  have hL1 : (1 : ℝ) ≤ L := by rw [hLdef]; linarith
  set u : ℕ → ℕ → ℝ := fun m n => if m = n then 0 else
      2 * ((m : ℝ) ^ (1 - σ) * ((n : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)|)) with hu
  have hterm : ∀ m ∈ Finset.Icc 1 N, ∀ n ∈ Finset.Icc 1 N,
      (if m = n then 0 else 2 * (‖(1 : ℂ)‖ * ‖(1 : ℂ)‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)))
        / |Real.log ((n : ℝ) / (m : ℝ))|) ≤ u m n + u n m := by
    intro m hm n hn
    simp only [Finset.mem_Icc] at hm hn
    by_cases hmn : m = n
    · simp [hu, hmn]
    · rw [if_neg hmn, hu]
      simp only [if_neg hmn, if_neg (Ne.symm hmn)]
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hne : (m : ℝ) ≠ (n : ℝ) := by exact_mod_cast hmn
      have hkey : 1 / |Real.log ((n : ℝ) / (m : ℝ))| ≤ ((m : ℝ) + (n : ℝ)) / |(n : ℝ) - (m : ℝ)| :=
        inv_abs_log_div_le hm0 hn0 hne
      have habs : (0 : ℝ) < |(n : ℝ) - (m : ℝ)| := by
        rw [abs_pos]; exact sub_ne_zero.mpr (Ne.symm hne)
      have hmr : (0 : ℝ) < (m : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hm0 _
      have hnr : (0 : ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hn0 _
      have hm1 : (m : ℝ) ^ (1 - σ) = (m : ℝ) * (m : ℝ) ^ (-σ) := by
        rw [show (1 : ℝ) - σ = 1 + (-σ) by ring, Real.rpow_add hm0, Real.rpow_one]
      have hn1 : (n : ℝ) ^ (1 - σ) = (n : ℝ) * (n : ℝ) ^ (-σ) := by
        rw [show (1 : ℝ) - σ = 1 + (-σ) by ring, Real.rpow_add hn0, Real.rpow_one]
      rw [abs_sub_comm (m : ℝ) (n : ℝ), hm1, hn1]
      have hexp : 2 * ((m : ℝ) * (m : ℝ) ^ (-σ) * ((n : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)|))
          + 2 * ((n : ℝ) * (n : ℝ) ^ (-σ) * ((m : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)|))
          = 2 * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))
            * (((m : ℝ) + (n : ℝ)) / |(n : ℝ) - (m : ℝ)|) := by
        field_simp
      rw [hexp]
      have hleft : 2 * (‖(1 : ℂ)‖ * ‖(1 : ℂ)‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)))
          / |Real.log ((n : ℝ) / (m : ℝ))|
          = 2 * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) * (1 / |Real.log ((n : ℝ) / (m : ℝ))|) := by
        rw [norm_one]; ring
      rw [hleft]
      exact mul_le_mul_of_nonneg_left hkey (by positivity)
  have hstep1 : offDiagSum (fun _ => 1) N σ
      ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (u m n + u n m) := by
    unfold offDiagSum
    exact Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hterm m hm n hn
  have hstep2 : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (u m n + u n m)
      = 2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, u m n := by
    have e1 : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (u m n + u n m)
        = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, u m n)
          + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, u n m := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_add_distrib
    have e2 : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, u n m
        = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, u m n := Finset.sum_comm
    rw [e1, e2]; ring
  have hinner : ∀ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N, u m n ≤ 2 * K * L * (m : ℝ) ^ (1 - 2 * σ) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
    have heq : ∑ n ∈ Finset.Icc 1 N, u m n
        = 2 * (m : ℝ) ^ (1 - σ)
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≠ m),
              (n : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)| := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h : m = n
      · simp [hu, h]
      · rw [hu]
        simp only [if_neg h, if_pos (Ne.symm h)]
        ring
    rw [heq]
    have hbd := sum_rpow_neg_div_abs_sub_le hσ0 h1 hm.1 hm.2
    have hpow : (m : ℝ) ^ (1 - σ) * (m : ℝ) ^ (-σ) = (m : ℝ) ^ (1 - 2 * σ) := by
      rw [← Real.rpow_add hm0]; ring_nf
    calc 2 * (m : ℝ) ^ (1 - σ)
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≠ m),
              (n : ℝ) ^ (-σ) / |(n : ℝ) - (m : ℝ)|
        ≤ 2 * (m : ℝ) ^ (1 - σ) * (K * (m : ℝ) ^ (-σ) * L) :=
          mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = 2 * K * L * (m : ℝ) ^ (1 - 2 * σ) := by rw [← hpow]; ring
  have houter : ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * σ)
      ≤ (N : ℝ) ^ (2 - 2 * σ) * (1 + 1 / (2 - 2 * σ)) := by
    have hq : ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(2 * σ - 1))
        ≤ 1 + (N : ℝ) ^ (1 - (2 * σ - 1)) / (1 - (2 * σ - 1)) :=
      sum_Icc_rpow_neg_le (by linarith) (by linarith) N
    have hrw : ∀ m : ℕ, (m : ℝ) ^ (1 - 2 * σ) = (m : ℝ) ^ (-(2 * σ - 1)) := by
      intro m; rw [show (1 : ℝ) - 2 * σ = -(2 * σ - 1) by ring]
    have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ) :=
      Real.one_le_rpow hN1 (by linarith)
    have hEq : (1 : ℝ) - (2 * σ - 1) = 2 - 2 * σ := by ring
    rw [Finset.sum_congr rfl fun m _ => hrw m]
    rw [hEq] at hq
    calc ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(2 * σ - 1))
        ≤ 1 + (N : ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ) := hq
      _ ≤ (N : ℝ) ^ (2 - 2 * σ) * (1 + 1 / (2 - 2 * σ)) := by
          rw [mul_add, mul_one, mul_one_div]
          linarith
  have hLpos : (0 : ℝ) < L := by linarith
  calc offDiagSum (fun _ => 1) N σ
      ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (u m n + u n m) := hstep1
    _ = 2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, u m n := hstep2
    _ ≤ 2 * ∑ m ∈ Finset.Icc 1 N, 2 * K * L * (m : ℝ) ^ (1 - 2 * σ) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (by norm_num)
    _ = 4 * K * L * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * σ) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 4 * K * L * ((N : ℝ) ^ (2 - 2 * σ) * (1 + 1 / (2 - 2 * σ))) := by
        refine mul_le_mul_of_nonneg_left houter (by positivity)
    _ = 4 * K * (1 + 1 / (2 - 2 * σ)) * (N : ℝ) ^ (2 - 2 * σ) * L := by ring

/-- **The off-diagonal term of the mean value theorem for `∑_{n ≤ N} n^(-s)`** is
`O_σ(N^(2-2σ) (1 + log N))` for `1/2 < σ < 1`. -/
theorem offDiagSum_one_le {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      offDiagSum (fun _ => 1) N σ ≤ C * (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) :=
  offDiagSum_one_le' h0.le h1

/-! ## The mean square of the Dirichlet polynomial -/

/-- The Dirichlet polynomial with all coefficients `1` is the truncated zeta sum. -/
theorem dirichletPoly_one (N : ℕ) (s : ℂ) :
    dirichletPoly (fun _ => 1) N s = ∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s) := by
  unfold dirichletPoly
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext n; simp, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by congr 1) fun i _ => ?_
  push_cast
  ring_nf

/-- **The mean square of the truncated zeta sum** on `[0, T]`. -/
theorem integral_normSq_dirichletPoly_one_le {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ C * (T + (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N)) := by
  obtain ⟨C₁, hC₁, hoff⟩ := offDiagSum_one_le h0 h1
  have h2σ : (1 : ℝ) < 2 * σ := by linarith
  set D : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)) with hD
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(2 * σ))) :=
    summable_natAddOne_rpow_neg h2σ
  have hD0 : 0 ≤ D := tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  refine ⟨D + C₁, by linarith, fun N hN T hT => ?_⟩
  have hdiag : ∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-2 * σ) ≤ D := by
    have heq : ∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-2 * σ)
        = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(2 * σ)) := by
      rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext n; simp, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1) fun i _ => ?_
      rw [norm_one]
      push_cast
      ring_nf
    rw [heq, hD]
    exact hsum.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (by positivity) _)
  have hmain := integral_normSq_dirichletPoly_le_diag_add_offDiag (fun _ => 1) N σ hT
  have hoffN := hoff N hN
  have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have : 0 ≤ Real.log N := Real.log_nonneg hN1
    positivity
  nlinarith [hmain, hoffN, hdiag, hT, hD0, hC₁]

/-! ## The Euler–Maclaurin error -/

/-- **The Euler–Maclaurin bound** for the difference between `ζ` and the truncated zeta sum on
a vertical line inside the strip. -/
theorem norm_riemannZeta_sub_dirichletPoly_le {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ}
    (hN : 1 ≤ N) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) - dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * I) - 1‖
        + (σ + |t|) * (N : ℝ) ^ (-σ) / σ := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hre]; exact h0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  rw [riemannZeta_eq_zetaApprox_of_pos_re N hs0 hs1, zetaApprox, ← dirichletPoly_one N s]
  have hsplit : dirichletPoly (fun _ => 1) N s + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      + ∑' n : ℕ, eulerTerm (n + N) s - dirichletPoly (fun _ => 1) N s
      = ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ∑' n : ℕ, eulerTerm (n + N) s := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hre]
  · have hbd : ∀ n : ℕ, ‖eulerTerm (n + N) s‖ ≤ ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
      fun n => norm_eulerTerm_le (n + N) hs0.le hs1
    have hsh : Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re))) :=
      (summable_nat_add_iff N).2 (summable_natAddOne_rpow_neg (by rw [hre]; linarith))
    have hsummable := hsh.mul_left ‖s‖
    have hnorms : Summable (fun n : ℕ => ‖eulerTerm (n + N) s‖) :=
      hsummable.of_nonneg_of_le (fun n => norm_nonneg _) hbd
    have htail : ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re))
        ≤ (N : ℝ) ^ (1 - (1 + s.re)) / ((1 + s.re) - 1) :=
      tsum_shift_rpow_neg_le_rpow (by rw [hre]; linarith) hN
    have hnorm_s : ‖s‖ ≤ σ + |t| := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [hre, him, abs_of_pos h0] at h
      exact h
    have hpos : (0 : ℝ) ≤ ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
      tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
    calc ‖∑' n : ℕ, eulerTerm (n + N) s‖
        ≤ ∑' n : ℕ, ‖eulerTerm (n + N) s‖ := norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' n : ℕ, ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) :=
          hnorms.tsum_le_tsum hbd hsummable
      _ = ‖s‖ * ∑' n : ℕ, (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + s.re)) := tsum_mul_left
      _ ≤ (σ + |t|) * ((N : ℝ) ^ (1 - (1 + s.re)) / ((1 + s.re) - 1)) :=
          mul_le_mul hnorm_s htail hpos (by positivity)
      _ = (σ + |t|) * (N : ℝ) ^ (-σ) / σ := by
          rw [hre, show (1 : ℝ) - (1 + σ) = -σ by ring, show (1 + σ) - 1 = σ by ring]
          ring

/-! ## Continuity along the line, and two auxiliary integrals -/

/-- The map `t ↦ ζ(σ + i t)` is continuous for `σ < 1`: the line misses the pole at `s = 1`. -/
theorem continuous_riemannZeta_line_of_lt_one {σ : ℝ} (h1 : σ < 1) :
    Continuous (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) := by
  have hline : Continuous (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I)) := by fun_prop
  rw [continuous_iff_continuousAt]
  intro t
  have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have hre : ((σ : ℂ) + (t : ℂ) * I).re = 1 := by rw [h]; simp
    simp at hre
    linarith
  exact ContinuousAt.comp (f := fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I)) (g := riemannZeta)
    (differentiableAt_riemannZeta hne).continuousAt hline.continuousAt

/-- The map `t ↦ ‖ζ(σ + i t)‖²` is continuous for `σ < 1`. -/
theorem continuous_normSq_riemannZeta_line_of_lt_one {σ : ℝ} (h1 : σ < 1) :
    Continuous (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
  (continuous_riemannZeta_line_of_lt_one h1).norm.pow 2

/-- The map `t ↦ ‖∑_{n ≤ N} n^(-σ-i t)‖²` is continuous. -/
theorem continuous_normSq_dirichletPoly_line {σ : ℝ} (N : ℕ) :
    Continuous (fun t : ℝ => ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
  refine (Continuous.norm ?_).pow 2
  unfold dirichletPoly
  refine continuous_finset_sum _ fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
  have hc : Continuous (fun t : ℝ => ((n : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * I))) := by
    refine Continuous.cpow continuous_const (by fun_prop) ?_
    intro t
    left
    simpa using hn0
  simpa using hc

/-- `∫₀ᵀ dt / ((1-σ)² + t²) ≤ (π/2)/(1-σ)²`, uniformly in `T`. -/
theorem integral_inv_sq_shift_le {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, 1 / ((1 - σ) ^ 2 + t ^ 2)) ≤ (Real.pi / 2) / (1 - σ) ^ 2 := by
  have h1σ : (0 : ℝ) < 1 - σ := by linarith
  have hsq1 : (1 - σ) ^ 2 ≤ 1 := by nlinarith
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) T,
      1 / ((1 - σ) ^ 2 + t ^ 2) ≤ (1 / (1 - σ) ^ 2) * (1 / (1 + t ^ 2)) := by
    intro t _
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hkey : (1 / (1 - σ) ^ 2) * ((1 - σ) ^ 2 + t ^ 2) = 1 + t ^ 2 / (1 - σ) ^ 2 := by
      field_simp
    have ht2 : t ^ 2 ≤ t ^ 2 / (1 - σ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg t]
    rw [hkey]
    linarith
  have hcont1 : Continuous (fun t : ℝ => 1 / ((1 - σ) ^ 2 + t ^ 2)) := by
    refine Continuous.div continuous_const (by fun_prop) fun t => ?_
    have hs : (0 : ℝ) < 1 - σ := by linarith
    exact ne_of_gt (by nlinarith [sq_nonneg t])
  have hcont2 : Continuous (fun t : ℝ => (1 / (1 - σ) ^ 2) * (1 / (1 + t ^ 2))) := by
    refine Continuous.mul continuous_const
      (Continuous.div continuous_const (by fun_prop) fun t => by positivity)
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / ((1 - σ) ^ 2 + t ^ 2)) volume 0 T :=
    hcont1.intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun t : ℝ => (1 / (1 - σ) ^ 2) * (1 / (1 + t ^ 2))) volume 0 T :=
    hcont2.intervalIntegrable 0 T
  refine (intervalIntegral.integral_mono_on hT hi1 hi2 hle).trans ?_
  rw [intervalIntegral.integral_const_mul, integral_one_div_one_add_sq]
  have harc : Real.arctan T - Real.arctan 0 ≤ Real.pi / 2 := by
    rw [Real.arctan_zero, sub_zero]
    linarith [Real.arctan_lt_pi_div_two T]
  have hinv : (0 : ℝ) < 1 / (1 - σ) ^ 2 := by positivity
  rw [div_eq_mul_one_div (Real.pi / 2) ((1 - σ) ^ 2), mul_comm (Real.pi / 2)]
  exact mul_le_mul_of_nonneg_left harc hinv.le

/-- The pointwise bound behind the mean square estimate: on `[0, T]` the square of `‖ζ‖` is at
most three times the sum of the squares of the Dirichlet polynomial and of the two
Euler–Maclaurin error terms. -/
theorem normSq_riemannZeta_le_pointwise {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N)
    {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ 3 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        + 3 * (((N : ℝ) + 1) ^ (2 - 2 * σ) * (1 / ((1 - σ) ^ 2 + t ^ 2)))
        + 3 * ((N : ℝ) ^ (-(2 * σ)) / σ ^ 2 * (σ + T) ^ 2) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set P : ℂ := dirichletPoly (fun _ => 1) N s with hP
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnormsq : ‖s - 1‖ ^ 2 = (1 - σ) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hs]
    simp [Complex.normSq_apply]
    ring
  have hnormpos : (0 : ℝ) < ‖s - 1‖ := by
    have hpos : (0 : ℝ) < (1 - σ) ^ 2 + t ^ 2 := by nlinarith
    nlinarith [norm_nonneg (s - 1), hnormsq]
  have hbd := norm_riemannZeta_sub_dirichletPoly_le h0 h1 hN t
  set E1 : ℝ := ((N : ℝ) + 1) ^ (1 - σ) / ‖s - 1‖ with hE1
  set E2 : ℝ := (σ + |t|) * (N : ℝ) ^ (-σ) / σ with hE2
  have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
  have hE20 : 0 ≤ E2 := by rw [hE2]; positivity
  have htri : ‖riemannZeta s‖ ≤ ‖P‖ + E1 + E2 := by
    have := norm_sub_norm_le (riemannZeta s) P
    linarith [hbd]
  have hsq : ‖riemannZeta s‖ ^ 2 ≤ 3 * (‖P‖ ^ 2 + E1 ^ 2 + E2 ^ 2) := by
    nlinarith [norm_nonneg (riemannZeta s), norm_nonneg P, hE10, hE20, htri,
      sq_nonneg (‖P‖ - E1), sq_nonneg (‖P‖ - E2), sq_nonneg (E1 - E2)]
  have hE1sq : E1 ^ 2 = ((N : ℝ) + 1) ^ (2 - 2 * σ) * (1 / ((1 - σ) ^ 2 + t ^ 2)) := by
    rw [hE1, div_pow, hnormsq, ← Real.rpow_natCast (((N : ℝ) + 1) ^ (1 - σ)) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
    ring_nf
  have hE2sq : E2 ^ 2 ≤ (N : ℝ) ^ (-(2 * σ)) / σ ^ 2 * (σ + T) ^ 2 := by
    have hpow : ((N : ℝ) ^ (-σ)) ^ 2 = (N : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hN0.le]
      norm_num
      ring_nf
    rw [hE2, abs_of_nonneg ht0, div_pow, mul_pow, hpow]
    have hNp : (0 : ℝ) < (N : ℝ) ^ (-(2 * σ)) := Real.rpow_pos_of_pos hN0 _
    have hsqT : (σ + t) ^ 2 ≤ (σ + T) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have hrw : (N : ℝ) ^ (-(2 * σ)) / σ ^ 2 * (σ + T) ^ 2 * σ ^ 2
        = (N : ℝ) ^ (-(2 * σ)) * (σ + T) ^ 2 := by field_simp
    rw [hrw]
    nlinarith [hNp]
  nlinarith [hsq, hE1sq, hE2sq]

/-- The mean square of `ζ` on `[0, T]`, in terms of the length `N` of the Dirichlet
polynomial. -/
theorem integral_normSq_riemannZeta_le_aux {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 3 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        + 3 * ((N : ℝ) + 1) ^ (2 - 2 * σ) * ((Real.pi / 2) / (1 - σ) ^ 2)
        + 3 * ((N : ℝ) ^ (-(2 * σ)) / σ ^ 2 * (σ + T) ^ 2) * T := by
  set A : ℝ := ((N : ℝ) + 1) ^ (2 - 2 * σ) with hA
  set B : ℝ := (N : ℝ) ^ (-(2 * σ)) / σ ^ 2 * (σ + T) ^ 2 with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hzetaC := continuous_normSq_riemannZeta_line_of_lt_one (σ := σ) h1
  have hPC := continuous_normSq_dirichletPoly_line (σ := σ) N
  have hcont1 : Continuous (fun t : ℝ => 1 / ((1 - σ) ^ 2 + t ^ 2)) := by
    refine Continuous.div continuous_const (by fun_prop) fun t => ?_
    have hs : (0 : ℝ) < 1 - σ := by linarith
    exact ne_of_gt (by nlinarith [sq_nonneg t])
  have hi1 : IntervalIntegrable
      (fun t : ℝ => 3 * ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 0 T :=
    ((hPC.const_smul (3 : ℝ)).congr fun t => by simp [smul_eq_mul]).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun t : ℝ => 3 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2)))) volume 0 T :=
    (by fun_prop : Continuous
      (fun t : ℝ => 3 * (A * (1 / ((1 - σ) ^ 2 + t ^ 2))))).intervalIntegrable 0 T
  have hi3 : IntervalIntegrable (fun _ : ℝ => 3 * B) volume 0 T := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hT (hzetaC.intervalIntegrable 0 T)
    ((hi1.add hi2).add hi3)
    (fun t ht => normSq_riemannZeta_le_pointwise h0 h1 hN ht.1 ht.2)
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  have hφ : (∫ t in (0 : ℝ)..T, 1 / ((1 - σ) ^ 2 + t ^ 2)) ≤ (Real.pi / 2) / (1 - σ) ^ 2 :=
    integral_inv_sq_shift_le h0 h1 hT
  simp only [smul_eq_mul, sub_zero]
  nlinarith [hφ, hA0]

/-! ## The mean square of `ζ` -/

set_option maxHeartbeats 1000000 in
-- the assembly of the three bounds is a long arithmetic normalisation
/-- **The mean square of `ζ` on a vertical line with `2/3 < σ < 1` is `O(T)`.**

For fixed `σ` in that range there is a constant `C` with
`∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C T` for every `T ≥ 1`. -/
theorem exists_integral_normSq_riemannZeta_le {σ : ℝ} (h0 : 2 / 3 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T := by
  have hs0 : (0 : ℝ) < σ := by linarith
  have h1s : (0 : ℝ) < 1 - σ := by linarith
  have ha1 : (2 - 2 * σ) / σ < 1 := by rw [div_lt_one hs0]; linarith
  obtain ⟨C₂, hC₂, hpoly⟩ := integral_normSq_dirichletPoly_one_le (by linarith) h1
  obtain ⟨C₃, hC₃, hlog⟩ := exists_rpow_mul_one_add_log_le ha1
  have hC₄ : (0 : ℝ) < Real.pi / 2 / (1 - σ) ^ 2 := div_pos (by positivity) (pow_pos h1s 2)
  refine ⟨3 * C₂ * (1 + 8 * C₃) + 27 * (Real.pi / 2 / (1 - σ) ^ 2) + 27, by nlinarith,
    fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  have hx1 : (1 : ℝ) ≤ T ^ (1 / σ) := Real.one_le_rpow hT (by positivity)
  have hx0 : (0 : ℝ) < T ^ (1 / σ) := by linarith
  obtain ⟨N, hN1, hxN, hNx⟩ : ∃ N : ℕ, 1 ≤ N ∧ T ^ (1 / σ) ≤ (N : ℝ) ∧
      (N : ℝ) ≤ T ^ (1 / σ) + 1 := by
    refine ⟨⌈T ^ (1 / σ)⌉₊, ?_, Nat.le_ceil _, (Nat.ceil_lt_add_one hx0.le).le⟩
    have h := le_trans hx1 (Nat.le_ceil (T ^ (1 / σ)))
    exact_mod_cast h
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  -- the two exponent identities
  have hxa : (T ^ (1 / σ)) ^ (2 - 2 * σ) = T ^ ((2 - 2 * σ) / σ) := by
    rw [← Real.rpow_mul hT0.le]
    congr 1
    field_simp
  have hxd : (T ^ (1 / σ)) ^ (-(2 * σ)) = (T ^ 2)⁻¹ := by
    rw [← Real.rpow_mul hT0.le, show 1 / σ * -(2 * σ) = -(2 : ℝ) by field_simp,
      Real.rpow_neg hT0.le]
    norm_num
  have hTa0 : (0 : ℝ) ≤ T ^ ((2 - 2 * σ) / σ) := Real.rpow_nonneg hT0.le _
  have hTa : T ^ ((2 - 2 * σ) / σ) ≤ T := by
    calc T ^ ((2 - 2 * σ) / σ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT ha1.le
      _ = T := Real.rpow_one T
  -- the length of the Dirichlet polynomial
  have hNa : (N : ℝ) ^ (2 - 2 * σ) ≤ 4 * T ^ ((2 - 2 * σ) / σ) := by
    have h2 : (N : ℝ) ^ (2 - 2 * σ) ≤ (2 * T ^ (1 / σ)) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow hN0.le (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hx0.le, hxa] at h2
    have h3 : (2 : ℝ) ^ (2 - 2 * σ) ≤ 4 := by
      calc (2 : ℝ) ^ (2 - 2 * σ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    nlinarith
  have hNa' : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ 9 * T := by
    have h2 : ((N : ℝ) + 1) ^ (2 - 2 * σ) ≤ (3 * T ^ (1 / σ)) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hx0.le, hxa] at h2
    have h3 : (3 : ℝ) ^ (2 - 2 * σ) ≤ 9 := by
      calc (3 : ℝ) ^ (2 - 2 * σ) ≤ (3 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 9 := by norm_num
    nlinarith
  have hNlog : Real.log N ≤ 1 + 2 * Real.log T := by
    have hle : Real.log N ≤ Real.log (2 * T ^ (1 / σ)) :=
      Real.log_le_log hN0 (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0), Real.log_rpow hT0] at hle
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hinv : 1 / σ ≤ 3 / 2 := by rw [div_le_div_iff₀ hs0 (by norm_num)]; linarith
    nlinarith
  have hNneg : (N : ℝ) ^ (-(2 * σ)) ≤ (T ^ 2)⁻¹ := by
    have h2 : (N : ℝ) ^ (-(2 * σ)) ≤ (T ^ (1 / σ)) ^ (-(2 * σ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 hxN (by linarith)
    rwa [hxd] at h2
  -- the three contributions
  have hprod : (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) ≤ 8 * (C₃ * T) := by
    have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1'
    have hNpow0 : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * σ) := Real.rpow_nonneg hN0.le _
    calc (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N)
        ≤ 4 * T ^ ((2 - 2 * σ) / σ) * (2 * (1 + Real.log T)) :=
          mul_le_mul hNa (by linarith) (by linarith) (by linarith)
      _ = 8 * (T ^ ((2 - 2 * σ) / σ) * (1 + Real.log T)) := by ring
      _ ≤ 8 * (C₃ * T) := by linarith [hlog T hT]
  have hb1 : 3 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 3 * C₂ * (1 + 8 * C₃) * T := by
    calc 3 * (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ 3 * (C₂ * (T + (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N))) := by
          linarith [hpoly N hN1 T hT0.le]
      _ ≤ 3 * (C₂ * (T + 8 * (C₃ * T))) := by
          linarith only [mul_le_mul_of_nonneg_left hprod hC₂.le]
      _ = 3 * C₂ * (1 + 8 * C₃) * T := by ring
  have hb2 : 3 * ((N : ℝ) + 1) ^ (2 - 2 * σ) * (Real.pi / 2 / (1 - σ) ^ 2)
      ≤ 27 * (Real.pi / 2 / (1 - σ) ^ 2) * T := by
    linarith only [mul_le_mul_of_nonneg_right hNa' hC₄.le]
  have hb3 : 3 * ((N : ℝ) ^ (-(2 * σ)) / σ ^ 2 * (σ + T) ^ 2) * T ≤ 27 * T := by
    have hY : (N : ℝ) ^ (-(2 * σ)) / σ ^ 2 * (σ + T) ^ 2 ≤ 9 := by
      have hstep : (N : ℝ) ^ (-(2 * σ)) / σ ^ 2 * (σ + T) ^ 2
          ≤ (T ^ 2)⁻¹ / σ ^ 2 * (4 * T ^ 2) := by
        refine mul_le_mul (by gcongr) (by nlinarith) (by positivity) (by positivity)
      have heq : (T ^ 2)⁻¹ / σ ^ 2 * (4 * T ^ 2) = 4 / σ ^ 2 := by
        field_simp
      have hfin : 4 / σ ^ 2 ≤ 9 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith [hstep, heq ▸ hstep]
    linarith only [mul_le_mul_of_nonneg_right hY hT0.le]
  have hmain := integral_normSq_riemannZeta_le_aux hs0 h1 hN1 hT0.le
  have hexp : (3 * C₂ * (1 + 8 * C₃) + 27 * (Real.pi / 2 / (1 - σ) ^ 2) + 27) * T
      = 3 * C₂ * (1 + 8 * C₃) * T + 27 * (Real.pi / 2 / (1 - σ) ^ 2) * T + 27 * T := by ring
  rw [hexp]
  linarith only [hmain, hb1, hb2, hb3]

/-! ## Two consequences: the first moment, and a large values estimate -/

/-- **The first moment of `ζ` on a vertical line with `2/3 < σ < 1` is `O(T)`.**

Immediate from the mean square and `x ≤ (1 + x²)/2`. -/
theorem exists_integral_norm_riemannZeta_le {σ : ℝ} (h0 : 2 / 3 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) ≤ C * T := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le h0 h1
  refine ⟨(1 + C) / 2, by positivity, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hc := continuous_riemannZeta_line_of_lt_one (σ := σ) h1
  have hi1 : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)
      volume 0 T := hc.norm.intervalIntegrable 0 T
  have hisq : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume 0 T := (continuous_normSq_riemannZeta_line_of_lt_one h1).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable
      (fun t : ℝ => (1 + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2) volume 0 T :=
    ((continuous_const.add (continuous_normSq_riemannZeta_line_of_lt_one h1)).div_const
      2).intervalIntegrable 0 T
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (1 + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2 := by
    intro t _
    nlinarith [sq_nonneg (‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ - 1)]
  refine (intervalIntegral.integral_mono_on hT0 hi1 hi2 hle).trans ?_
  have hsplit : (∫ t in (0 : ℝ)..T, (1 + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2)
      = (T + ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const hisq,
      intervalIntegral.integral_const]
    simp
  rw [hsplit]
  linarith [hmean T hT]

/-- **A large values estimate.**  For `2/3 < σ < 1` the set of `t ∈ (0, T]` at which
`‖ζ(σ + i t)‖ ≥ V` has measure `O(T / V²)`.  This is Chebyshev's inequality applied to the
mean square bound, and it is the shape in which the mean square enters the zero-density
estimates. -/
theorem exists_volume_norm_riemannZeta_ge_le {σ : ℝ} (h0 : 2 / 3 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ V : ℝ, 0 < V →
      (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal ≤ C * T / V ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le h0 h1
  refine ⟨C, hC, fun T hT V hV => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set f : ℝ → ℝ := fun t => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hf
  have hcont : Continuous f := continuous_normSq_riemannZeta_line_of_lt_one h1
  have hint : IntegrableOn f (Set.Ioc (0 : ℝ) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1 (hcont.intervalIntegrable 0 T)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] f :=
    Filter.Eventually.of_forall fun t => by positivity
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hint (V ^ 2)
  -- the level set of `f` is the set in the statement
  have hset : {t : ℝ | V ^ 2 ≤ f t} ∩ Set.Ioc (0 : ℝ) T
      = {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧ V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hf]
    constructor
    · rintro ⟨hle, ht⟩
      exact ⟨ht, by nlinarith [norm_nonneg (riemannZeta ((σ : ℂ) + (t : ℂ) * I))]⟩
    · rintro ⟨ht, hle⟩
      exact ⟨by nlinarith, ht⟩
  have hmeas : MeasurableSet {t : ℝ | V ^ 2 ≤ f t} :=
    measurableSet_le measurable_const hcont.measurable
  have hrestrict : (volume.restrict (Set.Ioc (0 : ℝ) T)).real {t : ℝ | V ^ 2 ≤ f t}
      = (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal := by
    rw [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply hmeas, hset]
  have hintegral : ∫ t in Set.Ioc (0 : ℝ) T, f t ≤ C * T := by
    rw [← intervalIntegral.integral_of_le hT0]
    exact hmean T hT
  rw [hrestrict] at hmarkov
  rw [le_div_iff₀ (by positivity)]
  calc (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal * V ^ 2
      = V ^ 2 * (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖}).toReal := by ring
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) T, f t := hmarkov
    _ ≤ C * T := hintegral

end RiemannHypothesis
