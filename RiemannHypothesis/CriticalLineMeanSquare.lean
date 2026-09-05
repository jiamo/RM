/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.StripMeanSquareBohrLandau

/-!
# The mean square of `ζ` **on the critical line**

`RiemannHypothesis.StripMeanSquareBohrLandau` proves the Bohr–Landau mean square
`∫₀ᵀ ‖ζ(σ + i t)‖² dt = O_σ(T)` for every fixed `σ > 1/2`, with a constant that blows up as
`σ` decreases to `1/2`.  Nothing was proved on the line `σ = 1/2` itself, where the classical
Hardy–Littlewood asymptotic is `∫₀ᵀ ‖ζ(1/2 + i t)‖² dt ∼ T log T`.

This file proves the first mean square bound of the repository **on** the critical line:

`exists_integral_normSq_riemannZeta_le_critical_line` :
for every `ε > 0` there is a `C` with `∫₀ᵀ ‖ζ(1/2 + i t)‖² dt ≤ C · T^(1+ε)` for all `T ≥ 1`.

The route is the one of the Bohr–Landau file, carried out at `σ = 1/2`:

* the off-diagonal estimate `offDiagSum_one_le` of `RiemannHypothesis.StripMeanSquare` is
  stated there for `1/2 < σ < 1`, but its proof needs only `1/2 ≤ σ`; it is restated as
  `offDiagSum_one_le'` and specialized to the critical line in `offDiagSum_one_le_half`,
  where it reads `offDiagSum 1 N (1/2) = O(N (1 + log N))`;
* the diagonal term at `σ = 1/2` is the harmonic sum `∑_{n ≤ N} 1/n ≤ 1 + log N`, so the mean
  square of the truncated zeta sum is `(T + O(N))(1 + log N)`
  (`integral_normSq_dirichletPoly_one_le_half`);
* the Euler–Maclaurin expansion to order `m` (`exists_norm_riemannZeta_sub_dirichletPoly_le_em`)
  forces the length `N ≍ T^e` with `e = 2m/(2m−1)`, and the mean square is then `O(T^e log T)`.
  Letting `m → ∞` gives the exponent `1 + ε` for every `ε > 0`.

## Scope

The sharp Hardy–Littlewood asymptotic `∼ T log T` is **not** proved here, and neither is the
`O(T log T)` upper bound: the loss `T^ε` is exactly the loss of the elementary Euler–Maclaurin
approximation of `ζ` on the critical line, which needs a Dirichlet polynomial of length
`N ≍ T^(1+1/(2m−1))` where the approximate functional equation would allow `N ≍ T`.  Removing
it needs the first-derivative test for exponential sums (van der Corput / Kusmin–Landau), which
is not formalized here.  Nothing about the location of the zeroes is deduced.

## Main results

* `offDiagSum_one_le_half` — the off-diagonal term on the critical line is `O(N (1 + log N))`.
* `integral_normSq_dirichletPoly_one_le_half` — the mean square of `∑_{n ≤ N} n^(-1/2-it)`.
* `exists_integral_normSq_riemannZeta_le_critical_line` — **the mean square bound**
  `∫₀ᵀ ‖ζ(1/2 + i t)‖² dt ≤ C_ε T^(1+ε)`.
* `exists_integral_norm_riemannZeta_le_critical_line` — the first moment, `O_ε(T^(1+ε))`.
* `exists_volume_norm_riemannZeta_ge_le_critical_line` — the large values estimate: the set of
  `t ∈ (0, T]` with `‖ζ(1/2 + i t)‖ ≥ V` has measure `O_ε(T^(1+ε)/V²)`.
-/

noncomputable section

open Complex MeasureTheory

namespace RiemannHypothesis

/-! ## The two ingredients at `σ = 1/2` -/

/-- **The off-diagonal term of the mean value theorem on the critical line** is
`O(N (1 + log N))`.  This is `offDiagSum_one_le'` at `σ = 1/2`. -/
theorem offDiagSum_one_le_half :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      offDiagSum (fun _ => 1) N (1 / 2) ≤ C * (N : ℝ) * (1 + Real.log N) := by
  obtain ⟨C, hC, hbd⟩ := offDiagSum_one_le' (σ := 1 / 2) le_rfl (by norm_num)
  refine ⟨C, hC, fun N hN => ?_⟩
  have h := hbd N hN
  have hexp : (2 : ℝ) - 2 * (1 / 2) = 1 := by norm_num
  rwa [hexp, Real.rpow_one] at h

/-- The diagonal term of the mean value theorem on the critical line is the harmonic sum. -/
theorem sum_Icc_diag_half_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 : ℝ)) ≤ 1 + Real.log N := by
  have heq : ∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 : ℝ))
      = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(1 : ℝ)) := by
    rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext n; simp, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1) fun i _ => ?_
    rw [norm_one]
    push_cast
    norm_num [add_comm]
  rw [heq]
  exact sum_range_natAddOne_rpow_neg_le_one_add_log le_rfl N

/-- **The mean square of the truncated zeta sum on the critical line**:
`∫₀ᵀ ‖∑_{n ≤ N} n^(-1/2-it)‖² dt ≤ (T + C N)(1 + log N)`. -/
theorem integral_normSq_dirichletPoly_one_le_half :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ => 1) N (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ (T + C * (N : ℝ)) * (1 + Real.log N) := by
  obtain ⟨C, hC, hoff⟩ := offDiagSum_one_le_half
  refine ⟨C, hC, fun N hN T hT => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have hmain := integral_normSq_dirichletPoly_le_diag_add_offDiag (fun _ => 1) N (1 / 2) hT
  have hdiag := sum_Icc_diag_half_le N
  have hoffN := hoff N hN
  have hdiag' : T * (∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 : ℝ)))
      ≤ T * (1 + Real.log N) := mul_le_mul_of_nonneg_left hdiag hT
  refine hmain.trans ?_
  have hgoal : (T + C * (N : ℝ)) * (1 + Real.log N)
      = T * (1 + Real.log N) + C * (N : ℝ) * (1 + Real.log N) := by ring
  rw [hgoal]
  linarith only [hdiag', hoffN]

/-! ## The mean square of `ζ` on the critical line -/

/-- **The mean square of `ζ` on the critical line is `O_ε(T^(1+ε))`.**

For every `ε > 0` there is a constant `C` with
`∫₀ᵀ ‖ζ(1/2 + i t)‖² dt ≤ C · T^(1+ε)` for every `T ≥ 1`.

The Euler–Maclaurin expansion to order `m` allows the Dirichlet polynomial to be taken of
length `N ≍ T^e` with `e = 2m/(2m−1)`; its mean square is `O(T^e log T)`, and `e → 1` as
`m → ∞`. -/
theorem exists_integral_normSq_riemannZeta_le_critical_line {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ C * T ^ (1 + ε) := by
  have hs0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hs1 : (1 : ℝ) / 2 < 1 := by norm_num
  -- the order of the expansion
  obtain ⟨m, hm, hmbig⟩ : ∃ m : ℕ, 1 ≤ m ∧ 1 / ε + 1 ≤ (m : ℝ) := by
    refine ⟨⌈1 / ε⌉₊ + 1, by omega, ?_⟩
    have h := Nat.le_ceil (1 / ε)
    push_cast
    linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2m : (0 : ℝ) < 2 * (m : ℝ) - 1 := by linarith
  -- the exponent
  set e : ℝ := 2 * (m : ℝ) / (2 * (m : ℝ) - 1) with he_def
  have he1 : (1 : ℝ) ≤ e := by
    rw [he_def, le_div_iff₀ h2m]; linarith
  have he0 : (0 : ℝ) < e := by linarith
  have hehalf : e ≤ 1 + ε / 2 := by
    have hkey : e - 1 = 1 / (2 * (m : ℝ) - 1) := by
      rw [he_def]; field_simp; ring
    have hbd : 1 / (2 * (m : ℝ) - 1) ≤ ε / 2 := by
      rw [div_le_div_iff₀ h2m (by norm_num)]
      have h1 : 2 / ε + 1 ≤ 2 * (m : ℝ) - 1 := by
        have : 2 * (1 / ε + 1) ≤ 2 * (m : ℝ) := by linarith
        have h2 : 2 * (1 / ε) = 2 / ε := by ring
        linarith [h2]
      have hεpos : 0 < ε := hε
      nlinarith [mul_pos hεpos hεpos, (div_mul_cancel₀ (2 : ℝ) (ne_of_gt hεpos))]
    linarith
  set a : ℝ := e - ε with ha_def
  have ha1 : a < 1 := by rw [ha_def]; linarith
  have hkey : e * (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ)) = -(2 * (m : ℝ)) := by
    rw [he_def]
    field_simp
    ring
  -- the ingredients
  obtain ⟨Cem, hCem, hembd⟩ := exists_norm_riemannZeta_sub_dirichletPoly_le_em m hm hs0 hs1
  obtain ⟨C₂, hC₂, hpoly⟩ := integral_normSq_dirichletPoly_one_le_half
  obtain ⟨C₃, hC₃, hlog⟩ := exists_rpow_mul_one_add_log_le ha1
  set L : ℝ := Real.log 6 with hL_def
  have hL0 : (0 : ℝ) ≤ L := Real.log_nonneg (by norm_num)
  set K : ℝ := 3 * (1 + 6 * C₂) * (1 + L + e) * C₃ with hK_def
  have hK0 : (0 : ℝ) < K := by
    rw [hK_def]; positivity
  refine ⟨K + 36 * Real.pi + 6 * Cem ^ 2 + 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2, ?_,
    fun T hT => ?_⟩
  · have h3 : (0 : ℝ) < 6 * Cem ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 := by positivity
    have h2 : (0 : ℝ) < 36 * Real.pi := by positivity
    linarith
  -- fix `T`
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  set x : ℝ := T ^ e with hx_def
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow hT he0.le
  have hx0 : (0 : ℝ) < x := by linarith
  have hTx : T ≤ x := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ x := Real.rpow_le_rpow_of_exponent_le hT he1
  set N : ℕ := ⌈x⌉₊ + ⌈T⌉₊ + 1 with hN_def
  have hN1 : 1 ≤ N := by omega
  have hNcast : (N : ℝ) = (⌈x⌉₊ : ℝ) + (⌈T⌉₊ : ℝ) + 1 := by rw [hN_def]; push_cast; ring
  have hNx : x ≤ (N : ℝ) := by
    have h := Nat.le_ceil x
    have hpos : (0 : ℝ) ≤ (⌈T⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [hNcast]; linarith
  have hNT : (1 : ℝ) / 2 + T ≤ (N : ℝ) := by
    have h := Nat.le_ceil T
    have hpos : (0 : ℝ) ≤ (⌈x⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [hNcast]; linarith
  have hN6 : (N : ℝ) + 1 ≤ 6 * x := by
    have h1' : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    have h2' : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0.le
    rw [hNcast]
    linarith only [h1', h2', hTx, hx1]
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  clear_value N
  clear_value x
  clear_value e
  -- the two powers of `T`
  have hTe : T ^ e = T ^ a * T ^ ε := by
    rw [ha_def, ← Real.rpow_add hT0]; ring_nf
  have hT1e : (0 : ℝ) < T ^ (1 + ε) := Real.rpow_pos_of_pos hT0 _
  have hTeps : T ^ e ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hT_le : T ≤ T ^ (1 + ε) := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  -- the Dirichlet polynomial term
  have hNlog : Real.log N ≤ L + e * Real.log T := by
    have hle : Real.log N ≤ Real.log (6 * x) := Real.log_le_log hN0 (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0), hx_def, Real.log_rpow hT0] at hle
    linarith only [hle]
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1'
  have hstepL : 1 + Real.log N ≤ (1 + L + e) * (1 + Real.log T) := by
    have hLlog : (0 : ℝ) ≤ L * Real.log T := mul_nonneg hL0 hlogT
    have hexpand : (1 + L + e) * (1 + Real.log T)
        = 1 + Real.log T + L + L * Real.log T + e + e * Real.log T := by ring
    rw [hexpand]
    linarith only [hNlog, hLlog, hlogT, he0]
  have hb1 : 3 * (∫ t in (0 : ℝ)..T,
        ‖dirichletPoly (fun _ => 1) N (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ K * T ^ (1 + ε) := by
    have hpolyN := hpoly N hN1 T hT0.le
    have hTN6 : T + C₂ * (N : ℝ) ≤ (1 + 6 * C₂) * x := by
      have h6 : (N : ℝ) ≤ 6 * x := by linarith
      nlinarith [hC₂.le, hTx]
    have hfirst : (T + C₂ * (N : ℝ)) * (1 + Real.log N)
        ≤ (1 + 6 * C₂) * x * ((1 + L + e) * (1 + Real.log T)) := by
      have hnn : (0 : ℝ) ≤ 1 + Real.log N := by linarith
      have h2 : (0 : ℝ) ≤ (1 + 6 * C₂) * x := by positivity
      exact mul_le_mul hTN6 hstepL hnn h2
    have hxlog : x * (1 + Real.log T) ≤ C₃ * T ^ (1 + ε) := by
      have h := hlog T hT
      have hx_eq : x = T ^ a * T ^ ε := by rw [hx_def, hTe]
      have hTeps0 : (0 : ℝ) < T ^ ε := Real.rpow_pos_of_pos hT0 _
      have hstep : x * (1 + Real.log T) = (T ^ a * (1 + Real.log T)) * T ^ ε := by
        rw [hx_eq]; ring
      rw [hstep]
      have h2 : (T ^ a * (1 + Real.log T)) * T ^ ε ≤ (C₃ * T) * T ^ ε :=
        mul_le_mul_of_nonneg_right h hTeps0.le
      have h3 : (C₃ * T) * T ^ ε = C₃ * T ^ (1 + ε) := by
        rw [Real.rpow_add hT0, Real.rpow_one]; ring
      linarith [h2, h3.le, h3.ge]
    calc 3 * (∫ t in (0 : ℝ)..T,
          ‖dirichletPoly (fun _ => 1) N (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ 3 * ((T + C₂ * (N : ℝ)) * (1 + Real.log N)) := by linarith only [hpolyN]
      _ ≤ 3 * ((1 + 6 * C₂) * x * ((1 + L + e) * (1 + Real.log T))) := by
          linarith only [hfirst]
      _ = 3 * (1 + 6 * C₂) * (1 + L + e) * (x * (1 + Real.log T)) := by ring
      _ ≤ 3 * (1 + 6 * C₂) * (1 + L + e) * (C₃ * T ^ (1 + ε)) := by
          have hcoef : (0 : ℝ) ≤ 3 * (1 + 6 * C₂) * (1 + L + e) := by positivity
          exact mul_le_mul_of_nonneg_left hxlog hcoef
      _ = K * T ^ (1 + ε) := by rw [hK_def]; ring
  -- the pole term
  have hb2 : 3 * ((N : ℝ) + 1) ^ (2 - 2 * (1 / 2 : ℝ)) * (Real.pi / 2 / (1 - 1 / 2 : ℝ) ^ 2)
      ≤ 36 * Real.pi * T ^ (1 + ε) := by
    have hexp : (2 : ℝ) - 2 * (1 / 2) = 1 := by norm_num
    rw [hexp, Real.rpow_one]
    have hconst : (Real.pi / 2 / (1 - 1 / 2 : ℝ) ^ 2) = 2 * Real.pi := by norm_num; ring
    rw [hconst]
    have hxT : x ≤ T ^ (1 + ε) := by rw [hx_def]; exact hTeps
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    calc 3 * ((N : ℝ) + 1) * (2 * Real.pi) = 6 * Real.pi * ((N : ℝ) + 1) := by ring
      _ ≤ 6 * Real.pi * (6 * x) := by
          exact mul_le_mul_of_nonneg_left hN6 (by positivity)
      _ = 36 * Real.pi * x := by ring
      _ ≤ 36 * Real.pi * T ^ (1 + ε) := by
          exact mul_le_mul_of_nonneg_left hxT (by positivity)
  -- the two Euler–Maclaurin error terms
  have hNneg : (N : ℝ) ^ (-(2 * (1 / 2 : ℝ))) ≤ 1 := by
    have := Real.rpow_le_rpow_of_nonpos (x := 1) (y := (N : ℝ)) (by norm_num) hN1'
      (by norm_num : -(2 * (1 / 2 : ℝ)) ≤ 0)
    simpa using this
  have hb3 : 6 * Cem ^ 2 * (N : ℝ) ^ (-(2 * (1 / 2 : ℝ))) * T ≤ 6 * Cem ^ 2 * T ^ (1 + ε) := by
    calc 6 * Cem ^ 2 * (N : ℝ) ^ (-(2 * (1 / 2 : ℝ))) * T
        = (6 * Cem ^ 2 * T) * (N : ℝ) ^ (-(2 * (1 / 2 : ℝ))) := by ring
      _ ≤ (6 * Cem ^ 2 * T) * 1 := mul_le_mul_of_nonneg_left hNneg (by positivity)
      _ = 6 * Cem ^ 2 * T := by ring
      _ ≤ 6 * Cem ^ 2 * T ^ (1 + ε) := mul_le_mul_of_nonneg_left hT_le (by positivity)
  have hNm : (N : ℝ) ^ (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ)) ≤ T ^ (-(2 * (m : ℝ))) := by
    have hexp : (2 : ℝ) - 2 * (1 / 2) - 2 * (m : ℝ) ≤ 0 := by linarith
    have h2 : (N : ℝ) ^ (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ))
        ≤ x ^ (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 hNx hexp
    rwa [hx_def, ← Real.rpow_mul hT0.le, hkey] at h2
  have hTm2 : ((T : ℝ) ^ m) ^ 2 = T ^ (2 * (m : ℝ)) := by
    rw [← Real.rpow_natCast T m, ← Real.rpow_natCast (T ^ (m : ℝ)) 2, ← Real.rpow_mul hT0.le]
    ring_nf
  have hbig : (((1 / 2 : ℝ) + T + (m : ℝ)) ^ m) ^ 2
      ≤ ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (2 * (m : ℝ)) := by
    have hbase : (1 / 2 : ℝ) + T + (m : ℝ) ≤ (2 + (m : ℝ)) * T := by
      have hmT : (m : ℝ) ≤ (m : ℝ) * T := by
        calc (m : ℝ) = (m : ℝ) * 1 := by ring
          _ ≤ (m : ℝ) * T := mul_le_mul_of_nonneg_left hT (by linarith only [hmR])
      have hexpand : (2 + (m : ℝ)) * T = T + T + (m : ℝ) * T := by ring
      rw [hexpand]
      linarith only [hmT, hT]
    have hb0 : (0 : ℝ) ≤ (1 / 2 : ℝ) + T + (m : ℝ) := by positivity
    have hp := pow_le_pow_left₀ hb0 hbase m
    rw [mul_pow] at hp
    have hsq : (((1 / 2 : ℝ) + T + (m : ℝ)) ^ m) ^ 2 ≤ ((2 + (m : ℝ)) ^ m * T ^ m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hp 2
    rw [mul_pow, hTm2] at hsq
    exact hsq
  have herr : (((1 / 2 : ℝ) + T + (m : ℝ)) ^ m) ^ 2
        * (N : ℝ) ^ (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ))
      ≤ ((2 + (m : ℝ)) ^ m) ^ 2 := by
    have hnn2 : (0 : ℝ) ≤ (N : ℝ) ^ (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ)) := Real.rpow_nonneg hN0.le _
    have hcancel : T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ))) = 1 := by
      rw [← Real.rpow_add hT0]
      norm_num
    calc (((1 / 2 : ℝ) + T + (m : ℝ)) ^ m) ^ 2
          * (N : ℝ) ^ (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ))
        ≤ (((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (2 * (m : ℝ))) * T ^ (-(2 * (m : ℝ))) :=
          mul_le_mul hbig hNm hnn2 (by positivity)
      _ = ((2 + (m : ℝ)) ^ m) ^ 2 * (T ^ (2 * (m : ℝ)) * T ^ (-(2 * (m : ℝ)))) := by ring
      _ = ((2 + (m : ℝ)) ^ m) ^ 2 := by rw [hcancel, mul_one]
  have hb4 : 6 * Cem ^ 2 * ((((1 / 2 : ℝ) + T + (m : ℝ)) ^ m) ^ 2
        * (N : ℝ) ^ (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ))) * T
      ≤ 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (1 + ε) := by
    calc 6 * Cem ^ 2 * ((((1 / 2 : ℝ) + T + (m : ℝ)) ^ m) ^ 2
          * (N : ℝ) ^ (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ))) * T
        = (6 * Cem ^ 2 * T) * ((((1 / 2 : ℝ) + T + (m : ℝ)) ^ m) ^ 2
            * (N : ℝ) ^ (2 - 2 * (1 / 2 : ℝ) - 2 * (m : ℝ))) := by ring
      _ ≤ (6 * Cem ^ 2 * T) * ((2 + (m : ℝ)) ^ m) ^ 2 :=
          mul_le_mul_of_nonneg_left herr (by positivity)
      _ = 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 * T := by ring
      _ ≤ 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (1 + ε) :=
          mul_le_mul_of_nonneg_left hT_le (by positivity)
  -- assemble
  have hmain := integral_normSq_riemannZeta_le_aux_em (m := m) (σ := 1 / 2) (C := Cem)
    hs0 hs1 hCem.le hembd hN1 hT0.le hNT
  have hexpand : (K + 36 * Real.pi + 6 * Cem ^ 2 + 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2)
      * T ^ (1 + ε)
      = K * T ^ (1 + ε) + 36 * Real.pi * T ^ (1 + ε) + 6 * Cem ^ 2 * T ^ (1 + ε)
        + 6 * Cem ^ 2 * ((2 + (m : ℝ)) ^ m) ^ 2 * T ^ (1 + ε) := by ring
  rw [hexpand]
  linarith only [hmain, hb1, hb2, hb3, hb4]

/-! ## Two consequences: the first moment, and a large values estimate -/

/-- **The first moment of `ζ` on the critical line is `O_ε(T^(1+ε))`.** -/
theorem exists_integral_norm_riemannZeta_le_critical_line {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤ C * T ^ (1 + ε) := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le_critical_line hε
  have hs1 : (1 : ℝ) / 2 < 1 := by norm_num
  refine ⟨(1 + C) / 2, by positivity, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hT0' : (0 : ℝ) < T := by linarith
  have hc := continuous_riemannZeta_line_of_lt_one (σ := 1 / 2) hs1
  have hi1 : IntervalIntegrable (fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      volume 0 T := hc.norm.intervalIntegrable 0 T
  have hisq : IntervalIntegrable
      (fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 0 T :=
    (continuous_normSq_riemannZeta_line_of_lt_one hs1).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable
      (fun t : ℝ => (1 + ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2) volume 0 T :=
    ((continuous_const.add (continuous_normSq_riemannZeta_line_of_lt_one hs1)).div_const
      2).intervalIntegrable 0 T
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (1 + ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2 := by
    intro t _
    nlinarith [sq_nonneg (‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ - 1)]
  refine (intervalIntegral.integral_mono_on hT0 hi1 hi2 hle).trans ?_
  have hsplit : (∫ t in (0 : ℝ)..T, (1 + ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2)
      = (T + ∫ t in (0 : ℝ)..T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const hisq,
      intervalIntegral.integral_const]
    simp
  rw [hsplit]
  have hT_le : T ≤ T ^ (1 + ε) := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  linarith [hmean T hT]

/-- **A large values estimate on the critical line.**  For every `ε > 0` the set of `t ∈ (0, T]`
at which `‖ζ(1/2 + i t)‖ ≥ V` has measure `O_ε(T^(1+ε)/V²)`. -/
theorem exists_volume_norm_riemannZeta_ge_le_critical_line {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ V : ℝ, 0 < V →
      (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖}).toReal
        ≤ C * T ^ (1 + ε) / V ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_riemannZeta_le_critical_line hε
  have hs1 : (1 : ℝ) / 2 < 1 := by norm_num
  refine ⟨C, hC, fun T hT V hV => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set f : ℝ → ℝ := fun t => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hf
  have hcont : Continuous f := continuous_normSq_riemannZeta_line_of_lt_one hs1
  have hint : IntegrableOn f (Set.Ioc (0 : ℝ) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1 (hcont.intervalIntegrable 0 T)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] f :=
    Filter.Eventually.of_forall fun t => by positivity
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hint (V ^ 2)
  have hset : {t : ℝ | V ^ 2 ≤ f t} ∩ Set.Ioc (0 : ℝ) T
      = {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hf]
    constructor
    · rintro ⟨hle, ht⟩
      exact ⟨ht, by nlinarith [norm_nonneg (riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))]⟩
    · rintro ⟨ht, hle⟩
      exact ⟨by nlinarith, ht⟩
  have hmeas : MeasurableSet {t : ℝ | V ^ 2 ≤ f t} :=
    measurableSet_le measurable_const hcont.measurable
  have hrestrict : (volume.restrict (Set.Ioc (0 : ℝ) T)).real {t : ℝ | V ^ 2 ≤ f t}
      = (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖}).toReal := by
    rw [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply hmeas, hset]
  have hintegral : ∫ t in Set.Ioc (0 : ℝ) T, f t ≤ C * T ^ (1 + ε) := by
    rw [← intervalIntegral.integral_of_le hT0]
    exact hmean T hT
  rw [hrestrict] at hmarkov
  rw [le_div_iff₀ (by positivity)]
  calc (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖}).toReal * V ^ 2
      = V ^ 2 * (volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖}).toReal := by ring
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) T, f t := hmarkov
    _ ≤ C * T ^ (1 + ε) := hintegral

end RiemannHypothesis

end
