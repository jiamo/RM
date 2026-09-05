/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.SubconvexityUnconditional

/-!
# The subconvexity bound `t^((1-σ)/3)` inside the critical strip

`RiemannHypothesis.SubconvexityUnconditional` proves, unconditionally,
`‖ζ(1/2+it)‖ ≤ 200 t^(1/6)(log t + 1)`.  The block estimates it rests on are statements about
the *phase* `−(t/2π) log x` alone, so they do not know which vertical line one is on: the only
thing that changes with `σ` is the weight `n^(-σ)` that Abel summation carries.  Running the
same argument on the line `re s = σ` therefore costs nothing and gives, for `1/2 ≤ σ ≤ 1`,

`‖ζ(σ+it)‖ ≤ 400 t^((1-σ)/3) (log t + 1)`,

which for `σ > 1/2` is stronger than the convexity bound `t^((1-σ)/2)` of
`RiemannHypothesis.Convexity` — the exponent `(1-σ)/3` is the one the exponent pair
`(1/6, 2/3)` gives, and at `σ = 1/2` it degenerates to the `1/6` of the previous file.

## Main results

* `cpow_strip_eq` — the splitting `x^(-σ-it) = x^(-σ) · e(−(t/2π) log x)`.
* `norm_sum_block_strip_le` — one block of `∑ n^(-σ-it)`, at most `60 t^((1-σ)/3)`.
* `sum_Icc_rpow_neg_le` — the trivial bound `∑_{n ≤ K} n^(-σ) ≤ K^(1-σ)(1 + log K)`.
* `norm_zetaSum_strip_le` — the Dirichlet polynomial of length `N ≤ 2t²`.
* `norm_riemannZeta_sub_zetaSum_strip_le` — the Euler–Maclaurin error, again at most `10`.
* `norm_riemannZeta_strip_le` — **unconditionally**, `‖ζ(σ+it)‖ ≤ 400 t^((1-σ)/3)(log t + 1)`
  for `1/2 ≤ σ ≤ 1` and `t ≥ 10⁹`.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace SubconvexityStrip

open KusminLandau AFESubconvexity SubconvexityUnconditional

/-- On the line `re s = σ` the factor `x^(-σ-it)` splits into the real weight `x^(-σ)` and the
pure phase `e(−(t/2π) log x)`. -/
theorem cpow_strip_eq {x sg t : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-((sg : ℂ) + (t : ℂ) * I))
      = ((x ^ (-sg) : ℝ) : ℂ) * e2pi (-(t / (2 * Real.pi)) * Real.log x) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    KusminLandau.e2pi, Real.rpow_def_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have h2 : ((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log x) : ℝ) : ℂ)
      = -((t : ℂ) * (Real.log x : ℂ)) := by push_cast; field_simp
  rw [h2]
  push_cast
  ring

/-- `u ^ (2 - 2σ)` is what the weight `M^(-σ)` turns the block bound `60 √M u` into. -/
private theorem block_weight_le {M : ℕ} {u sg : ℝ} (hu : 10 ≤ u) (hsg : 1 / 2 ≤ sg)
    (hM : 30 * u ^ 2 ≤ (M : ℝ)) :
    ((M : ℝ) ^ (-sg)) * (60 * Real.sqrt M * u) ≤ 60 * u ^ (2 - 2 * sg) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hM0 : (0 : ℝ) < (M : ℝ) := by nlinarith [pow_pos hu0 2]
  have hsqrt : Real.sqrt M = (M : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hcomb : ((M : ℝ) ^ (-sg)) * Real.sqrt M = (M : ℝ) ^ (1 / 2 - sg) := by
    rw [hsqrt, ← Real.rpow_add hM0]
    ring_nf
  have hmono : (M : ℝ) ^ (1 / 2 - sg) ≤ (u ^ 2) ^ (1 / 2 - sg) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    nlinarith [pow_pos hu0 2]
  have hpow : (u ^ 2 : ℝ) ^ (1 / 2 - sg) = u ^ (1 - 2 * sg) := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_mul hu0.le]
    norm_num
    ring_nf
  have hfinal : u ^ (1 - 2 * sg) * u = u ^ (2 - 2 * sg) := by
    nth_rewrite 2 [show u = u ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hu0]
    ring_nf
  calc ((M : ℝ) ^ (-sg)) * (60 * Real.sqrt M * u)
      = 60 * (((M : ℝ) ^ (-sg)) * Real.sqrt M) * u := by ring
    _ = 60 * ((M : ℝ) ^ (1 / 2 - sg)) * u := by rw [hcomb]
    _ ≤ 60 * ((u ^ 2 : ℝ) ^ (1 / 2 - sg)) * u := by
        have := mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 60)
        exact mul_le_mul_of_nonneg_right this hu0.le
    _ = 60 * (u ^ (1 - 2 * sg) * u) := by rw [hpow]; ring
    _ = 60 * u ^ (2 - 2 * sg) := by rw [hfinal]

/-- **One block of the Dirichlet polynomial on the line `re s = σ`.** -/
theorem norm_sum_block_strip_le {M L : ℕ} {u sg : ℝ} (hu : 10 ≤ u) (hsg : 1 / 2 ≤ sg)
    (hM : 30 * u ^ 2 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ 2 * u ^ 12) (hLM : L ≤ M) :
    ‖∑ j ∈ range L, ((M + j : ℕ) : ℂ) ^ (-((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I))‖
      ≤ 60 * u ^ (2 - 2 * sg) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hM0 : (0 : ℝ) < (M : ℝ) := by nlinarith [pow_pos hu0 2]
  set w : ℕ → ℝ := fun j => ((M : ℝ) + j) ^ (-sg) with hwdef
  set z : ℕ → ℂ := fun j => e2pi (-(u ^ 6 / (2 * Real.pi)) * Real.log ((M : ℝ) + j)) with hzdef
  have hpos : ∀ j : ℕ, (0 : ℝ) < (M : ℝ) + j := fun j => by positivity
  have hterm : ∀ j ∈ range L,
      ((M + j : ℕ) : ℂ) ^ (-((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I)) = (w j : ℂ) * z j := by
    intro j _
    have hcast : ((M + j : ℕ) : ℂ) = (((M : ℝ) + (j : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, cpow_strip_eq (hpos j)]
  rw [Finset.sum_congr rfl hterm]
  have hnn : ∀ i, 0 ≤ w i := fun i => Real.rpow_nonneg (hpos i).le _
  have hanti : ∀ i j : ℕ, i ≤ j → w j ≤ w i := by
    intro i j hij
    have hle : (M : ℝ) + i ≤ (M : ℝ) + j := by
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    exact Real.rpow_le_rpow_of_nonpos (hpos i) hle (by linarith)
  have hB : ∀ l, l ≤ L → ‖∑ j ∈ range l, z j‖ ≤ 60 * Real.sqrt M * u := fun l hl =>
    norm_sum_e2pi_logPhase_block_le_all hu hM hMu (le_trans hl hLM)
  refine (norm_sum_weighted_le hnn hanti hB).trans ?_
  have hw0 : w 0 = ((M : ℝ) ^ (-sg)) := by
    rw [hwdef]; norm_num
  rw [hw0]
  exact block_weight_le hu hsg hM

/-- The trivial bound for the Dirichlet polynomial on the line `re s = σ`. -/
theorem norm_zetaSum_strip_le_trivial (N : ℕ) {sg t : ℝ} :
    ‖zetaSum N ((sg : ℂ) + (t : ℂ) * I)‖ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-sg) := by
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n hn => ?_))
  have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [Complex.norm_natCast_cpow_of_pos hn0]
  congr 1
  simp

/-- `∑_{1 ≤ n ≤ K} n^(-σ) ≤ K^(1-σ)(1 + log K)` for `σ ≤ 1`. -/
theorem sum_Icc_rpow_neg_le (K : ℕ) {sg : ℝ} (hsg1 : sg ≤ 1) :
    ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-sg) ≤ (K : ℝ) ^ (1 - sg) * (1 + Real.log K) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simpa using Real.rpow_nonneg (le_refl (0 : ℝ)) (1 - sg)
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hstep : ∀ n ∈ Finset.Icc 1 K,
      (n : ℝ) ^ (-sg) ≤ (K : ℝ) ^ (1 - sg) * ((n : ℝ))⁻¹ := by
    intro n hn
    obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnK' : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hnK
    have hsplit : (n : ℝ) ^ (-sg) = (n : ℝ) ^ (1 - sg) * ((n : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn0]
      ring_nf
    rw [hsplit]
    have hmono : (n : ℝ) ^ (1 - sg) ≤ (K : ℝ) ^ (1 - sg) :=
      Real.rpow_le_rpow hn0.le hnK' (by linarith)
    exact mul_le_mul_of_nonneg_right hmono (by positivity)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hK0.le _)
  have hre : ∑ n ∈ Finset.Icc 1 K, ((n : ℝ))⁻¹ = ∑ n ∈ range K, ((n : ℝ) + 1)⁻¹ := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring
  rw [hre]
  have hh : ((harmonic K : ℚ) : ℝ) = ∑ n ∈ range K, ((n : ℝ) + 1)⁻¹ := by simp [harmonic]
  rw [← hh]
  exact_mod_cast harmonic_le_one_add_log K

/-- **The Dirichlet polynomial of length `N ≤ 2t²` on the line `re s = σ`.** -/
theorem norm_zetaSum_strip_le {N : ℕ} {u sg : ℝ} (hu : 10 ≤ u) (hsg : 1 / 2 ≤ sg)
    (hsg1 : sg ≤ 1) (hN : (N : ℝ) ≤ 2 * u ^ 12) :
    ‖zetaSum N ((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I)‖
      ≤ 120 * u ^ (2 - 2 * sg) * (Nat.log 2 N + 1) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hB0 : (0 : ℝ) < u ^ (2 - 2 * sg) := Real.rpow_pos_of_pos hu0 _
  have key : ∀ n : ℕ, (n : ℝ) ≤ 2 * u ^ 12 →
      ‖zetaSum n ((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I)‖
        ≤ 120 * u ^ (2 - 2 * sg) * (Nat.log 2 n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hlog0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
      by_cases hsmall : (n : ℝ) < 60 * u ^ 2
      · -- the trivial bound
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · rw [zetaSum, show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl, Finset.sum_empty,
            norm_zero]
          positivity
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
        refine (norm_zetaSum_strip_le_trivial n).trans ?_
        refine (sum_Icc_rpow_neg_le n hsg1).trans ?_
        -- `n^(1-σ) ≤ 60 u^(2-2σ)` and `1 + log n ≤ 2 (log₂ n + 1)`
        have hnle : (n : ℝ) ^ (1 - sg) ≤ 60 * u ^ (2 - 2 * sg) := by
          have h1 : (n : ℝ) ^ (1 - sg) ≤ (60 * u ^ 2 : ℝ) ^ (1 - sg) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
          have h2 : (60 * u ^ 2 : ℝ) ^ (1 - sg)
              = (60 : ℝ) ^ (1 - sg) * (u ^ 2 : ℝ) ^ (1 - sg) :=
            Real.mul_rpow (by norm_num) (by positivity)
          have h3 : (60 : ℝ) ^ (1 - sg) ≤ 60 := by
            calc (60 : ℝ) ^ (1 - sg) ≤ (60 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 60 := Real.rpow_one 60
          have h4 : (u ^ 2 : ℝ) ^ (1 - sg) = u ^ (2 - 2 * sg) := by
            rw [← Real.rpow_natCast u 2, ← Real.rpow_mul hu0.le]
            norm_num
            ring_nf
          rw [h2, h4] at h1
          nlinarith [h1, h3, hB0, Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 60) (1 - sg)]
        have hlogn : 1 + Real.log n ≤ 2 * ((Nat.log 2 n : ℝ) + 1) := by
          have hlt : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by
            exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
          have hlog : Real.log n ≤ ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
            have h := Real.log_le_log (by linarith) hlt.le
            rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
          have hl2 : Real.log 2 ≤ 0.7 := by
            have := Real.log_two_lt_d9; linarith
          nlinarith [hlog, hl2, hlog0]
        have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (1 - sg) := Real.rpow_nonneg (by linarith) _
        have hpos : (0 : ℝ) ≤ 1 + Real.log n := by
          have := Real.log_nonneg hn1; linarith
        calc (n : ℝ) ^ (1 - sg) * (1 + Real.log n)
            ≤ (60 * u ^ (2 - 2 * sg)) * (2 * ((Nat.log 2 n : ℝ) + 1)) :=
              mul_le_mul hnle hlogn hpos (by positivity)
          _ = 120 * u ^ (2 - 2 * sg) * ((Nat.log 2 n : ℝ) + 1) := by ring
      · rw [not_lt] at hsmall
        have hn60 : (60 : ℝ) ≤ (n : ℝ) := by nlinarith
        have hn2 : 2 ≤ n := by
          have : (2 : ℝ) ≤ (n : ℝ) := by linarith
          exact_mod_cast this
        set K : ℕ := n / 2 with hKdef
        have hKn : K < n := Nat.div_lt_self (by omega) (by norm_num)
        have hKle : K + 1 ≤ n := by omega
        have hKtwice : n ≤ 2 * K + 1 := by omega
        have hKcast : (K : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hKle
        have hKu : (K : ℝ) ≤ 2 * u ^ 12 := le_trans (by exact_mod_cast hKn.le) hn
        have hIH := ih K hKn hKu
        have hsplit : zetaSum n ((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I)
            = zetaSum K ((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I)
              + ∑ j ∈ range (n - K),
                  ((K + 1 + j : ℕ) : ℂ) ^ (-((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I)) := by
          rw [zetaSum, zetaSum, ← Finset.Ico_add_one_right_eq_Icc,
            ← Finset.Ico_add_one_right_eq_Icc,
            ← Finset.sum_Ico_consecutive
              (fun m => ((m : ℂ)) ^ (-((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I)))
              (by omega : 1 ≤ K + 1) (by omega : K + 1 ≤ n + 1)]
          congr 1
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_add_right]
        have hblock : ‖∑ j ∈ range (n - K),
            ((K + 1 + j : ℕ) : ℂ) ^ (-((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I))‖
              ≤ 60 * u ^ (2 - 2 * sg) := by
          refine norm_sum_block_strip_le (M := K + 1) (L := n - K) hu hsg ?_ ?_ (by omega)
          · have : (n : ℝ) ≤ 2 * (K : ℝ) + 1 := by exact_mod_cast hKtwice
            push_cast
            nlinarith
          · push_cast
            linarith [hKcast, hn]
        have hlogn : Nat.log 2 n = Nat.log 2 K + 1 :=
          Nat.log_of_one_lt_of_le (by norm_num) hn2
        rw [hsplit]
        refine (norm_add_le _ _).trans ?_
        rw [hlogn]
        have hcast : ((Nat.log 2 K + 1 : ℕ) : ℝ) = (Nat.log 2 K : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        nlinarith [hIH, hblock, hB0]
  exact key N hN

/-- **The Euler–Maclaurin error on the line `re s = σ`**, at length `t² ≤ N ≤ 2t²`. -/
theorem norm_riemannZeta_sub_zetaSum_strip_le {N : ℕ} {sg t : ℝ} (hsg : 1 / 2 ≤ sg)
    (hsg1 : sg ≤ 1) (ht : 2 ≤ t) (hN : t ^ 2 ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * t ^ 2) :
    ‖riemannZeta ((sg : ℂ) + (t : ℂ) * I) - zetaSum N ((sg : ℂ) + (t : ℂ) * I)‖ ≤ 10 := by
  have ht0 : (0 : ℝ) < t := by linarith
  set s : ℂ := (sg : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = sg := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hsre]; linarith
  have hs1 : s ≠ 1 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    rw [hsim] at this
    linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by nlinarith
  have hNpos : 0 < N := by exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hzeta := riemannZeta_eq_zetaApprox_of_pos_re N hs0 hs1
  have hpoly : ∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s) = zetaSum N s := by
    rw [zetaSum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring
  -- the polar term
  have hden : t ≤ ‖s - 1‖ := by
    have hle : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have him : (s - 1).im = t := by simp [hs]
    rw [him, abs_of_pos ht0] at hle
    exact hle
  have hpolar : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 2 := by
    have hnum : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s)‖ = ((N : ℝ) + 1) ^ (1 - sg) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      congr 1
      simp [hs]
    have hnum1 : ((N : ℝ) + 1) ^ (1 - sg) ≤ ((N : ℝ) + 1) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hnum2 : ((N : ℝ) + 1) ^ (1 / 2 : ℝ) ≤ 2 * t := by
      rw [show (1 / 2 : ℝ) = (1 : ℝ) / 2 by norm_num, ← Real.sqrt_eq_rpow]
      have h1 : Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt (4 * t ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      refine h1.trans (le_of_eq ?_)
      rw [show (4 : ℝ) * t ^ 2 = (2 * t) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [norm_div, hnum, div_le_iff₀ (lt_of_lt_of_le ht0 hden)]
    nlinarith [hnum1, hnum2, hden, ht0]
  -- the tail
  have hbound : ∀ n : ℕ,
      ‖eulerTerm (n + N) s‖ ≤ ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(3 / 2) : ℝ) := by
    intro n
    have h := norm_eulerTerm_le (n + N) hs0.le hs1
    rw [hsre] at h
    refine h.trans ?_
    have hb : (1 : ℝ) ≤ ((n + N : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((n + N : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hmono : (((n + N : ℕ) : ℝ) + 1) ^ (-(1 + sg)) ≤ (((n + N : ℕ) : ℝ) + 1) ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
  have hsummable_bound : Summable
      (fun n : ℕ => ‖s‖ * (((n + N : ℕ) : ℝ) + 1) ^ (-(3 / 2) : ℝ)) := by
    refine Summable.mul_left _ ?_
    exact (summable_natAddOne_rpow_neg (p := 3 / 2) (by norm_num)).comp_injective
      (add_left_injective N)
  have hsummable_norm : Summable (fun n : ℕ => ‖eulerTerm (n + N) s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsummable_bound
  have htail : ‖∑' n : ℕ, eulerTerm (n + N) s‖ ≤ ‖s‖ * (2 / Real.sqrt N) := by
    refine (norm_tsum_le_tsum_norm hsummable_norm).trans ?_
    refine (hsummable_norm.tsum_le_tsum hbound hsummable_bound).trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_shift_rpow_neg_three_halves_le N hNpos)
      (norm_nonneg _)
  have hnorms : ‖s‖ ≤ 1 + t := by
    have h1 : ‖s‖ ≤ ‖(sg : ℂ)‖ + ‖(t : ℂ) * I‖ := by rw [hs]; exact norm_add_le _ _
    have h2 : ‖(t : ℂ) * I‖ = t := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
    have h3 : ‖(sg : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact hsg1
    linarith
  have hsqrtN : t ≤ Real.sqrt N := by
    have h1 : Real.sqrt (t ^ 2) ≤ Real.sqrt N := Real.sqrt_le_sqrt hN
    rwa [Real.sqrt_sq ht0.le] at h1
  have htail2 : ‖s‖ * (2 / Real.sqrt N) ≤ 8 := by
    have h1 : (2 : ℝ) / Real.sqrt N ≤ 2 / t :=
      div_le_div_of_nonneg_left (by norm_num) ht0 hsqrtN
    have h2 : ‖s‖ * (2 / Real.sqrt N) ≤ (1 + t) * (2 / t) :=
      mul_le_mul hnorms h1 (by positivity) (by linarith)
    have h3 : (1 + t) * (2 / t) = 2 / t + 2 := by field_simp
    rw [h3] at h2
    have h4 : (2 : ℝ) / t ≤ 1 := by
      rw [div_le_one ht0]; linarith
    linarith
  have hsplit : riemannZeta s - zetaSum N s
      = ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ∑' n : ℕ, eulerTerm (n + N) s := by
    rw [hzeta]
    unfold zetaApprox
    rw [hpoly]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith [hpolar, htail, htail2]

/-- **Unconditional subconvexity inside the strip**: for `1/2 ≤ σ ≤ 1` and `t ≥ 10⁹`,
`‖ζ(σ+it)‖ ≤ 400 t^((1-σ)/3) (log t + 1)`.  For `σ > 1/2` this is stronger than the convexity
bound `t^((1-σ)/2)`; at `σ = 1/2` it is the exponent `1/6`. -/
theorem norm_riemannZeta_strip_le {sg t : ℝ} (hsg : 1 / 2 ≤ sg) (hsg1 : sg ≤ 1)
    (ht : (10 : ℝ) ^ 9 ≤ t) :
    ‖riemannZeta ((sg : ℂ) + (t : ℂ) * I)‖
      ≤ 400 * t ^ ((1 - sg) / 3) * (Real.log t + 1) := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have ht2 : (2 : ℝ) ≤ t := by nlinarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  set u : ℝ := t ^ ((1 : ℝ) / 6) with hudef
  have hu6 : u ^ 6 = t := by
    rw [hudef, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 6)) 6, ← Real.rpow_mul ht0.le]
    norm_num
  have hu10 : 10 ≤ u := by
    have hbase : ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) = 10 := by
      rw [← Real.rpow_natCast (10 : ℝ) 6, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h1 : ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) ≤ ((10 : ℝ) ^ 9) ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
    have h2 : ((10 : ℝ) ^ 9) ^ ((1 : ℝ) / 6) ≤ u :=
      Real.rpow_le_rpow (by positivity) ht (by norm_num)
    rw [hbase] at h1
    linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hu12 : u ^ 12 = t ^ 2 := by
    have h : u ^ 12 = (u ^ 6) ^ 2 := by ring
    rw [h, hu6]
  -- `u^(2-2σ) = t^((1-σ)/3)`
  have hupow : u ^ (2 - 2 * sg) = t ^ ((1 - sg) / 3) := by
    rw [hudef, ← Real.rpow_mul ht0.le]
    congr 1
    ring
  set N : ℕ := ⌈t ^ 2⌉₊ with hNdef
  have hNlo : t ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) < t ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN2 : (N : ℝ) ≤ 2 * t ^ 2 := by nlinarith
  have hNpos : 0 < N := by
    have h : (0 : ℝ) < (N : ℝ) := by nlinarith
    exact_mod_cast h
  have hzs : ‖zetaSum N ((sg : ℂ) + (t : ℂ) * I)‖
      ≤ 120 * t ^ ((1 - sg) / 3) * (Nat.log 2 N + 1) := by
    have h := norm_zetaSum_strip_le (N := N) (u := u) hu10 hsg hsg1
      (by rw [hu12]; exact hN2)
    rwa [hu6, hupow] at h
  have hem := norm_riemannZeta_sub_zetaSum_strip_le (N := N) hsg hsg1 ht2 hNlo hN2
  have hlogN : ((Nat.log 2 N : ℕ) : ℝ) ≤ 1 + 2.887 * Real.log t := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 N) := by positivity
    have hlogle : Real.log ((2 : ℝ) ^ (Nat.log 2 N)) ≤ Real.log (2 * t ^ 2) :=
      Real.log_le_log h2pos (hpow.trans hN2)
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogle
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl2' : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    have hnn : (0 : ℝ) ≤ ((Nat.log 2 N : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at hlogle
    nlinarith [hlogle, hl2, hnn, hlogt]
  have hpow0 : (1 : ℝ) ≤ t ^ ((1 - sg) / 3) :=
    Real.one_le_rpow ht1 (by linarith)
  have hsplit : riemannZeta ((sg : ℂ) + (t : ℂ) * I)
      = (riemannZeta ((sg : ℂ) + (t : ℂ) * I) - zetaSum N ((sg : ℂ) + (t : ℂ) * I))
        + zetaSum N ((sg : ℂ) + (t : ℂ) * I) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hblocks : 120 * t ^ ((1 - sg) / 3) * ((Nat.log 2 N : ℝ) + 1)
      ≤ 240 * t ^ ((1 - sg) / 3) + 347 * t ^ ((1 - sg) / 3) * Real.log t := by
    nlinarith [hlogN, hpow0, hlogt]
  have hfinal : 10 + (240 * t ^ ((1 - sg) / 3) + 347 * t ^ ((1 - sg) / 3) * Real.log t)
      ≤ 400 * t ^ ((1 - sg) / 3) * (Real.log t + 1) := by
    nlinarith [hpow0, hlogt]
  calc ‖riemannZeta ((sg : ℂ) + (t : ℂ) * I) - zetaSum N ((sg : ℂ) + (t : ℂ) * I)‖
        + ‖zetaSum N ((sg : ℂ) + (t : ℂ) * I)‖
      ≤ 10 + 120 * t ^ ((1 - sg) / 3) * ((Nat.log 2 N : ℝ) + 1) := by
        linarith [hem, hzs]
    _ ≤ 10 + (240 * t ^ ((1 - sg) / 3) + 347 * t ^ ((1 - sg) / 3) * Real.log t) := by linarith
    _ ≤ 400 * t ^ ((1 - sg) / 3) * (Real.log t + 1) := hfinal

end SubconvexityStrip

end RiemannHypothesis

end
