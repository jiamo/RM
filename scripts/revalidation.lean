/-
Adversarial revalidation of every `DONE_STRONG` row of `docs/goal/task-board.yaml`.

This file is *not* part of the library build; it is run by `scripts/audit.sh` with

    lake env lean scripts/revalidation.lean

Its purpose is to make the exit criteria of the closed rows machine-checked rather than
prose.  Each claim below is *pinned*: the statement is written out in full here and the
repository's declaration is supplied as the proof term.  If a declaration is ever weakened,
renamed, or restated with extra hypotheses, this file stops elaborating — a status report
cannot hide that.

Nothing here is proved; every `example` is discharged by an existing declaration.
-/
import Solution
import RiemannHypothesis

open Complex Filter Finset
open scoped Topology FourierTransform Convolution

namespace RiemannHypothesisRevalidation

/-! ## M0-STATEMENTS — the statements are the intended ones (definitional unfolding) -/

example : RiemannHypothesis.ZetaForm = _root_.RiemannHypothesis := rfl

example : RiemannHypothesis.ZetaStripForm =
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := rfl

example : RiemannHypothesis.EtaForm =
    ∀ s : ℂ, 0 < s.re → s.re < 1 → RiemannHypothesis.dirichletEta s = 0 → s.re = 1 / 2 := rfl

example (j : ℕ) (s : ℂ) : RiemannHypothesis.pairedTerm j s =
    ((2 * j + 1 : ℕ) : ℂ) ^ (-s) - ((2 * j + 2 : ℕ) : ℂ) ^ (-s) := rfl

example (s : ℂ) : RiemannHypothesis.dirichletEta s =
    ∑' j : ℕ, RiemannHypothesis.pairedTerm j s := rfl

/-! ## M0-CONNECTED -/

example : IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) :=
  RiemannHypothesis.isPreconnected_punctured_halfPlane

/-! ## M0-ETA -/

example : ∀ {s : ℂ}, 0 < s.re → s ≠ 1 →
    RiemannHypothesis.dirichletEta s = (1 - 2 ^ (1 - s)) * riemannZeta s :=
  @RiemannHypothesis.dirichletEta_eq_mul_riemannZeta

example : ∀ {s : ℂ}, 1 < s.re →
    RiemannHypothesis.dirichletEta s = ∑' n : ℕ, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s :=
  @RiemannHypothesis.dirichletEta_eq_tsum_alternating_of_one_lt_re

/-! ## M0-TRIVIAL-ZEROS -/

example : ∀ {s : ℂ}, s.re ≤ 0 → riemannZeta s = 0 → ∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) :=
  @RiemannHypothesis.riemannZeta_eq_zero_of_re_nonpos

example : ∀ {s : ℂ}, s.re < 1 → (1 - 2 ^ (1 - s) : ℂ) ≠ 0 :=
  @RiemannHypothesis.one_sub_two_cpow_ne_zero

/-! ## M0-EQUIV — the three formulations are equivalent (and nothing stronger is claimed) -/

example : RiemannHypothesis.ZetaStripForm ↔ RiemannHypothesis.EtaForm :=
  RiemannHypothesisConjecture.zeta_strip_iff_eta

example : RiemannHypothesis.ZetaForm ↔ RiemannHypothesis.ZetaStripForm :=
  RiemannHypothesisConjecture.zeta_iff_zeta_strip

example : RiemannHypothesis.ZetaForm ↔ RiemannHypothesis.EtaForm :=
  RiemannHypothesisConjecture.zeta_iff_eta

/-! ## M0-PARTIAL-STATEMENTS — these are `Prop`s, and they say what they claim to say -/

example : RiemannHypothesis.ZeroFreeRegion =
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, 3 ≤ |s.im| → 1 - c / Real.log |s.im| < s.re → riemannZeta s ≠ 0 := rfl

example : RiemannHypothesis.HardyTheorem =
    Infinite {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2} := rfl

example (H : ℝ) : RiemannHypothesis.VerifiedUpToHeight H =
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.im → s.im < H → s.re = 1 / 2 := rfl

/-! ## M0-SYMMETRY -/

example : ∀ {s : ℂ}, 0 < s.re → s.re < 1 →
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) :=
  @RiemannHypothesis.riemannZeta_conj_of_mem_strip

example : ∀ {s : ℂ}, 0 < s.re → s.re < 1 → riemannZeta s = 0 → riemannZeta (1 - s) = 0 :=
  @RiemannHypothesis.riemannZeta_one_sub_eq_zero_of_mem_strip

example : ∀ {x : ℝ}, 0 < x → x < 1 → riemannZeta (x : ℂ) ≠ 0 :=
  @RiemannHypothesis.riemannZeta_ofReal_ne_zero_of_lt_one

example : RiemannHypothesis.ZetaStripForm ↔
    ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < s.im → riemannZeta s = 0 → s.re = 1 / 2 :=
  RiemannHypothesis.zeta_strip_iff_upper_strip

example : RiemannHypothesis.ZetaStripForm ↔
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 :=
  RiemannHypothesis.zeta_strip_iff_right_strip

example : RiemannHypothesis.ZetaStripForm ↔
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
  RiemannHypothesis.zeta_strip_iff_nonvanishing_right

example : RiemannHypothesis.ZetaStripForm ↔
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s = 1 - (starRingEnd ℂ) s :=
  RiemannHypothesis.zeta_strip_iff_self_reflective

example : RiemannHypothesis.ZetaStripForm ↔ ∀ H : ℝ, RiemannHypothesis.VerifiedUpToHeight H :=
  RiemannHypothesis.zeta_strip_iff_forall_verifiedUpToHeight

/-! ## M0-ALTERNATING-STRIP -/

example (s : ℂ) (N : ℕ) :
    ∑ n ∈ range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s
      = (∑ j ∈ range (N / 2), RiemannHypothesis.pairedTerm j s)
        + (if N % 2 = 0 then 0 else ((N : ℂ)) ^ (-s)) :=
  RiemannHypothesis.sum_alternating_eq_pairedSum_add_rem s N

example : ∀ {s : ℂ}, 0 < s.re →
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) atTop
      (𝓝 (RiemannHypothesis.dirichletEta s)) :=
  @RiemannHypothesis.tendsto_alternating_partialSum_dirichletEta

example : RiemannHypothesis.EtaForm ↔
    ∀ s : ℂ, 0 < s.re → s.re < 1 →
      Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) atTop (𝓝 0) →
      s.re = 1 / 2 :=
  RiemannHypothesis.eta_iff_eta_limit

example : RiemannHypothesis.ZetaForm ↔ RiemannHypothesis.EtaLimitForm :=
  RiemannHypothesis.zeta_iff_eta_limit

/-! ## M1-ABS-CONV-BOUND -/

example : ∀ {σ : ℝ}, 1 < σ → ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) ≤ 1 + 1 / (σ - 1) :=
  @RiemannHypothesis.tsum_natAddOne_rpow_neg_le

example : ∀ {s : ℂ}, 1 < s.re → ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) :=
  @RiemannHypothesis.norm_riemannZeta_le_of_one_lt_re

example (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) :=
  RiemannHypothesis.three_add_four_cos_add_cos_two_nonneg θ

/-! ## M1-STRIP-GROWTH -/

example : ∀ {s : ℂ}, 0 < s.re → ‖RiemannHypothesis.dirichletEta s‖ ≤ ‖s‖ * (1 + 1 / s.re) :=
  @RiemannHypothesis.norm_dirichletEta_le

example : ∀ {s : ℂ}, 0 < s.re → s.re < 1 →
    ‖riemannZeta s‖ ≤ ‖s‖ * (1 + 1 / s.re) / ((2 : ℝ) ^ (1 - s.re) - 1) :=
  @RiemannHypothesis.norm_riemannZeta_le_of_mem_strip

example : ∀ {σ : ℝ}, 0 < σ → σ < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖riemannZeta (σ + t * I)‖ ≤ C * (1 + |t|) :=
  @RiemannHypothesis.norm_riemannZeta_le_linear_of_mem_strip

/-! ## M1-MERTENS-341 -/

example : ∀ {x : ℝ}, 0 < x → ∀ y : ℝ,
    1 ≤ ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 *
      riemannZeta (1 + x + 2 * I * y)‖ :=
  @RiemannHypothesis.norm_riemannZeta_product_ge_one

/-! ## M1-SPECTRAL-INTERPRETATION -/

example : ∀ {t : ℝ}, 0 < t →
    jacobiTheta (I * (1 / t : ℝ)) = (Real.sqrt t : ℂ) * jacobiTheta (I * (t : ℝ)) :=
  @RiemannHypothesis.jacobiTheta_imaginary_axis

example (t : ℝ) : ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) = jacobiTheta (I * (t : ℝ)) :=
  RiemannHypothesis.evenKernel_zero_eq_jacobiTheta t

example : ∀ {s : ℂ}, 1 < s.re →
    completedRiemannZeta s
      = mellin (fun t : ℝ => (jacobiTheta (I * (t : ℝ)) - 1) / 2) (s / 2) :=
  @RiemannHypothesis.completedRiemannZeta_eq_mellin_jacobiTheta

/-! ## M1-EULER-MACLAURIN -/

example (n : ℕ) (s : ℂ) : RiemannHypothesis.eulerTerm n s =
    ((n + 1 : ℝ) : ℂ) ^ (-s)
      - (((n + 1 : ℝ) : ℂ) ^ (1 - s) - ((n + 2 : ℝ) : ℂ) ^ (1 - s)) / (s - 1) := rfl

example (N : ℕ) (s : ℂ) : RiemannHypothesis.zetaApprox N s =
    (∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s)) + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      + ∑' n : ℕ, RiemannHypothesis.eulerTerm (n + N) s := rfl

example : ∀ (N : ℕ) {s : ℂ}, 1 < s.re →
    riemannZeta s = RiemannHypothesis.zetaApprox N s :=
  @RiemannHypothesis.riemannZeta_eq_zetaApprox

example : ∀ {s : ℂ}, 1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ 6 + Real.log (1 + |s.im|) :=
  @RiemannHypothesis.norm_riemannZeta_le_log

/-! ## M1-ZETA-LOWER-BOUND -/

example : ∀ {x y : ℝ}, 0 < x → x ≤ 1 → 1 ≤ |y| →
    x ^ 3 / (8 * (6 + Real.log (1 + 2 * |y|))) ≤ ‖riemannZeta (1 + x + I * y)‖ ^ 4 :=
  @RiemannHypothesis.norm_riemannZeta_pow_four_ge

example : ∀ {x y : ℝ}, 0 < x → x ≤ 1 → 1 ≤ |y| → riemannZeta (1 + x + I * y) ≠ 0 :=
  @RiemannHypothesis.riemannZeta_ne_zero_of_one_lt_re_of_one_le_abs_im

/-! ## M1-ZETA-CONTINUATION -/

example : ∀ (N : ℕ) {s : ℂ}, 0 < s.re → s ≠ 1 →
    riemannZeta s = RiemannHypothesis.zetaApprox N s :=
  @RiemannHypothesis.riemannZeta_eq_zetaApprox_of_pos_re

/-! ## M1-NEARLINE-LOG-BOUND -/

example : ∀ {s : ℂ}, 3 ≤ |s.im| → 1 - 1 / (2 * Real.log |s.im|) ≤ s.re → s.re ≤ 2 →
    ‖riemannZeta s‖ ≤ 18 * Real.log |s.im| :=
  @RiemannHypothesis.norm_riemannZeta_le_log_near_line

/-! ## M1-ZERO-FREE-REGION-NINTH -/

example : ∀ {s : ℂ}, 4 ≤ |s.im| → 1 - 1 / (8 * Real.log |s.im|) ≤ s.re → s.re ≤ 5 / 4 →
    ‖deriv riemannZeta s‖ ≤ 288 * Real.log |s.im| ^ 2 :=
  @RiemannHypothesis.norm_deriv_riemannZeta_le_near_line

example : ∀ {s : ℂ}, 4 ≤ |s.im| → 1 - (1 / 2 ^ 45) / Real.log |s.im| ^ 9 < s.re →
    riemannZeta s ≠ 0 :=
  @RiemannHypothesis.riemannZeta_ne_zero_of_near_one

example : RiemannHypothesis.ZeroFreeRegionNinth = (∃ c : ℝ, 0 < c ∧
    ∀ s : ℂ, 4 ≤ |s.im| → 1 - c / Real.log |s.im| ^ 9 < s.re → riemannZeta s ≠ 0) := rfl

example : ∃ c : ℝ, 0 < c ∧
    ∀ s : ℂ, 4 ≤ |s.im| → 1 - c / Real.log |s.im| ^ 9 < s.re → riemannZeta s ≠ 0 :=
  RiemannHypothesis.zeroFreeRegionNinth

/-! ## M1-STRIP-TRIVIAL-BOUND -/

example : ∀ {s : ℂ}, 0 < s.re → s.re ≤ 1 → 3 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ 8 / s.re * |s.im| ^ (1 - s.re) * (1 + Real.log |s.im|) :=
  @RiemannHypothesis.norm_riemannZeta_le_strip

/-! ## M1-ZERO-LOCATION -/

example : ∀ {s : ℂ}, riemannZeta s = 0 → 4 ≤ |s.im| →
    (1 / 2 ^ 45) / Real.log |s.im| ^ 9 ≤ s.re ∧
      s.re ≤ 1 - (1 / 2 ^ 45) / Real.log |s.im| ^ 9 :=
  @RiemannHypothesis.zero_mem_shrinking_strip

example : ∀ {s : ℂ}, riemannZeta s = 0 → 4 ≤ |s.im| →
    |s.re - 1 / 2| ≤ 1 / 2 - (1 / 2 ^ 45) / Real.log |s.im| ^ 9 :=
  @RiemannHypothesis.zero_abs_re_sub_half_le

/-! ## M1-PNT-REDUCTION -/

example : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) →
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  RiemannHypothesis.chebyshev_theta_tendsto_of_psi

example : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) →
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) :=
  RiemannHypothesis.primeCounting_tendsto_of_chebyshev_theta

example : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) →
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) :=
  RiemannHypothesis.primeCounting_tendsto_of_chebyshev_psi

/-! ## M1-CHEBYSHEV-BOUNDS -/

example : ∀ {x : ℝ}, 8 ≤ x →
    (x - 2) * Real.log 2 - Real.log x ≤ Chebyshev.psi x :=
  @RiemannHypothesis.psi_lower_bound

example : ∀ {x : ℝ}, 12 ≤ x → Real.log 2 / 2 * x ≤ Chebyshev.psi x :=
  @RiemannHypothesis.psi_ge_half_log_two_mul

example : ∀ᶠ x : ℝ in atTop, Real.log 2 / 4 * x ≤ Chebyshev.theta x :=
  RiemannHypothesis.theta_ge_eventually

example : ∀ᶠ x : ℝ in atTop,
    Real.log 2 / 4 * (x / Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) :=
  RiemannHypothesis.primeCounting_ge_eventually

example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    c * (x / Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * (x / Real.log x) :=
  RiemannHypothesis.primeCounting_asymptotic_bounds

example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    c * x ≤ Chebyshev.psi x ∧ Chebyshev.psi x ≤ C * x :=
  RiemannHypothesis.psi_asymptotic_bounds

example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    c * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ C * x :=
  RiemannHypothesis.theta_asymptotic_bounds

/-! ## M1-MERTENS-FIRST -/

example (x : ℝ) : RiemannHypothesis.mertensSum x =
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n := rfl

example : ∀ (N : ℕ), ∑ n ∈ Finset.Ioc 0 N, Real.log n
    = ∑ d ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) :=
  RiemannHypothesis.sum_log_eq_sum_vonMangoldt_mul_floor_div

example : ∀ {N : ℕ}, 1 ≤ N →
    |∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / n - Real.log N|
      ≤ Real.log 4 + 4 :=
  @RiemannHypothesis.mertens_first_nat

example : ∀ {x : ℝ}, 1 ≤ x →
    |RiemannHypothesis.mertensSum x - Real.log x| ≤ Real.log 4 + 4 + Real.log 2 :=
  @RiemannHypothesis.mertens_first

example : (fun x : ℝ => RiemannHypothesis.mertensSum x - Real.log x)
    =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
  RiemannHypothesis.mertens_first_isBigO

example (x : ℝ) : RiemannHypothesis.primeLogSum x =
    ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}, Real.log p / p := rfl

example : ∀ {x : ℝ}, 1 ≤ x →
    |RiemannHypothesis.primeLogSum x - Real.log x| ≤ Real.log 4 + 12 + Real.log 2 :=
  @RiemannHypothesis.mertens_first_prime

example : (fun x : ℝ => RiemannHypothesis.primeLogSum x - Real.log x)
    =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
  RiemannHypothesis.mertens_first_prime_isBigO

/-! ## M1-MERTENS-SECOND -/

example (x : ℝ) : RiemannHypothesis.primeRecipSum x =
    ∑ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}, (1 : ℝ) / p := rfl

example : ∀ (b f : ℕ → ℝ) (N : ℕ),
    ∑ n ∈ Finset.Ioc 0 (N + 1), b n * f n
      = (∑ m ∈ Finset.Ioc 0 (N + 1), b m) * f (N + 1)
        + ∑ n ∈ Finset.Ioc 0 N, (∑ m ∈ Finset.Ioc 0 n, b m) * (f n - f (n + 1)) :=
  RiemannHypothesis.sum_by_parts_Ioc

example : ∀ (M : ℕ), ∑ n ∈ Finset.Icc 2 M, 1 / (n : ℝ) ^ 2 ≤ 1 :=
  RiemannHypothesis.sum_inv_sq_le

example : ∀ {N : ℕ}, 2 ≤ N →
    |RiemannHypothesis.primeRecipSum N - Real.log (Real.log N)| ≤ 50 :=
  @RiemannHypothesis.mertens_second_nat

example : ∀ {x : ℝ}, 4 ≤ x →
    |RiemannHypothesis.primeRecipSum x - Real.log (Real.log x)| ≤ 52 :=
  @RiemannHypothesis.mertens_second

/-! ## M1-MERTENS-THIRD -/

example (x : ℝ) : RiemannHypothesis.primeProd x =
    ∏ p ∈ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime}, (1 - 1 / (p : ℝ))⁻¹ := rfl

example : ∀ {t : ℝ}, 0 < t → t ≤ 1 / 2 →
    t ≤ -Real.log (1 - t) ∧ -Real.log (1 - t) ≤ t + 2 * t ^ 2 :=
  @RiemannHypothesis.neg_log_one_sub_bounds

example : ∀ {x : ℝ}, 4 ≤ x →
    |Real.log (RiemannHypothesis.primeProd x) - Real.log (Real.log x)| ≤ 54 :=
  @RiemannHypothesis.mertens_third

example : ∀ {x : ℝ}, 4 ≤ x →
    Real.exp (-54) * Real.log x ≤ RiemannHypothesis.primeProd x ∧
      RiemannHypothesis.primeProd x ≤ Real.exp 54 * Real.log x :=
  @RiemannHypothesis.mertens_third_bounds

/-! ## M1-IMAGINARY-AXIS -/

example : ∀ {t : ℝ}, t ≠ 0 →
    ‖Complex.Gamma (1 - (t : ℂ) * I)‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t) :=
  @RiemannHypothesis.norm_Gamma_one_sub_mul_I_sq

example : ∀ (t : ℝ),
    ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖ = |Real.sinh (Real.pi * t / 2)| :=
  RiemannHypothesis.norm_cos_pi_one_sub_mul_I_div_two

example : ∀ {t : ℝ}, 2 ≤ |t| →
    ‖riemannZeta ((t : ℂ) * I)‖
      ≤ Real.sqrt (|t| / (2 * Real.pi)) * (6 + Real.log (1 + |t|)) :=
  @RiemannHypothesis.norm_riemannZeta_mul_I_le

example : (fun t : ℝ => ‖riemannZeta ((t : ℂ) * I)‖)
    =O[atTop] fun t : ℝ => Real.sqrt t * Real.log t :=
  RiemannHypothesis.norm_riemannZeta_isBigO_imaginary_axis

/-! ## M1-CONVEXITY -/

example : ∀ {s : ℂ}, 0 < s.re → ‖Complex.Gamma s‖ ≤ Real.Gamma s.re :=
  @RiemannHypothesis.norm_Gamma_le_Gamma_re

example : ∀ {s : ℂ}, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ 100 * Real.exp (Real.pi * |s.im| / 2) * |s.im| ^ 2 :=
  @RiemannHypothesis.norm_riemannZeta_le_exp_strip

example : ∀ {e : ℝ}, 0 < e → e ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ ((1 - s.re) / 2 + e) :=
  @RiemannHypothesis.norm_riemannZeta_le_convexity

example : ∀ {e : ℝ}, 0 < e → e ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ (1 / 4 + e) :=
  @RiemannHypothesis.norm_riemannZeta_le_critical_line

/-! ## M1-CONVEXITY-LOG -/

example : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ C * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 2) :=
  RiemannHypothesis.norm_riemannZeta_le_convexity_log

example : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * (1 + Real.log |t|) * |t| ^ ((1 : ℝ) / 4) :=
  RiemannHypothesis.norm_riemannZeta_le_critical_line_log

/-! ## M0-XI -/

example (z : ℂ) : RiemannHypothesis.xiPoint z = 1 / 2 + z * I := rfl

example (z : ℂ) : RiemannHypothesis.riemannXi z =
    (RiemannHypothesis.xiPoint z * (RiemannHypothesis.xiPoint z - 1) *
      completedRiemannZeta₀ (RiemannHypothesis.xiPoint z) + 1) / 2 := rfl

example : RiemannHypothesis.XiForm = ∀ z : ℂ, RiemannHypothesis.riemannXi z = 0 → z.im = 0 :=
  rfl

example : Differentiable ℂ RiemannHypothesis.riemannXi :=
  RiemannHypothesis.differentiable_riemannXi

example : ∀ z : ℂ, RiemannHypothesis.riemannXi (-z) = RiemannHypothesis.riemannXi z :=
  RiemannHypothesis.riemannXi_neg

example : ∀ {s : ℂ}, 0 < s.re → s.re < 1 →
    completedRiemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta s) :=
  @RiemannHypothesis.completedRiemannZeta_conj_of_mem_strip

example : ∀ x : ℝ, (RiemannHypothesis.riemannXi (x : ℂ)).im = 0 :=
  RiemannHypothesis.riemannXi_ofReal_im

example : ∀ {z : ℂ}, RiemannHypothesis.xiPoint z ≠ 0 → RiemannHypothesis.xiPoint z ≠ 1 →
    RiemannHypothesis.riemannXi z =
      RiemannHypothesis.xiPoint z * (RiemannHypothesis.xiPoint z - 1) / 2 *
        completedRiemannZeta (RiemannHypothesis.xiPoint z) :=
  @RiemannHypothesis.riemannXi_eq_completed

example : ∀ {s : ℂ}, 1 ≤ s.re → completedRiemannZeta s ≠ 0 :=
  @RiemannHypothesis.completedRiemannZeta_ne_zero_of_one_le_re

example : ∀ {s : ℂ}, s.re ≤ 0 → completedRiemannZeta s ≠ 0 :=
  @RiemannHypothesis.completedRiemannZeta_ne_zero_of_re_nonpos

example : ∀ {z : ℂ}, RiemannHypothesis.riemannXi z = 0 ↔
    0 < (RiemannHypothesis.xiPoint z).re ∧ (RiemannHypothesis.xiPoint z).re < 1 ∧
      riemannZeta (RiemannHypothesis.xiPoint z) = 0 :=
  @RiemannHypothesis.riemannXi_eq_zero_iff

example : RiemannHypothesis.ZetaStripForm ↔ RiemannHypothesis.XiForm :=
  RiemannHypothesis.zeta_strip_iff_xi

example : RiemannHypothesis.ZetaForm ↔ RiemannHypothesis.XiForm :=
  RiemannHypothesis.zeta_iff_xi

-- conditional bridge, superseded: the hypothesis `H₀ = Ξ` is in fact *false* (the correct
-- normalisation is `H₀(z) = Ξ(z/2)/8`, proved below), so this statement is vacuous; it is
-- pinned here only because the row that introduced it is closed
example : ∀ (_h : ∀ z : ℂ, RiemannHypothesis.dbnH 0 z = RiemannHypothesis.riemannXi z),
    RiemannHypothesis.ZetaForm ↔ ∀ z : ℂ, RiemannHypothesis.dbnH 0 z = 0 → z.im = 0 :=
  RiemannHypothesis.zeta_iff_dbnH_zero_of_eq

/-! ## M2-DE-BRUIJN-NEWMAN -/

example (n : ℕ) (u : ℝ) : RiemannHypothesis.dbnTerm n u =
    (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) -
        3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u)) *
      Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))) := rfl

example (u : ℝ) : RiemannHypothesis.dbnPhi u = ∑' n : ℕ, RiemannHypothesis.dbnTerm (n + 1) u :=
  rfl

example (t : ℝ) (z : ℂ) : RiemannHypothesis.dbnH t z =
    ∫ u in Set.Ioi (0 : ℝ),
      ((Real.exp (t * u ^ 2) * RiemannHypothesis.dbnPhi u : ℝ) : ℂ) *
        Complex.cos ((u : ℂ) * z) := rfl

example : RiemannHypothesis.dbnLambda =
    sInf {t : ℝ | ∀ z : ℂ, RiemannHypothesis.dbnH t z = 0 → z.im = 0} := rfl

example : ∀ {u : ℝ}, 0 ≤ u →
    |RiemannHypothesis.dbnPhi u| ≤
      RiemannHypothesis.dbnConst *
        (Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
  @RiemannHypothesis.abs_dbnPhi_le

example : ∀ (t : ℝ) (z : ℂ),
    MeasureTheory.IntegrableOn (RiemannHypothesis.dbnKernel t z) (Set.Ioi 0) :=
  RiemannHypothesis.integrableOn_dbnKernel

example : ∀ t : ℝ, Differentiable ℂ (RiemannHypothesis.dbnH t) :=
  RiemannHypothesis.differentiable_dbnH

example : ∀ (t : ℝ) (z : ℂ), RiemannHypothesis.dbnH t (-z) = RiemannHypothesis.dbnH t z :=
  RiemannHypothesis.dbnH_neg

example : ∀ (t : ℝ) (z : ℂ), RiemannHypothesis.dbnH t ((starRingEnd ℂ) z) =
    (starRingEnd ℂ) (RiemannHypothesis.dbnH t z) :=
  RiemannHypothesis.dbnH_conj

/-- The two literature results are recorded as `Prop`s only; the pins below check that they
say what they are advertised to say, and no term of either type is produced anywhere. -/
example : RiemannHypothesis.DeBruijnNewmanEquivRH =
    (RiemannHypothesis.ZetaForm ↔ RiemannHypothesis.dbnLambda ≤ 0) := rfl

example : RiemannHypothesis.DeBruijnNewmanNonnegative = (0 ≤ RiemannHypothesis.dbnLambda) := rfl

/-! ## M2-H0-EQUALS-XI -/

example (x : ℝ) : RiemannHypothesis.thetaOmega x =
    ∑' n : ℕ, Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * x)) := rfl

example (u : ℝ) : RiemannHypothesis.wFun u =
    ∑' n : ℕ, Real.exp (u - Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)) := rfl

example (u : ℝ) : RiemannHypothesis.wFun u =
    Real.exp u * RiemannHypothesis.thetaOmega (Real.exp (4 * u)) :=
  RiemannHypothesis.wFun_eq u

example : ∀ u : ℝ, RiemannHypothesis.wFun (-u) = RiemannHypothesis.wFun u + Real.sinh u :=
  RiemannHypothesis.wFun_neg

example : RiemannHypothesis.wFun' 0 = -(1 / 2) := RiemannHypothesis.wFun'_zero

example : ∀ u : ℝ, HasDerivAt RiemannHypothesis.wFun (RiemannHypothesis.wFun' u) u :=
  RiemannHypothesis.hasDerivAt_wFun

example : ∀ u : ℝ, HasDerivAt RiemannHypothesis.wFun' (RiemannHypothesis.wFun'' u) u :=
  RiemannHypothesis.hasDerivAt_wFun'

example : ∀ u : ℝ, RiemannHypothesis.dbnPhi u =
    (RiemannHypothesis.wFun'' u - RiemannHypothesis.wFun u) / 8 :=
  RiemannHypothesis.dbnPhi_eq

example : ∀ s : ℂ, completedRiemannZeta₀ s =
    ∫ x in Set.Ioi (1 : ℝ), ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ (-s / 2 - 1 / 2)) *
      (RiemannHypothesis.thetaOmega x : ℂ) :=
  RiemannHypothesis.completedRiemannZeta₀_eq_integral

example : ∀ z : ℂ, RiemannHypothesis.riemannXi z = 1 / 2 - (4 * z ^ 2 + 1) *
    ∫ u in Set.Ioi (0 : ℝ), (RiemannHypothesis.wFun u : ℂ) * Complex.cos (2 * u * z) :=
  RiemannHypothesis.riemannXi_eq_integral

example : ∀ z : ℂ, (∫ u in Set.Ioi (0 : ℝ),
    ((RiemannHypothesis.wFun'' u : ℂ) + z ^ 2 * (RiemannHypothesis.wFun u : ℂ)) *
      Complex.cos (u * z)) = 1 / 2 :=
  RiemannHypothesis.integral_wFun''_add_sq_mul_wFun

example : ∀ z : ℂ, RiemannHypothesis.dbnH 0 z = RiemannHypothesis.riemannXi (z / 2) / 8 :=
  RiemannHypothesis.dbnH_zero_eq_riemannXi

example : ∀ z : ℂ, RiemannHypothesis.dbnH 0 z = 0 ↔ RiemannHypothesis.riemannXi (z / 2) = 0 :=
  RiemannHypothesis.dbnH_zero_eq_zero_iff

/-- The unconditional replacement for the vacuous conditional bridge above: no hypothesis. -/
example : RiemannHypothesis.ZetaForm ↔ ∀ z : ℂ, RiemannHypothesis.dbnH 0 z = 0 → z.im = 0 :=
  RiemannHypothesis.zeta_iff_dbnH_zero

/-! ## M1-XI-GROWTH -/

example : ∀ {c : ℂ} {R : ℝ}, 0 < R →
    ∀ (n : ℕ) (f : ℂ → ℂ) (M : ℝ), DiffContOnCl ℂ f (Metric.ball c R) →
      (∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) →
      ∀ S : Finset ℂ, S.card = n → (∀ a ∈ S, dist a c ≤ R / 4 ∧ f a = 0) →
      3 ^ n * ‖f c‖ ≤ M :=
  fun hR => RiemannHypothesis.pow_three_card_mul_norm_le hR

example : ∀ {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}, 0 < R →
    DiffContOnCl ℂ f (Metric.ball c R) → (∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) → f c ≠ 0 →
    ({z : ℂ | dist z c ≤ R / 4 ∧ f z = 0}.ncard : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log 3 :=
  fun hR hf hM hc => RiemannHypothesis.ncard_setOf_zeros_le hR hf hM hc

example (s : ℂ) : RiemannHypothesis.xiFn s =
    (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2 := rfl

example (z : ℂ) : RiemannHypothesis.riemannXi z =
    RiemannHypothesis.xiFn (RiemannHypothesis.xiPoint z) := rfl

example : Differentiable ℂ RiemannHypothesis.xiFn := RiemannHypothesis.differentiable_xiFn

example : ∀ s : ℂ, RiemannHypothesis.xiFn (1 - s) = RiemannHypothesis.xiFn s :=
  RiemannHypothesis.xiFn_one_sub

example : RiemannHypothesis.xiFn 2 ≠ 0 := RiemannHypothesis.xiFn_two_ne_zero

example : ∀ {s : ℂ}, 0 < s.re → s.re < 1 → riemannZeta s = 0 → RiemannHypothesis.xiFn s = 0 :=
  fun h0 h1 hz => RiemannHypothesis.xiFn_eq_zero_of_zeta h0 h1 hz

example : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
    ‖RiemannHypothesis.xiFn s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) :=
  RiemannHypothesis.norm_xiFn_le

/-! ## M2-ZERO-COUNT -/

example (T : ℝ) : RiemannHypothesis.nontrivialZeros T =
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T} := rfl

example : ∀ T : ℝ, (RiemannHypothesis.nontrivialZeros T).Finite :=
  RiemannHypothesis.finite_nontrivialZeros

example : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    ((RiemannHypothesis.nontrivialZeros T).ncard : ℝ) ≤ C * T * Real.log T :=
  RiemannHypothesis.ncard_nontrivialZeros_le

/-! ## M2-GAMMA-VERTICAL -/

example : ∀ t : ℝ, ‖Complex.Gamma (1 / 2 + (t : ℂ) * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) :=
  RiemannHypothesis.norm_Gamma_half_add_mul_I_sq

example : ∀ {t : ℝ}, t ≠ 0 →
    ‖Complex.Gamma (1 + (t : ℂ) * I)‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t) :=
  fun ht => RiemannHypothesis.norm_Gamma_one_add_mul_I_sq ht

example : ∀ {s : ℂ}, 1 / 2 ≤ s.re → s.re ≤ 3 →
    ‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤ 2 * ‖s + 3‖ ^ 3 :=
  fun h0 h1 => RiemannHypothesis.norm_Gamma_mul_cos_le_of_mem_strip h0 h1

example : ∀ (n : ℕ) {s : ℂ}, 1 / 4 ≤ s.re → s.re ≤ 5 + n → 1 ≤ |s.im| →
    ‖Complex.Gamma s‖ ≤ 8 * (5 + n + ‖s‖) ^ (5 + n) * Real.exp (-(Real.pi * |s.im| / 2)) :=
  @fun n _s h0 h1 ht => RiemannHypothesis.norm_Gamma_le_exp_decay_of_le n h0 h1 ht

/-! ## M2-ZERO-COUNT-LOCAL -/

example : ∀ {s : ℂ}, 3 ≤ s.re → 1 / 2 ≤ ‖riemannZeta s‖ :=
  fun hs => RiemannHypothesis.half_le_norm_riemannZeta_of_three_le_re hs

example : ∀ {s : ℂ}, -23 ≤ s.re → s.re ≤ 24 → 3 ≤ |s.im| →
    ‖RiemannHypothesis.xiFn s‖
      ≤ 128 * (13 + ‖s‖) ^ 16 * Real.exp (-(Real.pi * |s.im| / 4)) :=
  fun h0 h1 ht => RiemannHypothesis.norm_xiFn_le_exp_neg_pi_im' h0 h1 ht

example : ∀ {T : ℝ}, 25 ≤ T →
    Real.exp (-(Real.pi * T / 4)) ≤ ‖RiemannHypothesis.xiFn (4 + (T : ℂ) * I)‖ :=
  fun hT => RiemannHypothesis.exp_le_norm_xiFn_centre hT

example (T : ℝ) : RiemannHypothesis.zerosNearHeight T =
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im - T| ≤ 1} := rfl

example : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 25 ≤ T →
    ((RiemannHypothesis.zerosNearHeight T).ncard : ℝ) ≤ C * Real.log T :=
  RiemannHypothesis.ncard_zerosNearHeight_le

/-! ## M2-ZERO-SUM -/

example : RiemannHypothesis.nontrivialZeroSet =
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} := rfl

example : RiemannHypothesis.nontrivialZeroSet.Countable :=
  RiemannHypothesis.countable_nontrivialZeroSet

example : ∃ B : ℝ, 0 < B ∧ ∀ S : Finset ℂ,
    (∀ ρ ∈ S, ρ ∈ RiemannHypothesis.nontrivialZeroSet) →
      ∑ ρ ∈ S, 1 / (1 + ρ.im ^ 2) ≤ B :=
  RiemannHypothesis.sum_inv_one_add_im_sq_le

example : Summable (fun ρ : RiemannHypothesis.nontrivialZeroSet => 1 / (1 + ((ρ : ℂ).im) ^ 2)) :=
  RiemannHypothesis.summable_inv_one_add_im_sq

example : Summable (fun ρ : RiemannHypothesis.nontrivialZeroSet => 1 / (1 + ‖(ρ : ℂ)‖ ^ 2)) :=
  RiemannHypothesis.summable_inv_one_add_norm_sq

example : Summable (fun ρ : RiemannHypothesis.nontrivialZeroSet => 1 / ‖(ρ : ℂ)‖ ^ 2) :=
  RiemannHypothesis.summable_inv_norm_sq

/-! ## M2-ZERO-EXISTS -/

example : ∀ (f : ℂ → ℂ), Differentiable ℂ f → (∀ z, f z ≠ 0) →
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) :=
  fun _f hf hne => RiemannHypothesis.exists_exp_of_ne_zero hf hne

example : ∀ (g : ℂ → ℂ), Differentiable ℂ g → ∀ (C D : ℝ), 0 ≤ C → 0 ≤ D →
    (∀ z : ℂ, (g z).re ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) + D) →
      ∃ a b : ℂ, ∀ z : ℂ, g z = a + b * z :=
  fun _g hg _C _D hC hD hre => RiemannHypothesis.linear_of_re_le hg hC hD hre

example : ∀ (n : ℕ), 1 ≤ n →
    (Real.pi)⁻¹ ^ (n + 1) * (Nat.factorial n : ℝ) ≤ ‖RiemannHypothesis.xiFn (2 * ((n : ℂ) + 1))‖ :=
  fun n hn => RiemannHypothesis.factorial_le_norm_xiFn n hn

example : ∃ s : ℂ, RiemannHypothesis.xiFn s = 0 :=
  RiemannHypothesis.exists_xiFn_eq_zero

example : RiemannHypothesis.nontrivialZeroSet.Nonempty :=
  RiemannHypothesis.nontrivialZeroSet_nonempty

example : ∃ s : ℂ, riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 :=
  RiemannHypothesis.exists_riemannZeta_eq_zero_of_mem_strip

/-! ## M2-ZERO-INFINITE -/

example (m : Multiset ℂ) (z : ℂ) :
    RiemannHypothesis.rootProd m z = (m.map (fun ρ => z - ρ)).prod := rfl

example : ∀ (f : ℂ → ℂ), Differentiable ℂ f → ∀ (w : ℂ), f w ≠ 0 → ∀ (S : Finset ℂ),
    (∀ z, f z = 0 → z ∈ S) →
      ∃ (m : Multiset ℂ) (g : ℂ → ℂ), (∀ ρ ∈ m, ρ ∈ S) ∧ Differentiable ℂ g ∧
        (∀ z, g z ≠ 0) ∧ ∀ z, f z = RiemannHypothesis.rootProd m z * g z :=
  fun _f hf _w hw S hS => RiemannHypothesis.exists_rootMultiset_factorization hf hw S hS

example : ∀ {s : ℂ}, RiemannHypothesis.xiFn s = 0 ↔ s ∈ RiemannHypothesis.nontrivialZeroSet :=
  RiemannHypothesis.xiFn_eq_zero_iff_mem_nontrivialZeroSet

example : RiemannHypothesis.nontrivialZeroSet.Infinite :=
  RiemannHypothesis.infinite_nontrivialZeroSet

example : {s : ℂ | RiemannHypothesis.xiFn s = 0}.Infinite :=
  RiemannHypothesis.infinite_setOf_xiFn_eq_zero

/-! ## M2-ZERO-COUNT-LOWER -/

example : Monotone fun T : ℝ => (RiemannHypothesis.nontrivialZeros T).ncard :=
  RiemannHypothesis.monotone_ncard_nontrivialZeros

example : ∀ T : ℝ, ∃ s ∈ RiemannHypothesis.nontrivialZeroSet, T < |s.im| :=
  RiemannHypothesis.exists_mem_nontrivialZeroSet_lt_abs_im

example : ∀ n : ℕ, ∃ T : ℝ, 0 ≤ T ∧ n ≤ (RiemannHypothesis.nontrivialZeros T).ncard :=
  RiemannHypothesis.exists_le_ncard_nontrivialZeros

example : Filter.Tendsto (fun T : ℝ => ((RiemannHypothesis.nontrivialZeros T).ncard : ℝ))
    Filter.atTop Filter.atTop :=
  RiemannHypothesis.tendsto_ncard_nontrivialZeros_atTop

/-! ## M2-ZERO-SYMMETRY-COUNT -/

example : ∀ {s : ℂ}, s ∈ RiemannHypothesis.nontrivialZeroSet → s.im ≠ 0 :=
  RiemannHypothesis.im_ne_zero_of_mem_nontrivialZeroSet

example : ∀ {s : ℂ}, s ∈ RiemannHypothesis.nontrivialZeroSet →
    (starRingEnd ℂ) s ∈ RiemannHypothesis.nontrivialZeroSet :=
  RiemannHypothesis.conj_mem_nontrivialZeroSet

example : ∀ {s : ℂ}, s ∈ RiemannHypothesis.nontrivialZeroSet →
    1 - s ∈ RiemannHypothesis.nontrivialZeroSet :=
  RiemannHypothesis.one_sub_mem_nontrivialZeroSet

example : RiemannHypothesis.upperNontrivialZeroSet =
    {s : ℂ | s ∈ RiemannHypothesis.nontrivialZeroSet ∧ 0 < s.im} := rfl

example : RiemannHypothesis.lowerNontrivialZeroSet =
    {s : ℂ | s ∈ RiemannHypothesis.nontrivialZeroSet ∧ s.im < 0} := rfl

example (T : ℝ) : RiemannHypothesis.upperNontrivialZeros T =
    {s : ℂ | s ∈ RiemannHypothesis.nontrivialZeros T ∧ 0 < s.im} := rfl

example : (starRingEnd ℂ) '' RiemannHypothesis.upperNontrivialZeroSet =
    RiemannHypothesis.lowerNontrivialZeroSet :=
  RiemannHypothesis.conj_image_upperNontrivialZeroSet

example : RiemannHypothesis.upperNontrivialZeroSet.Infinite :=
  RiemannHypothesis.infinite_upperNontrivialZeroSet

example : RiemannHypothesis.lowerNontrivialZeroSet.Infinite :=
  RiemannHypothesis.infinite_lowerNontrivialZeroSet

example : ∀ T : ℝ, (RiemannHypothesis.nontrivialZeros T).ncard =
    2 * (RiemannHypothesis.upperNontrivialZeros T).ncard :=
  RiemannHypothesis.ncard_nontrivialZeros_eq_two_mul

example : ∀ T : ℝ, Even (RiemannHypothesis.nontrivialZeros T).ncard :=
  RiemannHypothesis.even_ncard_nontrivialZeros

/-! ## M2-OFF-LINE-QUADRUPLE -/

example (T : ℝ) : RiemannHypothesis.offLineNontrivialZeros T =
    {s : ℂ | s ∈ RiemannHypothesis.nontrivialZeros T ∧ s.re ≠ 1 / 2} := rfl

example (T : ℝ) : RiemannHypothesis.leftUpperNontrivialZeros T =
    {s : ℂ | s ∈ RiemannHypothesis.nontrivialZeros T ∧ s.re < 1 / 2 ∧ 0 < s.im} := rfl

example (s : ℂ) : RiemannHypothesis.criticalReflect s = 1 - (starRingEnd ℂ) s := rfl

example : ∀ {T : ℝ} {s : ℂ}, s ∈ RiemannHypothesis.nontrivialZeros T →
    RiemannHypothesis.criticalReflect s ∈ RiemannHypothesis.nontrivialZeros T :=
  RiemannHypothesis.criticalReflect_mem_nontrivialZeros

example : ∀ {T : ℝ} {s : ℂ}, s ∈ RiemannHypothesis.nontrivialZeros T → s.re ≠ 1 / 2 →
    (((starRingEnd ℂ) s ∈ RiemannHypothesis.nontrivialZeros T ∧
        (1 - s) ∈ RiemannHypothesis.nontrivialZeros T ∧
        RiemannHypothesis.criticalReflect s ∈ RiemannHypothesis.nontrivialZeros T) ∧
      (((starRingEnd ℂ) s).re ≠ 1 / 2 ∧ (1 - s).re ≠ 1 / 2 ∧
        (RiemannHypothesis.criticalReflect s).re ≠ 1 / 2) ∧
      (s ≠ (starRingEnd ℂ) s ∧ s ≠ 1 - s ∧ s ≠ RiemannHypothesis.criticalReflect s ∧
        (starRingEnd ℂ) s ≠ 1 - s ∧
        (starRingEnd ℂ) s ≠ RiemannHypothesis.criticalReflect s ∧
        1 - s ≠ RiemannHypothesis.criticalReflect s)) :=
  fun hs hre => RiemannHypothesis.offLineQuadruple_distinct hs hre

example : ∀ T : ℝ, (RiemannHypothesis.offLineNontrivialZeros T).ncard =
    4 * (RiemannHypothesis.leftUpperNontrivialZeros T).ncard :=
  RiemannHypothesis.ncard_offLineNontrivialZeros_eq_four_mul

example : ∀ T : ℝ, 4 ∣ (RiemannHypothesis.offLineNontrivialZeros T).ncard :=
  RiemannHypothesis.four_dvd_ncard_offLineNontrivialZeros

example : ∀ {T : ℝ} {s : ℂ}, s ∈ RiemannHypothesis.nontrivialZeros T → s.re ≠ 1 / 2 →
    4 ≤ (RiemannHypothesis.offLineNontrivialZeros T).ncard :=
  fun hs hre => RiemannHypothesis.four_le_ncard_offLineNontrivialZeros hs hre

/-! ## M2-MULTIPLICITY-SYMMETRY -/

example (f : ℂ → ℂ) (z₀ : ℂ) :
    analyticOrderAt (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) ((starRingEnd ℂ) z₀)
      = analyticOrderAt f z₀ :=
  RiemannHypothesis.analyticOrderAt_conj_conj f z₀

example : ∀ {s : ℂ}, 0 < s.re → s.re < 1 →
    analyticOrderAt completedRiemannZeta s = analyticOrderAt riemannZeta s :=
  RiemannHypothesis.analyticOrderAt_completedRiemannZeta_eq

example : ∀ {s : ℂ}, 0 < s.re → s.re < 1 →
    RiemannHypothesis.zeroMultiplicity ((starRingEnd ℂ) s) = RiemannHypothesis.zeroMultiplicity s :=
  RiemannHypothesis.zeroMultiplicity_conj

example : ∀ {s : ℂ}, 0 < s.re → s.re < 1 →
    RiemannHypothesis.zeroMultiplicity (1 - s) = RiemannHypothesis.zeroMultiplicity s :=
  RiemannHypothesis.zeroMultiplicity_one_sub

example : ∀ {s : ℂ}, 0 < s.re → s.re < 1 →
    RiemannHypothesis.zeroMultiplicity (RiemannHypothesis.criticalReflect s)
      = RiemannHypothesis.zeroMultiplicity s :=
  RiemannHypothesis.zeroMultiplicity_criticalReflect

example (T : ℝ) : RiemannHypothesis.multCount T =
    ∑ᶠ ρ ∈ RiemannHypothesis.nontrivialZeros T, RiemannHypothesis.zeroMultiplicity ρ := rfl

example (T : ℝ) : RiemannHypothesis.offLineMultCount T =
    ∑ᶠ ρ ∈ RiemannHypothesis.offLineNontrivialZeros T, RiemannHypothesis.zeroMultiplicity ρ := rfl

example : ∀ T : ℝ, Even (RiemannHypothesis.multCount T) :=
  RiemannHypothesis.even_multCount

example : ∀ T : ℝ, RiemannHypothesis.offLineMultCount T =
    4 * ∑ᶠ ρ ∈ RiemannHypothesis.leftUpperNontrivialZeros T,
      RiemannHypothesis.zeroMultiplicity ρ :=
  RiemannHypothesis.offLineMultCount_eq_four_mul

example : ∀ T : ℝ, 4 ∣ RiemannHypothesis.offLineMultCount T :=
  RiemannHypothesis.four_dvd_offLineMultCount

/-! ## M1-TWO-THIRDS — the counting functions and the two-thirds theorems -/

example (ρ : ℂ) : RiemannHypothesis.zeroMultiplicity ρ = (analyticOrderAt riemannZeta ρ).toNat :=
  rfl

example (T₁ T₂ : ℝ) : RiemannHypothesis.windowZeros T₁ T₂ =
    {ρ ∈ RiemannHypothesis.nontrivialZeroSet | T₁ < ρ.im ∧ ρ.im ≤ T₂} := rfl

example (T₁ T₂ : ℝ) : RiemannHypothesis.windowCount T₁ T₂ =
    ∑ᶠ ρ ∈ RiemannHypothesis.windowZeros T₁ T₂, RiemannHypothesis.zeroMultiplicity ρ := rfl

example (T₁ T₂ : ℝ) : RiemannHypothesis.windowCountDistinct T₁ T₂ =
    (RiemannHypothesis.windowZeros T₁ T₂).ncard := rfl

example (T₁ T₂ : ℝ) : RiemannHypothesis.windowCountOnLine T₁ T₂ =
    (RiemannHypothesis.windowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2}).ncard := rfl

example (T₁ T₂ : ℝ) : RiemannHypothesis.windowCountSimpleOnLine T₁ T₂ =
    (RiemannHypothesis.windowZeros T₁ T₂ ∩ {ρ : ℂ | ρ.re = 1 / 2} ∩
      {ρ : ℂ | RiemannHypothesis.zeroMultiplicity ρ = 1}).ncard := rfl

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (2 / 3 - ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountOnLine T (2 * T) :=
  RiemannHypothesis.two_thirds_on_critical_line

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (2 / 3 - ε) * (RiemannHypothesis.windowCount 0 T : ℝ) ≤
      RiemannHypothesis.windowCountOnLine 0 T :=
  RiemannHypothesis.two_thirds_on_critical_line_cumulative

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (2 / 3 - ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountSimpleOnLine T (2 * T) :=
  RiemannHypothesis.two_thirds_simple_on_critical_line

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (2 / 3 - ε) * (RiemannHypothesis.windowCount 0 T : ℝ) ≤
      RiemannHypothesis.windowCountSimpleOnLine 0 T :=
  RiemannHypothesis.two_thirds_simple_on_critical_line_cumulative

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (5 / 6 - ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountDistinct T (2 * T) :=
  RiemannHypothesis.five_sixths_distinct

example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    0.8 * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountDistinct T (2 * T) :=
  RiemannHypothesis.eighty_percent_distinct

/-! ## M1-SIMPLE-EIGHTY — eighty per cent of the distinct zeroes are simple -/

example : RiemannHypothesis.windowCountSimple = fun T₁ T₂ =>
    (RiemannHypothesis.windowZeros T₁ T₂ ∩
      {ρ : ℂ | RiemannHypothesis.zeroMultiplicity ρ = 1}).ncard := rfl

example (T₁ T₂ : ℝ) :
    2 * RiemannHypothesis.windowCountDistinct T₁ T₂ ≤
      RiemannHypothesis.windowCountSimple T₁ T₂ + RiemannHypothesis.windowCount T₁ T₂ :=
  RiemannHypothesis.two_mul_windowCountDistinct_le_add T₁ T₂

example : 3 / 4 < RiemannHypothesis.mtConstant :=
  RiemannHypothesis.mtConstant_gt_three_quarters

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (4 / 5 - ε) * (RiemannHypothesis.windowCountDistinct T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountSimple T (2 * T) :=
  RiemannHypothesis.four_fifths_simple_among_distinct

example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    0.8 * (RiemannHypothesis.windowCountDistinct T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountSimple T (2 * T) :=
  RiemannHypothesis.eighty_percent_simple_among_distinct

example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    0.8 * (RiemannHypothesis.windowCountDistinct 0 T : ℝ) ≤
      RiemannHypothesis.windowCountSimple 0 T :=
  RiemannHypothesis.eighty_percent_simple_among_distinct_cumulative

example : 4 / 5 ≤ liminf (fun T : ℝ =>
    (RiemannHypothesis.windowCountSimple 0 T : ℝ) /
      (RiemannHypothesis.windowCountDistinct 0 T : ℝ)) atTop :=
  RiemannHypothesis.four_fifths_le_liminf_windowCountSimple_div_windowCountDistinct

example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    0.92 * (RiemannHypothesis.xiDerivWindowCountDistinct T (2 * T) : ℝ) ≤
      RiemannHypothesis.xiDerivWindowCountSimple T (2 * T) :=
  RiemannHypothesis.ninety_two_percent_simple_among_distinct_xiDeriv

example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    0.92 * (RiemannHypothesis.xiDerivWindowCountDistinct 0 T : ℝ) ≤
      RiemannHypothesis.xiDerivWindowCountSimple 0 T :=
  RiemannHypothesis.ninety_two_percent_simple_among_distinct_xiDeriv_cumulative

example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      0.8 * (RiemannHypothesis.windowCountDistinctL χ T (2 * T) : ℝ) ≤
        RiemannHypothesis.windowCountSimpleL χ T (2 * T) :=
  RiemannHypothesis.eighty_percent_simple_among_distinctL χ hq hχ

-- the open target is a statement only, and it is the intended one
example : RiemannHypothesis.EightyPercentOnCriticalLine =
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 / 5 - ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
        RiemannHypothesis.windowCountOnLine T (2 * T) := rfl

example (h : RiemannHypothesis.EightyPercentOnCriticalLine) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (RiemannHypothesis.windowCountOffLine T (2 * T) : ℝ) ≤
        (1 / 5 + ε) * RiemannHypothesis.windowCount T (2 * T) :=
  RiemannHypothesis.one_fifth_off_critical_line_of_eightyPercent h

/-! ## M1-HARDY — Hardy's theorem -/

example : RiemannHypothesis.criticalLineZeroSet =
    {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2} := rfl

example : RiemannHypothesis.simpleCriticalLineZeroSet =
    {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ RiemannHypothesis.zeroMultiplicity ρ = 1} := rfl

example : Tendsto (fun T : ℝ => (RiemannHypothesis.windowCount 0 T : ℝ)) atTop atTop :=
  RiemannHypothesis.tendsto_windowCount_atTop

example : Tendsto (fun T : ℝ => (RiemannHypothesis.windowCountOnLine 0 T : ℝ)) atTop atTop :=
  RiemannHypothesis.tendsto_windowCountOnLine_atTop

example : Tendsto (fun T : ℝ => (RiemannHypothesis.windowCountSimpleOnLine 0 T : ℝ)) atTop atTop :=
  RiemannHypothesis.tendsto_windowCountSimpleOnLine_atTop

example : {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2}.Infinite :=
  RiemannHypothesis.infinite_criticalLineZeroSet

example : {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧
    RiemannHypothesis.zeroMultiplicity ρ = 1}.Infinite :=
  RiemannHypothesis.infinite_simpleCriticalLineZeroSet

example : Infinite {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2} :=
  RiemannHypothesis.hardyTheorem

/-! ## M2-SELBERG, M2-LEVINSON, M2-CONREY — the proportions on the line -/

example : ∃ c > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    c * (RiemannHypothesis.windowCount 0 T : ℝ) ≤ RiemannHypothesis.windowCountOnLine 0 T :=
  RiemannHypothesis.selberg_positive_proportion

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (1 / 3 - ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountOnLine T (2 * T) :=
  RiemannHypothesis.levinson_one_third

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (2 / 5 - ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountOnLine T (2 * T) :=
  RiemannHypothesis.conrey_two_fifths

example : 0 < liminf (fun T : ℝ =>
    (RiemannHypothesis.criticalZeroCount T : ℝ) / (RiemannHypothesis.zeroCount T : ℝ)) atTop :=
  RiemannHypothesis.positiveProportionOnCriticalLine

example : (2 / 5 : ℝ) ≤ liminf (fun T : ℝ =>
    (RiemannHypothesis.criticalZeroCount T : ℝ) / (RiemannHypothesis.zeroCount T : ℝ)) atTop :=
  RiemannHypothesis.twoFifthsOnCriticalLine

example : (2 / 3 : ℝ) ≤ liminf (fun T : ℝ =>
    (RiemannHypothesis.criticalZeroCount T : ℝ) / (RiemannHypothesis.zeroCount T : ℝ)) atTop :=
  RiemannHypothesis.twoThirds_le_liminf_criticalZeroCount_div

/-! ## M1-PNT — the prime number theorem -/

example : ∃ c > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
    fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) :=
  RiemannHypothesis.chebyshev_psi_sub_id_isBigO

example : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) :=
  RiemannHypothesis.chebyshev_psi_div_tendsto_one

example : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) :=
  RiemannHypothesis.chebyshev_theta_div_tendsto_one

example : Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (nhds 1) :=
  RiemannHypothesis.prime_number_theorem

/-! ## M1-CRITICAL-LINE-ORDINATES — where the zeroes on the line are -/

example : ∀ T : ℝ, ∃ s ∈ RiemannHypothesis.criticalLineZeroSet, T < s.im :=
  RiemannHypothesis.exists_mem_criticalLineZeroSet_lt_im

example : ∀ T : ℝ, ∃ s ∈ RiemannHypothesis.simpleCriticalLineZeroSet, T < s.im :=
  RiemannHypothesis.exists_mem_simpleCriticalLineZeroSet_lt_im

example : ∀ T : ℝ, ∃ s ∈ RiemannHypothesis.criticalLineZeroSet, s.im < T :=
  RiemannHypothesis.exists_mem_criticalLineZeroSet_im_lt

example : {t : ℝ | RiemannHypothesis.riemannXi (t : ℂ) = 0}.Infinite :=
  RiemannHypothesis.infinite_setOf_riemannXi_ofReal_eq_zero

example : ∀ T : ℝ, ∃ t : ℝ, T < t ∧ RiemannHypothesis.riemannXi (t : ℂ) = 0 :=
  RiemannHypothesis.exists_riemannXi_ofReal_eq_zero_lt

example : ∀ T : ℝ, ∃ t : ℝ, t < T ∧ RiemannHypothesis.riemannXi (t : ℂ) = 0 :=
  RiemannHypothesis.exists_riemannXi_ofReal_eq_zero_gt

example : ¬ BddAbove {t : ℝ | RiemannHypothesis.riemannXi (t : ℂ) = 0} :=
  RiemannHypothesis.not_bddAbove_setOf_riemannXi_ofReal_eq_zero

example : ¬ BddBelow {t : ℝ | RiemannHypothesis.riemannXi (t : ℂ) = 0} :=
  RiemannHypothesis.not_bddBelow_setOf_riemannXi_ofReal_eq_zero

/-! ## M1-OFF-LINE — at most a third of the zeroes lie off the critical line -/

example : ∀ T₁ T₂ : ℝ,
    RiemannHypothesis.windowCountOffLine T₁ T₂ + RiemannHypothesis.windowCountOnLine T₁ T₂
      = RiemannHypothesis.windowCountDistinct T₁ T₂ :=
  RiemannHypothesis.windowCountOffLine_add_windowCountOnLine

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (RiemannHypothesis.windowCountOffLine T (2 * T) : ℝ) ≤
      (1 / 3 + ε) * RiemannHypothesis.windowCount T (2 * T) :=
  RiemannHypothesis.one_third_off_critical_line

example : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (RiemannHypothesis.windowCountOffLine 0 T : ℝ) ≤
      (1 / 3 + ε) * RiemannHypothesis.windowCount 0 T :=
  RiemannHypothesis.one_third_off_critical_line_cumulative

example : ∀ T : ℝ,
    RiemannHypothesis.offCriticalZeroCount T + RiemannHypothesis.criticalZeroCount T
      = RiemannHypothesis.zeroCount T :=
  RiemannHypothesis.offCriticalZeroCount_add_criticalZeroCount

example : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
    (RiemannHypothesis.offCriticalZeroCount T : ℝ) ≤
      (1 / 3 + ε) * RiemannHypothesis.zeroCount T :=
  RiemannHypothesis.eventually_offCriticalZeroCount_le

example : limsup (fun T : ℝ =>
      (RiemannHypothesis.offCriticalZeroCount T : ℝ) / (RiemannHypothesis.zeroCount T : ℝ))
      atTop ≤ 1 / 3 :=
  RiemannHypothesis.limsup_offCriticalZeroCount_div_le_one_third

/-! ## M1-SIXTY-SEVEN-CRITICAL — the `ε`-free 67 % on the critical line -/

example {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 :=
  RiemannHypothesis.cos_le_one_sub_sq_div_two_add_pow_four_div_24 hx

example : 44 * Real.sqrt 2 / 73 < Real.tan (1 / Real.sqrt 2) :=
  RiemannHypothesis.tan_one_div_sqrt_two_gt_quartic

example : 88 / 117 < RiemannHypothesis.mtConstant :=
  RiemannHypothesis.mtConstant_gt_eightyEight_div_117

example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    0.67 * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountOnLine T (2 * T) :=
  RiemannHypothesis.sixty_seven_percent_on_critical_line

example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    0.67 * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
      RiemannHypothesis.windowCountSimpleOnLine T (2 * T) :=
  RiemannHypothesis.sixty_seven_percent_simple_on_critical_line

example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    0.67 * (RiemannHypothesis.windowCount 0 T : ℝ) ≤
      RiemannHypothesis.windowCountSimpleOnLine 0 T :=
  RiemannHypothesis.sixty_seven_percent_simple_on_critical_line_cumulative

example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (RiemannHypothesis.windowCountOffLine T (2 * T) : ℝ) ≤
      0.33 * RiemannHypothesis.windowCount T (2 * T) :=
  RiemannHypothesis.thirty_three_percent_off_critical_line

/-! ## M1-EIGHTY-CRITICAL-ROUTE — the conditional route through the zeroes of `ξ′`

The hypothesis `SpeiserTransfer` is pinned as a statement: it is a `def … : Prop`, never a
theorem, and the results below all carry it as an explicit argument. -/

example : RiemannHypothesis.SpeiserTransfer =
    ∃ C S : ℝ, ∀ T ≥ S,
      (RiemannHypothesis.windowCountOffLine T (2 * T) : ℝ) ≤
        RiemannHypothesis.xiDerivWindowCountBad T (2 * T) + C * Real.log T := rfl

example : ∃ C S : ℝ, 0 ≤ C ∧ 1 ≤ S ∧ ∀ T ≥ S,
    |(RiemannHypothesis.xiDerivWindowCount T (2 * T) : ℝ) -
        (RiemannHypothesis.windowCount T (2 * T) : ℝ)| ≤ C * Real.log T :=
  RiemannHypothesis.abs_xiDerivWindowCount_sub_windowCount_le

example (K : ℝ) : ∃ S : ℝ, 1 ≤ S ∧ ∀ T ≥ S,
    K * Real.log T ≤ (RiemannHypothesis.windowCount T (2 * T) : ℝ) :=
  RiemannHypothesis.exists_le_windowCount_mul_log K

example (ε : ℝ) (hε : 0 < ε) : ∃ S : ℝ, 1 ≤ S ∧ ∀ T ≥ S,
    (RiemannHypothesis.xiDerivWindowCount T (2 * T) : ℝ) ≤
      (1 + ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) :=
  RiemannHypothesis.xiDerivWindowCount_le_one_add_mul hε

example (h : RiemannHypothesis.SpeiserTransfer) : ∃ S : ℝ, ∀ T ≥ S,
    0.84 * (RiemannHypothesis.windowCountDistinct T (2 * T) : ℝ) ≤
      (RiemannHypothesis.windowCountOnLine T (2 * T) : ℝ) :=
  RiemannHypothesis.eighty_four_percent_distinct_on_critical_line_of_speiserTransfer h

example (h : RiemannHypothesis.SpeiserTransfer) : ∃ S : ℝ, ∀ T ≥ S,
    0.7 * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
      (RiemannHypothesis.windowCountOnLine T (2 * T) : ℝ) :=
  RiemannHypothesis.seventy_percent_on_critical_line_of_speiserTransfer h

example (h : RiemannHypothesis.SpeiserTransfer) :
    RiemannHypothesis.EightyPercentOnCriticalLineDistinct :=
  RiemannHypothesis.eightyPercentOnCriticalLineDistinct_of_speiserTransfer h

/-! ## M1-ZERO-FREE-REGION -/

example : RiemannHypothesis.ZeroFreeRegion = (∃ c : ℝ, 0 < c ∧
    ∀ s : ℂ, 3 ≤ |s.im| → 1 - c / Real.log |s.im| < s.re → riemannZeta s ≠ 0) := rfl

example : ∃ c : ℝ, 0 < c ∧
    ∀ s : ℂ, 3 ≤ |s.im| → 1 - c / Real.log |s.im| < s.re → riemannZeta s ≠ 0 :=
  RiemannHypothesis.zeroFreeRegion

example (s : ℂ) : RiemannHypothesis.negReLogDerivZeta s =
    (-(deriv riemannZeta s / riemannZeta s)).re := rfl

example {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * RiemannHypothesis.negReLogDerivZeta (σ : ℂ)
      + 4 * RiemannHypothesis.negReLogDerivZeta ((σ : ℂ) + (t : ℂ) * I)
      + RiemannHypothesis.negReLogDerivZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) :=
  RiemannHypothesis.three_four_one hσ t

example {σ a : ℝ} (ha : 0 < a) (hσ : 1 + a < σ) :
    RiemannHypothesis.negReLogDerivZeta (σ : ℂ) ≤ 1 / (σ - 1 - a) + (σ - 1) / a :=
  RiemannHypothesis.negReLogDerivZeta_real_le ha hσ

example : ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℝ, 4 ≤ t₀ ∧
    ∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ → t₀ ≤ |ρ.im| → ρ.re ≤ 1 - c / Real.log |ρ.im| :=
  RiemannHypothesis.exists_re_le_one_sub_of_nontrivialZero

/-! ## M1-ZERO-LOCATION-CLASSICAL -/

example : ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, riemannZeta s = 0 → 3 ≤ |s.im| →
    c / Real.log |s.im| ≤ s.re ∧ s.re ≤ 1 - c / Real.log |s.im| :=
  RiemannHypothesis.exists_zero_mem_shrinking_strip_classical

example : ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, riemannZeta s = 0 → 3 ≤ |s.im| →
    |s.re - 1 / 2| ≤ 1 / 2 - c / Real.log |s.im| :=
  RiemannHypothesis.exists_zero_abs_re_sub_half_le_classical

/-! ## M1-REDHEFFER -/

example (n : ℕ) (i j : Fin n) : RiemannHypothesis.redheffer n i j =
    if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0 := rfl

example {m : ℕ} (hm : 1 ≤ m) :
    ∑ d ∈ Finset.Icc 1 m, RiemannHypothesis.mertens (m / d) = 1 :=
  RiemannHypothesis.sum_mertens_div hm

example {n : ℕ} (hn : 1 ≤ n) :
    (RiemannHypothesis.redheffer n).det = RiemannHypothesis.mertens n :=
  RiemannHypothesis.det_redheffer hn

example : RiemannHypothesis.RedhefferBoundForm → RiemannHypothesis.ZetaForm :=
  RiemannHypothesis.zeta_of_redhefferBound

/-! ## M1-MERTENS-ELEMENTARY -/

example {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ((N / n : ℕ) : ℤ) * ArithmeticFunction.moebius n = 1 :=
  RiemannHypothesis.sum_moebius_mul_div hN

example (N : ℕ) : |RiemannHypothesis.littleMertens N| ≤ 1 :=
  RiemannHypothesis.abs_littleMertens_le_one N

example (N : ℕ) : RiemannHypothesis.littleMertens N =
    ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / n := rfl

/-! ## M2-WEIL-TESTFUNCTIONS -/

example (g : ℝ → ℂ) (x : ℝ) :
    RiemannHypothesis.starReflect g x = (starRingEnd ℂ) (g (-x)) := rfl

example (g : ℝ → ℂ) : RiemannHypothesis.weilSquare g =
    g ⋆[ContinuousLinearMap.mul ℂ ℂ, MeasureTheory.volume] RiemannHypothesis.starReflect g := rfl

example (k : ℝ → ℂ) (r : ℝ) :
    RiemannHypothesis.testTransform k (r : ℂ) = 𝓕 k (-(r / (2 * Real.pi))) :=
  RiemannHypothesis.testTransform_ofReal k r

example (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (RiemannHypothesis.starReflect g) ξ = (starRingEnd ℂ) (𝓕 g ξ) :=
  RiemannHypothesis.fourier_starReflect g ξ

example {g : ℝ → ℂ} (hg : MeasureTheory.Integrable g) (r : ℝ) :
    RiemannHypothesis.testTransform (RiemannHypothesis.weilSquare g) (r : ℂ)
      = ((‖𝓕 g (-(r / (2 * Real.pi)))‖ ^ 2 : ℝ) : ℂ) :=
  RiemannHypothesis.testTransform_weilSquare hg r

example (g : ℝ → ℂ) :
    RiemannHypothesis.weilSquare g 0 = ∫ t : ℝ, ((‖g t‖ ^ 2 : ℝ) : ℂ) :=
  RiemannHypothesis.weilSquare_zero g

example {g : ℝ → ℂ} (hg2 : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    RiemannHypothesis.IsPositiveTestFunction (RiemannHypothesis.weilSquare g) :=
  RiemannHypothesis.isPositiveTestFunction_weilSquare hg2 hgc

example : ∃ k : ℝ → ℂ, RiemannHypothesis.IsPositiveTestFunction k ∧ k ≠ 0 :=
  RiemannHypothesis.exists_isPositiveTestFunction_ne_zero

/-! ## M1-LIOUVILLE-ELEMENTARY -/

example {k : ℕ} (hk : k ≠ 0) :
    ∑ d ∈ k.divisors, ArithmeticFunction.liouville d = if IsSquare k then 1 else 0 :=
  RiemannHypothesis.sum_divisors_liouville hk

example (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((N / n : ℕ) : ℤ) * ArithmeticFunction.liouville n = Nat.sqrt N :=
  RiemannHypothesis.sum_liouville_mul_div N

example (N : ℕ) : RiemannHypothesis.littleLiouville N =
    ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ) / n := rfl

example (N : ℕ) : |RiemannHypothesis.littleLiouville N - (Nat.sqrt N : ℝ) / N| ≤ 1 :=
  RiemannHypothesis.abs_littleLiouville_sub_le_one N

/-! ## M1-MEAN-SQUARE -/

example (σ t : ℝ) : RiemannHypothesis.linePoint σ t = (σ : ℂ) + (t : ℂ) * Complex.I := rfl

example {θ : ℝ} (hθ : θ ≠ 0) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, Complex.exp ((θ * t : ℝ) * Complex.I)) / (T : ℂ))
      atTop (𝓝 0) :=
  RiemannHypothesis.oscAvg_tendsto_zero hθ

example {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ((‖riemannZeta (RiemannHypothesis.linePoint σ t)‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : ℕ × ℕ, (RiemannHypothesis.msCoeff σ p : ℂ) *
        Complex.exp ((RiemannHypothesis.msFreq p * t : ℝ) * Complex.I) :=
  RiemannHypothesis.normSq_riemannZeta_line_eq_tsum hσ t

example {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / T) atTop
      (𝓝 (riemannZeta ((2 * σ : ℝ) : ℂ)).re) :=
  RiemannHypothesis.meanSquareAvg_tendsto_riemannZeta hσ

example (A : ℕ → ℂ) (σ t : ℝ) : RiemannHypothesis.dirichletLineSum A σ t =
    ∑' n : ℕ, A n * (1 / ((n : ℂ) + 1) ^ RiemannHypothesis.linePoint σ t) := rfl

example (A : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    RiemannHypothesis.dirichletWeight A σ n = ‖A n‖ * ((n : ℝ) + 1) ^ (-σ) := rfl

example {A : ℕ → ℂ} {σ : ℝ} (hA : Summable (RiemannHypothesis.dirichletWeight A σ)) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, ‖RiemannHypothesis.dirichletLineSum A σ t‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, RiemannHypothesis.dirichletWeight A σ n ^ 2)) :=
  RiemannHypothesis.meanSquareAvg_tendsto_tsum_of_summable hA

example {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) ^ 2 *
        ((n : ℝ) + 1) ^ (-(2 * σ)))) :=
  RiemannHypothesis.meanSquareAvg_tendsto_tsum_moebius hσ

example {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (RiemannHypothesis.divisorCount n : ℂ)) s = riemannZeta s ^ 2 :=
  RiemannHypothesis.lseries_divisorCount hs

example (n : ℕ) : RiemannHypothesis.divisorCount n = n.divisors.card := rfl

example {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4) / T) atTop
      (𝓝 (∑' n : ℕ, ((RiemannHypothesis.divisorCount (n + 1) : ℝ)) ^ 2 *
        ((n : ℝ) + 1) ^ (-(2 * σ)))) :=
  RiemannHypothesis.fourthMomentAvg_tendsto_tsum_divisorCount hσ

example (k : ℕ) (n : ℕ) :
    RiemannHypothesis.divisorCountK k n = (ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n :=
  rfl

example (n : ℕ) : RiemannHypothesis.divisorCountK 2 n = n.divisors.card :=
  RiemannHypothesis.divisorCountK_two n

example (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (RiemannHypothesis.divisorCountK k n : ℂ)) s = riemannZeta s ^ k :=
  RiemannHypothesis.lseries_divisorCountK k hs

example (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ (2 * k)) / T) atTop
      (𝓝 (∑' n : ℕ, ((RiemannHypothesis.divisorCountK k (n + 1) : ℝ)) ^ 2 *
        ((n : ℝ) + 1) ^ (-(2 * σ)))) :=
  RiemannHypothesis.momentAvg_tendsto_tsum_divisorCountK k hσ

example {f : ℝ → ℝ} {L ε : ℝ} (hf : ∀ T : ℝ, IntervalIntegrable f MeasureTheory.volume 0 T)
    (havg : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, f t) / T) atTop (𝓝 L)) (hε : 0 < ε) :
    ∃ᶠ t in atTop, L - ε < f t :=
  RiemannHypothesis.frequently_gt_sub_of_avg_tendsto hf havg hε

example {σ : ℝ} (hσ : 1 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ t : ℝ in atTop, (riemannZeta ((2 * σ : ℝ) : ℂ)).re - ε
      < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
  RiemannHypothesis.frequently_normSq_riemannZeta_gt hσ hε

example {σ : ℝ} (hσ : 1 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ t : ℝ in atTop, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      < (riemannZeta ((2 * σ : ℝ) : ℂ)).re + ε :=
  RiemannHypothesis.frequently_normSq_riemannZeta_lt hσ hε

/-! ## M1-ZERO-MULTIPLICITY — the multiplicity of a nontrivial zero is O(log |gamma|) -/

example {f : ℂ → ℂ} {c a : ℂ} {R M : ℝ} {m : ℕ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball c R)) (hM : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M)
    (ha : dist a c ≤ R / 4) (hord : (m : ℕ∞) ≤ analyticOrderAt f a) :
    3 ^ m * ‖f c‖ ≤ M :=
  RiemannHypothesis.pow_three_pow_mul_norm_le hR hf hM ha hord

example {f : ℂ → ℂ} {c a : ℂ} {R M : ℝ} {m : ℕ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball c R)) (hM : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M)
    (hc : f c ≠ 0) (ha : dist a c ≤ R / 4) (hord : (m : ℕ∞) ≤ analyticOrderAt f a) :
    (m : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log 3 :=
  RiemannHypothesis.analyticOrder_le_log_div_log_three hR hf hM hc ha hord

example {f : ℂ → ℂ} {c a : ℂ} {R : ℝ} {m : ℕ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball c R)) (ha : a ∈ Metric.ball c R)
    (hord : (m : ℕ∞) ≤ analyticOrderAt f a) :
    ∃ G : ℂ → ℂ, DiffContOnCl ℂ G (Metric.ball c R) ∧ ∀ z, z ≠ a → G z = f z / (z - a) ^ m :=
  RiemannHypothesis.exists_divided hR hf ha hord

example {c : ℂ} {R : ℝ} (hR : 0 < R) (S : Finset ℂ) :
    ∀ (f : ℂ → ℂ) (M : ℝ) (m : ℂ → ℕ), DiffContOnCl ℂ f (Metric.ball c R) →
      (∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) → (∀ a ∈ S, dist a c ≤ R / 4) →
      (∀ a ∈ S, (m a : ℕ∞) ≤ analyticOrderAt f a) →
      3 ^ (∑ a ∈ S, m a) * ‖f c‖ ≤ M :=
  RiemannHypothesis.pow_three_sum_mul_norm_le hR S

example {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} {m : ℂ → ℕ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hM : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M)
    (hc : f c ≠ 0) (S : Finset ℂ) (hdist : ∀ a ∈ S, dist a c ≤ R / 4)
    (hord : ∀ a ∈ S, (m a : ℕ∞) ≤ analyticOrderAt f a) :
    ((∑ a ∈ S, m a : ℕ) : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log 3 :=
  RiemannHypothesis.sum_analyticOrder_le_log_div_log_three hR hf hM hc S hdist hord

example : ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 2 ≤ T → ∃ M : ℝ, 0 < M ∧
      (∀ z ∈ Metric.sphere (2 : ℂ) (4 * (T + 2)), ‖RiemannHypothesis.xiFn z‖ ≤ M) ∧
      Real.log (M / ‖RiemannHypothesis.xiFn 2‖) / Real.log 3 ≤ A * T * Real.log T :=
  RiemannHypothesis.exists_global_disc_bound

example {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderAt RiemannHypothesis.xiFn s = analyticOrderAt riemannZeta s :=
  RiemannHypothesis.analyticOrderAt_xiFn_eq h0 h1

example {T : ℝ} (hT : 25 ≤ T) {ρ : ℂ} (hρ : ρ ∈ RiemannHypothesis.zerosNearHeight T) :
    (RiemannHypothesis.zeroMultiplicity ρ : ℝ) ≤ 41 * Real.log T :=
  RiemannHypothesis.zeroMultiplicity_le_of_mem_zerosNearHeight hT hρ

example {ρ : ℂ} (hρ : ρ ∈ RiemannHypothesis.nontrivialZeroSet) (him : 25 ≤ |ρ.im|) :
    (RiemannHypothesis.zeroMultiplicity ρ : ℝ) ≤ 41 * Real.log |ρ.im| :=
  RiemannHypothesis.zeroMultiplicity_le_log_abs_im hρ him

example : ∃ K : ℝ, 0 < K ∧ ∀ ρ ∈ RiemannHypothesis.nontrivialZeroSet, |ρ.im| ≤ 25 →
      (RiemannHypothesis.zeroMultiplicity ρ : ℝ) ≤ K :=
  RiemannHypothesis.exists_zeroMultiplicity_bound_low

example : ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 25 ≤ T → ∀ ρ ∈ RiemannHypothesis.nontrivialZeros T,
      (RiemannHypothesis.zeroMultiplicity ρ : ℝ) ≤ K * Real.log T :=
  RiemannHypothesis.exists_zeroMultiplicity_bound

example {T : ℝ} (hT : 25 ≤ T) : (RiemannHypothesis.zerosNearHeight T).Finite :=
  RiemannHypothesis.finite_zerosNearHeight hT

example {T : ℝ} (hT : 25 ≤ T) :
    ((∑ᶠ ρ ∈ RiemannHypothesis.zerosNearHeight T,
      RiemannHypothesis.zeroMultiplicity ρ : ℕ) : ℝ) ≤ 41 * Real.log T :=
  RiemannHypothesis.sum_zeroMultiplicity_zerosNearHeight_le hT

example : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (RiemannHypothesis.multCount T : ℝ) ≤ C * T * Real.log T :=
  RiemannHypothesis.multCount_le

/-! ## M1-SPEISER-MULTIPLE — the unconditional half of Speiser's transfer -/

example {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    RiemannHypothesis.xiDerivMultiplicity s + 1 = RiemannHypothesis.zeroMultiplicity s :=
  RiemannHypothesis.xiDerivMultiplicity_add_one h0 h1 hz

example {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0)
    (hm : 2 ≤ RiemannHypothesis.zeroMultiplicity s) : RiemannHypothesis.xiDerivFn s = 0 :=
  RiemannHypothesis.xiDerivFn_eq_zero_of_multiple h0 h1 hz hm

example {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0)
    (hm : RiemannHypothesis.zeroMultiplicity s = 1) : RiemannHypothesis.xiDerivFn s ≠ 0 :=
  RiemannHypothesis.xiDerivFn_ne_zero_of_simple h0 h1 hz hm

example (T₁ T₂ : ℝ) :
    RiemannHypothesis.windowZerosOffLineMultiple T₁ T₂ ⊆
      RiemannHypothesis.xiDerivWindowZerosOffLine T₁ T₂ :=
  RiemannHypothesis.windowZerosOffLineMultiple_subset T₁ T₂

example (T₁ T₂ : ℝ) :
    ((RiemannHypothesis.windowZerosOffLineMultiple T₁ T₂).ncard : ℝ) ≤
      RiemannHypothesis.xiDerivWindowCountBad T₁ T₂ :=
  RiemannHypothesis.ncard_windowZerosOffLineMultiple_le_bad T₁ T₂

example {ε : ℝ} (hε : 0 < ε) : ∃ S : ℝ, ∀ T ≥ S,
    ((RiemannHypothesis.windowZerosOffLineMultiple T (2 * T)).ncard : ℝ) ≤
      (0.13136 + ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) :=
  RiemannHypothesis.ncard_windowZerosOffLineMultiple_le_windowCount hε

example (T₁ T₂ : ℝ) : RiemannHypothesis.windowMultipleOffLineExcess T₁ T₂ =
    ∑ᶠ ρ ∈ RiemannHypothesis.windowZerosOffLineMultiple T₁ T₂,
      (RiemannHypothesis.zeroMultiplicity ρ - 1) := rfl

example {ε : ℝ} (hε : 0 < ε) : ∃ S : ℝ, ∀ T ≥ S,
    (RiemannHypothesis.windowMultipleOffLineExcess T (2 * T) : ℝ) ≤
      (0.13136 + ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) :=
  RiemannHypothesis.windowMultipleOffLineExcess_le_windowCount hε

/-! ## M1-SPEISER-ROLLE -/

example (t : ℝ) : RiemannHypothesis.onLine t = 1 / 2 + (t : ℂ) * I := rfl

example (t : ℝ) : RiemannHypothesis.XiReal t =
    (RiemannHypothesis.xiFn (RiemannHypothesis.onLine t)).re := rfl

example (t : ℝ) : HasDerivAt RiemannHypothesis.XiReal
    ((RiemannHypothesis.xiDerivFn (RiemannHypothesis.onLine t) * I).re) t :=
  RiemannHypothesis.hasDerivAt_XiReal t

example {a b : ℝ} (hab : a < b)
    (ha : RiemannHypothesis.xiFn (RiemannHypothesis.onLine a) = 0)
    (hb : RiemannHypothesis.xiFn (RiemannHypothesis.onLine b) = 0) :
    ∃ c ∈ Set.Ioo a b, RiemannHypothesis.xiDerivFn (RiemannHypothesis.onLine c) = 0 :=
  RiemannHypothesis.exists_xiDerivFn_onLine_eq_zero hab ha hb

example (T₁ T₂ : ℝ) :
    RiemannHypothesis.windowCountOffLineMult T₁ T₂ +
      RiemannHypothesis.windowCountOnLineMult T₁ T₂ = RiemannHypothesis.windowCount T₁ T₂ :=
  RiemannHypothesis.windowCountOffLineMult_add_windowCountOnLineMult T₁ T₂

example (T₁ T₂ : ℝ) :
    RiemannHypothesis.windowCountOnLineMult T₁ T₂ ≤
      RiemannHypothesis.xiDerivWindowCountOnLineMult T₁ T₂ + 1 :=
  RiemannHypothesis.windowCountOnLineMult_le_xiDerivWindowCountOnLineMult T₁ T₂

example : RiemannHypothesis.SpeiserOffLineTransfer ↔ RiemannHypothesis.XiDerivOnLineDominates :=
  RiemannHypothesis.speiserOffLineTransfer_iff_xiDerivOnLineDominates

example : ∃ C S : ℝ, ∀ T ≥ S,
    (RiemannHypothesis.xiDerivWindowCountOffLineMult T (2 * T) : ℝ) ≤
      (RiemannHypothesis.windowCountOffLineMult T (2 * T) : ℝ) + C * Real.log T :=
  RiemannHypothesis.xiDerivWindowCountOffLineMult_le_windowCountOffLineMult

example (h : RiemannHypothesis.SpeiserOffLineTransfer) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 - ε) * (RiemannHypothesis.windowCount T (2 * T) : ℝ) ≤
        (RiemannHypothesis.windowCountOnLineMult T (2 * T) : ℝ) :=
  RiemannHypothesis.eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer h

/-! ## M1-RECTANGLE-ARGUMENT-PRINCIPLE — the modulus half of Littlewood's lemma -/

example {f : ℂ → ℂ} {a b t : ℝ}
    (hf : ∀ σ ∈ Set.uIcc a b, AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ Set.uIcc a b, f ((σ : ℂ) + t * I) ≠ 0) :
    (∫ σ in a..b, (logDeriv f ((σ : ℂ) + t * I)).re)
      = Real.log ‖f ((b : ℂ) + t * I)‖ - Real.log ‖f ((a : ℂ) + t * I)‖ :=
  RiemannHypothesis.integral_re_logDeriv_horizontal hf h0

example {f : ℂ → ℂ} {σ c d : ℝ}
    (hf : ∀ t ∈ Set.uIcc c d, AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ t ∈ Set.uIcc c d, f ((σ : ℂ) + t * I) ≠ 0) :
    (∫ t in c..d, -(logDeriv f ((σ : ℂ) + t * I)).im)
      = Real.log ‖f ((σ : ℂ) + d * I)‖ - Real.log ‖f ((σ : ℂ) + c * I)‖ :=
  RiemannHypothesis.integral_im_logDeriv_vertical hf h0

/-! ## M1-ZETA-RECTANGLE-COUNT -/

example (z w : ℂ) :
    RiemannHypothesis.rectZeros RiemannHypothesis.xiFn z w =
      Rectangle z w ∩ RiemannHypothesis.nontrivialZeroSet :=
  RiemannHypothesis.rectZeros_xiFn_eq z w

example (z w : ℂ) : (RiemannHypothesis.rectZeros RiemannHypothesis.xiFn z w).Finite :=
  RiemannHypothesis.rectZeros_xiFn_finite z w

example {z w : ℂ} (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) :
    RiemannHypothesis.rectZeroCount riemannZeta z w =
      RiemannHypothesis.rectZeroCount RiemannHypothesis.xiFn z w :=
  RiemannHypothesis.rectZeroCount_riemannZeta_eq_xiFn hz0 hw1 hre

example {z w : ℂ} (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ _root_.RectangleBorder z w, riemannZeta s ≠ 0) :
    _root_.RectangleIntegral' (logDeriv riemannZeta) z w
      = (RiemannHypothesis.rectZeroCount riemannZeta z w : ℂ) :=
  RiemannHypothesis.zeta_rectangle_argument_principle hz0 hw1 hre him hborder

example {z w : ℂ} (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) :
    (∫ σ in z.re..w.re,
        (RiemannHypothesis.rectZeroCount riemannZeta
          (RiemannHypothesis.leftCorner σ z) w : ℝ))
      = ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros riemannZeta z w,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re) :=
  RiemannHypothesis.integral_rectZeroCount_riemannZeta_eq_finsum hz0 hw1 hre

example {z w : ℂ} (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ σ ∈ Set.Icc z.re w.re,
      ∀ s ∈ _root_.RectangleBorder (RiemannHypothesis.leftCorner σ z) w,
        riemannZeta s ≠ 0) :
    (∫ σ in z.re..w.re,
        (_root_.RectangleIntegral' (logDeriv riemannZeta)
          (RiemannHypothesis.leftCorner σ z) w).re)
      = ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros riemannZeta z w,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re) :=
  RiemannHypothesis.integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum hz0 hw1 hre him
    hborder

/-! ## M1-RECTANGLE-ARGUMENT-PRINCIPLE — the previous hypothesis is vacuous, and the fix

Asking `f` to be zero-free on the border of *every* truncation of the rectangle forces the
rectangle to contain no zero at all.  The corrected identity assumes zero-freeness only on the
border of the rectangle itself. -/

example {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (hborder : ∀ σ ∈ Set.Icc z.re w.re,
      ∀ s ∈ _root_.RectangleBorder (RiemannHypothesis.leftCorner σ z) w, f s ≠ 0) :
    RiemannHypothesis.rectZeros f z w = ∅ :=
  RiemannHypothesis.rectZeros_eq_empty_of_forall_leftCorner_border hre hborder

example {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ _root_.RectangleBorder z w, f s ≠ 0) :
    (∫ σ in z.re..w.re,
        (_root_.RectangleIntegral' (logDeriv f) (RiemannHypothesis.leftCorner σ z) w).re)
      = ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros f z w,
          (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re) :=
  RiemannHypothesis.integral_rectangleIntegral'_logDeriv_eq_finsum_of_border hre him hf hborder

example {z w : ℂ} (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ _root_.RectangleBorder z w, riemannZeta s ≠ 0) :
    (∫ σ in z.re..w.re,
        (_root_.RectangleIntegral' (logDeriv riemannZeta)
          (RiemannHypothesis.leftCorner σ z) w).re)
      = ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros riemannZeta z w,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re) :=
  RiemannHypothesis.integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum_of_border
    hz0 hw1 hre him hborder

/-! ## M1-RECTANGLE-ARGUMENT-PRINCIPLE — the modulus half, assembled around the border

The increments of `log ‖f‖` along the four sides telescope, so the real part of the contour
integral of `f'/f` vanishes and the normalized integral is real — assuming only analyticity and
nonvanishing on the border, nothing inside. -/

example {f : ℂ → ℂ} {z w : ℂ} (hf : ∀ s ∈ _root_.RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ _root_.RectangleBorder z w, f s ≠ 0) :
    (_root_.RectangleIntegral (logDeriv f) z w).re = 0 :=
  RiemannHypothesis.re_rectangleIntegral_logDeriv_eq_zero hf h0

example {f : ℂ → ℂ} {z w : ℂ} (hf : ∀ s ∈ _root_.RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ _root_.RectangleBorder z w, f s ≠ 0) :
    (_root_.RectangleIntegral' (logDeriv f) z w).im = 0 :=
  RiemannHypothesis.im_rectangleIntegral'_logDeriv_eq_zero hf h0

/-! ## M1-RECTANGLE-ARGUMENT-PRINCIPLE — the argument half, and Littlewood's lemma

A continuous branch of the argument of `g` along a segment is built by integrating `g'/g`, so
the winding number of `f` around the border of a rectangle is an integer; and Littlewood's lemma
turns the positions of the zeroes inside the rectangle into boundary data. -/

example {g g' : ℝ → ℂ} {a b : ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x) (h0 : ∀ x ∈ Set.uIcc a b, g x ≠ 0)
    (hc : ContinuousOn (fun x => g' x / g x) (Set.uIcc a b)) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Set.uIcc a b) ∧
      (∀ u ∈ Set.uIcc a b, g u = (‖g u‖ : ℂ) * Complex.exp (θ u * Complex.I)) ∧
      ∀ u ∈ Set.uIcc a b, ∀ v ∈ Set.uIcc a b,
        θ v - θ u = (∫ x in u..v, g' x / g x).im :=
  RiemannHypothesis.exists_continuousOn_arg hg h0 hc

example {f : ℂ → ℂ} {z w : ℂ} (hf : ∀ s ∈ _root_.RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ _root_.RectangleBorder z w, f s ≠ 0) :
    ∃ n : ℤ, _root_.RectangleIntegral' (logDeriv f) z w = (n : ℂ) :=
  RiemannHypothesis.exists_int_rectangleIntegral'_logDeriv hf h0

example {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ _root_.RectangleBorder z w, f s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros f z w,
        (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re)
      = (∫ t in z.im..w.im,
            (Real.log ‖f ((z.re : ℂ) + t * Complex.I)‖
              - Real.log ‖f ((w.re : ℂ) + t * Complex.I)‖))
        + (∫ σ in z.re..w.re, (_root_.HIntegral (logDeriv f) σ w.re z.im).im)
        - (∫ σ in z.re..w.re, (_root_.HIntegral (logDeriv f) σ w.re w.im).im)
        + (w.re - z.re) * (_root_.VIntegral (logDeriv f) w.re z.im w.im).im :=
  RiemannHypothesis.littlewood_lemma hre him hf hborder

example {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ _root_.RectangleBorder z w, f s ≠ 0) :
    ∃ θb θt : ℝ → ℝ, ContinuousOn θb (Set.uIcc z.re w.re) ∧
      ContinuousOn θt (Set.uIcc z.re w.re) ∧
      (∀ σ ∈ Set.uIcc z.re w.re, f ((σ : ℂ) + z.im * Complex.I)
        = (‖f ((σ : ℂ) + z.im * Complex.I)‖ : ℂ) * Complex.exp (θb σ * Complex.I)) ∧
      (∀ σ ∈ Set.uIcc z.re w.re, f ((σ : ℂ) + w.im * Complex.I)
        = (‖f ((σ : ℂ) + w.im * Complex.I)‖ : ℂ) * Complex.exp (θt σ * Complex.I)) ∧
      2 * Real.pi * ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros f z w,
          (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re)
        = (∫ t in z.im..w.im,
              (Real.log ‖f ((z.re : ℂ) + t * Complex.I)‖
                - Real.log ‖f ((w.re : ℂ) + t * Complex.I)‖))
          + (∫ σ in z.re..w.re, (θb w.re - θb σ))
          - (∫ σ in z.re..w.re, (θt w.re - θt σ))
          + (w.re - z.re) * (_root_.VIntegral (logDeriv f) w.re z.im w.im).im :=
  RiemannHypothesis.littlewood_lemma_arg hre him hf hborder

/-! ## M1-ZETA-RECTANGLE-COUNT — Littlewood's lemma for `ζ` -/

example {z w : ℂ} (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ _root_.RectangleBorder z w, riemannZeta s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros riemannZeta z w,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)
      = (∫ t in z.im..w.im,
            (Real.log ‖riemannZeta ((z.re : ℂ) + t * Complex.I)‖
              - Real.log ‖riemannZeta ((w.re : ℂ) + t * Complex.I)‖))
        + (∫ σ in z.re..w.re, (_root_.HIntegral (logDeriv riemannZeta) σ w.re z.im).im)
        - (∫ σ in z.re..w.re, (_root_.HIntegral (logDeriv riemannZeta) σ w.re w.im).im)
        + (w.re - z.re) * (_root_.VIntegral (logDeriv riemannZeta) w.re z.im w.im).im :=
  RiemannHypothesis.zeta_littlewood_lemma hz0 hw1 hre him hborder

example {z w : ℂ} (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ _root_.RectangleBorder z w, riemannZeta s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ Rectangle z w ∩ RiemannHypothesis.nontrivialZeroSet,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)
      = (∫ t in z.im..w.im,
            (Real.log ‖riemannZeta ((z.re : ℂ) + t * Complex.I)‖
              - Real.log ‖riemannZeta ((w.re : ℂ) + t * Complex.I)‖))
        + (∫ σ in z.re..w.re, (_root_.HIntegral (logDeriv riemannZeta) σ w.re z.im).im)
        - (∫ σ in z.re..w.re, (_root_.HIntegral (logDeriv riemannZeta) σ w.re w.im).im)
        + (w.re - z.re) * (_root_.VIntegral (logDeriv riemannZeta) w.re z.im w.im).im :=
  RiemannHypothesis.zeta_littlewood_lemma_nontrivialZeros hz0 hw1 hre him hborder

/-! ## M1-SPEISER-RH -/

example (h : RiemannHypothesis.ZetaStripForm) : RiemannHypothesis.SpeiserOffLineTransfer :=
  RiemannHypothesis.speiserOffLineTransfer_of_zetaStripForm h

example (h : RiemannHypothesis.ZetaStripForm) : ∃ C S : ℝ, ∀ T ≥ S,
    (RiemannHypothesis.xiDerivWindowCountOffLineMult T (2 * T) : ℝ) ≤ C * Real.log T :=
  RiemannHypothesis.xiDerivWindowCountOffLineMult_le_log_of_zetaStripForm h

example (h : ∀ C S : ℝ, ∃ T ≥ S,
      C * Real.log T < (RiemannHypothesis.xiDerivWindowCountOffLineMult T (2 * T) : ℝ)) :
    ¬ RiemannHypothesis.ZetaStripForm :=
  RiemannHypothesis.not_zetaStripForm_of_xiDeriv_offLine_gt h

/-! ## M1-STRIP-MEAN-SQUARE — the mean square of `ζ` inside the critical strip -/

example {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
        - RiemannHypothesis.dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖
        + (σ + |t|) * (N : ℝ) ^ (-σ) / σ :=
  RiemannHypothesis.norm_riemannZeta_sub_dirichletPoly_le h0 h1 hN t

example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      RiemannHypothesis.offDiagSum (fun _ => 1) N σ
        ≤ C * (N : ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) :=
  RiemannHypothesis.offDiagSum_one_le h0 h1

example {σ : ℝ} (h0 : 2 / 3 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤ C * T :=
  RiemannHypothesis.exists_integral_normSq_riemannZeta_le h0 h1

example {σ : ℝ} (h0 : 2 / 3 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ≤ C * T :=
  RiemannHypothesis.exists_integral_norm_riemannZeta_le h0 h1

example {σ : ℝ} (h0 : 2 / 3 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ V : ℝ, 0 < V →
      (MeasureTheory.volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖}).toReal ≤ C * T / V ^ 2 :=
  RiemannHypothesis.exists_volume_norm_riemannZeta_ge_le h0 h1

/-! ## M1-STRIP-MEAN-SQUARE — the trapezoidal refinement, `σ > 3/5` -/

example (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖RiemannHypothesis.trapTerm n s‖
      ≤ 1 / 8 * ‖s‖ * ‖s + 1‖ * ((n : ℝ) + 1) ^ (-(2 + s.re)) :=
  RiemannHypothesis.norm_trapTerm_le n hs0 hs1

example {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
        - RiemannHypothesis.dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖
        + ((N : ℝ) + 1) ^ (-σ) / 2
        + (σ + |t|) * (1 + σ + |t|) * (N : ℝ) ^ (-(1 + σ)) / (8 * (1 + σ)) :=
  RiemannHypothesis.norm_riemannZeta_sub_dirichletPoly_le_trap h0 h1 hN t

example {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤ C * T :=
  RiemannHypothesis.exists_integral_normSq_riemannZeta_le_three_fifths h0 h1

example {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ≤ C * T :=
  RiemannHypothesis.exists_integral_norm_riemannZeta_le_three_fifths h0 h1

example {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ V : ℝ, 0 < V →
      (MeasureTheory.volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖}).toReal ≤ C * T / V ^ 2 :=
  RiemannHypothesis.exists_volume_norm_riemannZeta_ge_le_three_fifths h0 h1

/-! ## M1-STRIP-MEAN-SQUARE — the second Bernoulli correction, `σ > 4/7` -/

example (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖RiemannHypothesis.bernTerm n s‖
      ≤ 1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 1) ^ (-(3 + s.re)) :=
  RiemannHypothesis.norm_bernTerm_le n hs0 hs1

example (N : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = (∑ n ∈ Finset.range N, ((n + 1 : ℝ) : ℂ) ^ (-s))
        + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((N + 1 : ℝ) : ℂ) ^ (-s) / 2
        + s * ((N + 1 : ℝ) : ℂ) ^ (-s - 1) / 12
        + ∑' n : ℕ, RiemannHypothesis.bernTerm (n + N) s :=
  RiemannHypothesis.riemannZeta_eq_bernApprox N hs0 hs1

example {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
        - RiemannHypothesis.dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖
        + ((N : ℝ) + 1) ^ (-σ) / 2
        + (σ + |t|) * (N : ℝ) ^ (-(1 + σ)) / 12
        + (σ + |t|) * (1 + σ + |t|) * (2 + σ + |t|) * (N : ℝ) ^ (-(2 + σ))
            / (48 * (2 + σ)) :=
  RiemannHypothesis.norm_riemannZeta_sub_dirichletPoly_le_bern h0 h1 hN t

example {σ : ℝ} (h0 : 4 / 7 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤ C * T :=
  RiemannHypothesis.exists_integral_normSq_riemannZeta_le_four_sevenths h0 h1

example {σ : ℝ} (h0 : 4 / 7 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ≤ C * T :=
  RiemannHypothesis.exists_integral_norm_riemannZeta_le_four_sevenths h0 h1

example {σ : ℝ} (h0 : 4 / 7 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ V : ℝ, 0 < V →
      (MeasureTheory.volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖}).toReal ≤ C * T / V ^ 2 :=
  RiemannHypothesis.exists_volume_norm_riemannZeta_ge_le_four_sevenths h0 h1

/-! ## M1-STRIP-MEAN-SQUARE — the Euler–Maclaurin expansion of arbitrary order,
and the Bohr–Landau mean square for every `σ > 1/2` -/

example (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs0 : 0 < s.re) (N : ℕ) :
    RiemannHypothesis.emTail m N s
      = -(RiemannHypothesis.bq (m + 1) 0) * RiemannHypothesis.dfun m s ((N : ℝ) + 1)
        - RiemannHypothesis.emTail (m + 1) N s :=
  RiemannHypothesis.emTail_succ m hm hs0 N

example (m : ℕ) (hm : 1 ≤ m) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, σ + |t| ≤ (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          - RiemannHypothesis.dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖
          + C * ((N : ℝ) ^ (-σ) + (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - m)) :=
  RiemannHypothesis.exists_norm_riemannZeta_sub_dirichletPoly_le_em m hm h0 h1

example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤ C * T :=
  RiemannHypothesis.exists_integral_normSq_riemannZeta_le_half h0 h1

example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ≤ C * T :=
  RiemannHypothesis.exists_integral_norm_riemannZeta_le_half h0 h1

example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ V : ℝ, 0 < V →
      (MeasureTheory.volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
        V ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖}).toReal ≤ C * T / V ^ 2 :=
  RiemannHypothesis.exists_volume_norm_riemannZeta_ge_le_half h0 h1

/-! ## M1-STRIP-MEAN-SQUARE-ASYMPTOTIC — the asymptotic with a power saving -/

example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        - T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))|
      ≤ RiemannHypothesis.offDiagSum a N σ :=
  RiemannHypothesis.abs_integral_normSq_dirichletPoly_sub_diag_le a N σ T

example {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
          - (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ))) * T| ≤ C * T ^ (1 - c) :=
  RiemannHypothesis.exists_integral_normSq_riemannZeta_asymptotic h0 h1

example {σ : ℝ} (h : 1 < 2 * σ) :
    ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)) : ℝ) : ℂ) = riemannZeta ((2 * σ : ℝ) : ℂ) :=
  RiemannHypothesis.ofReal_tsum_natAddOne_rpow_neg_eq_riemannZeta h

example {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    Filter.Tendsto
      (fun T : ℝ =>
        (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / T)
      Filter.atTop (nhds (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)))) :=
  RiemannHypothesis.tendsto_integral_normSq_riemannZeta_div h0 h1

/-! ## M1-STRIP-MEAN-SQUARE-ASYMPTOTIC — the asymptotic for every `σ > 1/2` (Bohr–Landau) -/

example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ (m : ℕ) (e : ℝ), 1 ≤ m ∧ 1 < e ∧ (m : ℝ) / (σ + (m : ℝ) - 1) < e ∧ e < 1 / (2 - 2 * σ) :=
  RiemannHypothesis.exists_emOrder_meanSquareExponent h0 h1

example {m : ℕ} {σ C : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (hC : 0 ≤ C)
    (hbd : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, σ + |t| ≤ (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          - RiemannHypothesis.dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ((N : ℝ) + 1) ^ (1 - σ) / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖
          + C * ((N : ℝ) ^ (-σ) + (σ + |t| + m) ^ m * (N : ℝ) ^ (1 - σ - m)))
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) (hTN : σ + T ≤ (N : ℝ)) :
    (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
        - RiemannHypothesis.dirichletPoly (fun _ => 1) N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ 3 * (((N : ℝ) + 1) ^ (2 - 2 * σ) * ((Real.pi / 2) / (1 - σ) ^ 2))
        + 3 * C ^ 2 * (N : ℝ) ^ (-(2 * σ)) * T
        + 3 * C ^ 2 * (((σ + T + m) ^ m) ^ 2 * (N : ℝ) ^ (2 - 2 * σ - 2 * (m : ℝ))) * T :=
  RiemannHypothesis.integral_normSq_error_em_le h0 h1 hC hbd hN hT hTN

example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
          - (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ))) * T| ≤ C * T ^ (1 - c) :=
  RiemannHypothesis.exists_integral_normSq_riemannZeta_asymptotic_half h0 h1

example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    Filter.Tendsto
      (fun T : ℝ =>
        (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / T)
      Filter.atTop (nhds (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)))) :=
  RiemannHypothesis.tendsto_integral_normSq_riemannZeta_div_half h0 h1

/-! ## M2-MEANVALUE — the mean value theorem for Dirichlet polynomials, arbitrary coefficients -/

example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    RiemannHypothesis.offDiagSum a N σ
      ≤ 8 * (N : ℝ) * (1 + Real.log N)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
  RiemannHypothesis.offDiagSum_le a N σ

example (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        - T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))|
      ≤ 8 * (N : ℝ) * (1 + Real.log N)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
  RiemannHypothesis.abs_integral_normSq_dirichletPoly_sub_diag_le_mvt a N σ T

example (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖RiemannHypothesis.dirichletPoly a N ((t : ℂ) * Complex.I)‖ ^ 2)
        - T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)|
      ≤ 8 * (N : ℝ) * (1 + Real.log N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
  RiemannHypothesis.integral_normSq_dirichletPoly_mvt_zero a N T

/-! ## M2-ZERO-EXPONENT — the exponent of convergence of the zeroes is at most `1` -/

example {e : ℝ} (he : 0 < e) :
    ∃ B : ℝ, 0 < B ∧ ∀ S : Finset ℂ, (∀ ρ ∈ S, ρ ∈ RiemannHypothesis.nontrivialZeroSet) →
      ∑ ρ ∈ S, ‖ρ‖ ^ (-(1 + e)) ≤ B :=
  RiemannHypothesis.sum_inv_norm_rpow_le he

example {e : ℝ} (he : 0 < e) :
    Summable (fun ρ : RiemannHypothesis.nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-(1 + e))) :=
  RiemannHypothesis.summable_inv_norm_rpow he

/-! ## M2-ZERO-EXPONENT — and it is exactly `1`: the divergence half -/

/-- The Riemann–von Mangoldt lower bound for the *distinct* zeroes. -/
example :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (T * Real.log T) ≤ (RiemannHypothesis.windowCountDistinct 0 T : ℝ) :=
  RiemannHypothesis.exists_mul_le_windowCountDistinct_zero

/-- The partial sums over the window `(0, T]` diverge for every `0 < e ≤ 1`. -/
example {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    Tendsto (fun T : ℝ =>
        ∑ ρ ∈ (RiemannHypothesis.windowZeros_finite 0 T).toFinset, ‖ρ‖ ^ (-e)) atTop atTop :=
  RiemannHypothesis.tendsto_sum_rpow_neg_windowZeros_atTop he he1

example {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ¬ Summable (fun ρ : RiemannHypothesis.nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-e)) :=
  RiemannHypothesis.not_summable_rpow_neg he he1

example {e : ℝ} (he : e ≤ 0) :
    ¬ Summable (fun ρ : RiemannHypothesis.nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-e)) :=
  RiemannHypothesis.not_summable_rpow_neg_of_nonpos he

/-- `∑_ρ 1/‖ρ‖` diverges. -/
example : ¬ Summable (fun ρ : RiemannHypothesis.nontrivialZeroSet => ‖(ρ : ℂ)‖⁻¹) :=
  RiemannHypothesis.not_summable_inv_norm

/-- The exponent of convergence of the nontrivial zeroes is exactly `1`. -/
example :
    sInf {e : ℝ |
        Summable (fun ρ : RiemannHypothesis.nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-e))} = 1 :=
  RiemannHypothesis.sInf_exponent_summable_eq_one

/-! ## M2-ZERO-SUM-LOGSQ — `∑_{0 < γ ≤ T} 1/‖ρ‖ ≍ (log T)²` -/

/-- The Riemann–von Mangoldt lower bound on a dyadic window, for the distinct zeroes. -/
example :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (T * Real.log T) ≤ (RiemannHypothesis.windowCountDistinct T (2 * T) : ℝ) :=
  RiemannHypothesis.exists_mul_le_windowCountDistinct_dyadic

/-- Distinct dyadic windows carry disjoint sets of zeroes. -/
example (s : Set ℕ) :
    s.PairwiseDisjoint (fun k : ℕ =>
      (RiemannHypothesis.windowZeros_finite ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset) :=
  RiemannHypothesis.pairwiseDisjoint_dyadic_windowZeros s

/-- Each dyadic block contributes `≫ k`. -/
example :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      c * k ≤ ∑ ρ ∈ (RiemannHypothesis.windowZeros_finite
        ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset, ‖ρ‖⁻¹ :=
  RiemannHypothesis.exists_mul_le_sum_inv_norm_block

/-- Each dyadic block contributes `≪ k`. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ∑ ρ ∈ (RiemannHypothesis.windowZeros_finite
          ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))).toFinset, ‖ρ‖⁻¹ ≤ C * ((k : ℝ) + 1) :=
  RiemannHypothesis.exists_sum_inv_norm_block_le

/-- `∑_{0 < γ ≤ T} 1/‖ρ‖ ≫ (log T)²`. -/
example :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (Real.log T) ^ 2
        ≤ ∑ ρ ∈ (RiemannHypothesis.windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹ :=
  RiemannHypothesis.exists_mul_log_sq_le_sum_inv_norm

/-- `∑_{0 < γ ≤ T} 1/‖ρ‖ ≪ (log T)²`. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∑ ρ ∈ (RiemannHypothesis.windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹
        ≤ C * (Real.log T) ^ 2 :=
  RiemannHypothesis.exists_sum_inv_norm_le_mul_log_sq

/-- The two-sided bound. -/
example :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (Real.log T) ^ 2
          ≤ ∑ ρ ∈ (RiemannHypothesis.windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹ ∧
        ∑ ρ ∈ (RiemannHypothesis.windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹
          ≤ C * (Real.log T) ^ 2 :=
  RiemannHypothesis.exists_sum_inv_norm_asymptotic

/-! ## M2-RVM-CUMULATIVE — `N(0, T) ~ (T/2π) log T` -/

/-- The Riemann–von Mangoldt formula on a dyadic window, in the repository's notation. -/
example :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |(RiemannHypothesis.windowCount T (2 * T) : ℝ)
          - T / (2 * Real.pi) * (Real.log T - RiemannHypothesis.rvmConst)|
        ≤ C * Real.log T :=
  RiemannHypothesis.exists_abs_windowCount_sub_main_le

/-- The dyadic telescope for the cumulative count. -/
example {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    RiemannHypothesis.windowCount 0 ((2 : ℝ) ^ n * s)
      = RiemannHypothesis.windowCount 0 s
        + ∑ j ∈ Finset.range n,
            RiemannHypothesis.windowCount ((2 : ℝ) ^ j * s) ((2 : ℝ) ^ (j + 1) * s) :=
  RiemannHypothesis.windowCount_eq_add_sum_dyadic hs n

/-- The summed main term over the dyadic blocks. -/
example (s : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n,
        (2 : ℝ) ^ j * s / (2 * Real.pi)
          * (Real.log s + (j : ℝ) * Real.log 2 - RiemannHypothesis.rvmConst)
      = (2 : ℝ) ^ n * s / (2 * Real.pi) * (Real.log s + (n : ℝ) * Real.log 2)
        - (2 : ℝ) ^ n * s / (2 * Real.pi) * (RiemannHypothesis.rvmConst + 2 * Real.log 2)
        + s / (2 * Real.pi) * (RiemannHypothesis.rvmConst - Real.log s + 2 * Real.log 2) :=
  RiemannHypothesis.sum_dyadic_main_term s n

/-- **The cumulative Riemann–von Mangoldt formula, sharp form**
`|N(0, T) − (T/2π)(log (T/2π) − 1)| ≤ A (log T)²`. -/
example :
    ∃ A : ℝ, 0 < A ∧ ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T →
      |(RiemannHypothesis.windowCount 0 T : ℝ)
          - T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1)|
        ≤ A * (Real.log T) ^ 2 :=
  RiemannHypothesis.exists_abs_windowCount_zero_sub_rvmMain_le

/-- The `o(T)` form of the sharp cumulative estimate. -/
example :
    Filter.Tendsto (fun T : ℝ => ((RiemannHypothesis.windowCount 0 T : ℝ)
        - T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1)) / T) Filter.atTop (nhds 0) :=
  RiemannHypothesis.tendsto_windowCount_zero_sub_rvmMain_div_atTop

/-- **The cumulative Riemann–von Mangoldt estimate, crude form**
`|N(0, T) − (T/2π) log T| ≤ A (T + (log T)²)`. -/
example :
    ∃ A : ℝ, 0 < A ∧ ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T →
      |(RiemannHypothesis.windowCount 0 T : ℝ) - T / (2 * Real.pi) * Real.log T|
        ≤ A * (T + (Real.log T) ^ 2) :=
  RiemannHypothesis.exists_abs_windowCount_zero_sub_main_le

/-- **`N(T) ~ (T/2π) log T`**, with multiplicity. -/
example :
    Filter.Tendsto (fun T : ℝ => (RiemannHypothesis.windowCount 0 T : ℝ) / (T * Real.log T))
      Filter.atTop (nhds (1 / (2 * Real.pi))) :=
  RiemannHypothesis.tendsto_windowCount_zero_div

/-! ## M2-ZERO-ORDINATE — the ordinate of the `n`-th zero -/

/-- Below `γ_n` the counting function has not reached `n`, and above it it has. -/
example {n : ℕ} {T : ℝ} (hT : 0 ≤ T) (h : T < RiemannHypothesis.nthZeroOrdinate n) :
    RiemannHypothesis.windowCount 0 T < n :=
  RiemannHypothesis.windowCount_lt_of_lt_nthZeroOrdinate hT h

example {n : ℕ} {T : ℝ} (h : RiemannHypothesis.nthZeroOrdinate n < T) :
    n ≤ RiemannHypothesis.windowCount 0 T :=
  RiemannHypothesis.le_windowCount_of_nthZeroOrdinate_lt h

/-- `γ_n` is the ordinate of an actual zero of `ζ` in the critical strip. -/
example {n : ℕ} (hn : 0 < n) :
    ∃ ρ ∈ RiemannHypothesis.nontrivialZeroSet, ρ.im = RiemannHypothesis.nthZeroOrdinate n :=
  RiemannHypothesis.exists_mem_nontrivialZeroSet_im_eq_nthZeroOrdinate hn

/-- `γ_n log γ_n ~ 2π n`. -/
example :
    Filter.Tendsto (fun n : ℕ => RiemannHypothesis.nthZeroOrdinate n
        * Real.log (RiemannHypothesis.nthZeroOrdinate n) / n) Filter.atTop
      (nhds (2 * Real.pi)) :=
  RiemannHypothesis.tendsto_nthZeroOrdinate_mul_log_div_nat

/-- **`γ_n ~ 2π n / log n`.** -/
example :
    Filter.Tendsto (fun n : ℕ => RiemannHypothesis.nthZeroOrdinate n * Real.log n / n)
      Filter.atTop (nhds (2 * Real.pi)) :=
  RiemannHypothesis.tendsto_nthZeroOrdinate_mul_log_nat_div

/-! ## M2-ZERO-GAPS — the gaps between consecutive zero ordinates -/

/-- The ordinates increase. -/
example : Monotone RiemannHypothesis.nthZeroOrdinate :=
  RiemannHypothesis.monotone_nthZeroOrdinate

/-- The gaps telescope: `∑_{n < N} (γ_{n+1} − γ_n) = γ_N`. -/
example (N : ℕ) :
    ∑ n ∈ Finset.range N, RiemannHypothesis.zeroGap n
      = RiemannHypothesis.nthZeroOrdinate N :=
  RiemannHypothesis.sum_zeroGap N

/-- `γ_n / n → 0`. -/
example :
    Filter.Tendsto (fun n : ℕ => RiemannHypothesis.nthZeroOrdinate n / n) Filter.atTop
      (nhds 0) :=
  RiemannHypothesis.tendsto_nthZeroOrdinate_div_nat

/-- **The average gap tends to `0`.** -/
example :
    Filter.Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, RiemannHypothesis.zeroGap n) / N)
      Filter.atTop (nhds 0) :=
  RiemannHypothesis.tendsto_avg_zeroGap

/-- Infinitely many gaps are smaller than any given `ε > 0`. -/
example {ε : ℝ} (hε : 0 < ε) : {n : ℕ | RiemannHypothesis.zeroGap n < ε}.Infinite :=
  RiemannHypothesis.infinite_setOf_zeroGap_lt hε

/-- **`liminf (γ_{n+1} − γ_n) log γ_n ≤ 2π`**: infinitely many gaps are no larger than the
average gap `2π / log γ_n`, up to an arbitrarily small relative error. -/
example {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | RiemannHypothesis.zeroGap n
      * Real.log (RiemannHypothesis.nthZeroOrdinate n) < 2 * Real.pi + ε}.Infinite :=
  RiemannHypothesis.infinite_setOf_zeroGap_mul_log_lt hε

/-- `log γ_{n+1} / log γ_n → 1`. -/
example :
    Filter.Tendsto (fun n : ℕ => Real.log (RiemannHypothesis.nthZeroOrdinate (n + 1))
        / Real.log (RiemannHypothesis.nthZeroOrdinate n)) Filter.atTop (nhds 1) :=
  RiemannHypothesis.tendsto_log_nthZeroOrdinate_succ_div

/-- **`limsup (γ_{n+1} − γ_n) log γ_n ≥ 2π`**: infinitely many gaps are at least as large as
the average gap `2π / log γ_n`, up to an arbitrarily small relative error. -/
example {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | 2 * Real.pi - ε < RiemannHypothesis.zeroGap n
      * Real.log (RiemannHypothesis.nthZeroOrdinate n)}.Infinite :=
  RiemannHypothesis.infinite_setOf_zeroGap_mul_log_gt hε

/-! ## M2-BOHR-LANDAU — the Bohr–Landau zero-density theorem -/

/-- The mean square on vertical lines, uniformly in the abscissa `σ ≥ σ₀ > 1/2`. -/
example {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤ C * T :=
  RiemannHypothesis.exists_integral_normSq_riemannZeta_le_uniform h0 h1

example {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤ C * b :=
  RiemannHypothesis.integral_normSq_riemannZeta_le_uniform_Icc h0 h1

/-- The same mean square transported from vertical lines to circles. -/
example {R : ℝ} (hR0 : 0 < R) (hR : R < 5 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 4 ≤ a → a ≤ b →
      (∫ y in a..b,
          Real.circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2)
            ((3 : ℂ) + (y : ℂ) * Complex.I) R)
        ≤ C * b :=
  RiemannHypothesis.exists_integral_circleAverage_normSq_riemannZeta_le hR0 hR

/-- `N(σ, T) = O_σ(T)` for every fixed `σ > 1/2`: zeroes counted without multiplicity. -/
example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T} : ℝ) ≤ C * T :=
  RiemannHypothesis.exists_ncard_zerosRightOf_le h0 h1

/-- The two-sided form: zeroes at distance at least `δ` from the critical line. -/
example {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ δ ≤ |ρ.re - 1 / 2| ∧ 0 < ρ.im ∧ ρ.im ≤ T} : ℝ)
        ≤ C * T :=
  RiemannHypothesis.exists_ncard_zerosOffCriticalLine_le hδ0 hδ1

/-- The Riemann–von Mangoldt lower bound `N(0, T) ≫ T log T`, with multiplicity. -/
example :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (T * Real.log T) ≤ (RiemannHypothesis.windowCount 0 T : ℝ) :=
  RiemannHypothesis.exists_mul_le_windowCount_zero

/-- **Almost all zeroes lie within `δ` of the critical line.** -/
example {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    Filter.Tendsto
      (fun T : ℝ =>
        (Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ δ ≤ |ρ.re - 1 / 2| ∧ 0 < ρ.im ∧ ρ.im ≤ T} : ℝ)
          / (RiemannHypothesis.windowCount 0 T : ℝ))
      Filter.atTop (nhds 0) :=
  RiemannHypothesis.tendsto_zerosOffCriticalLine_div_windowCount hδ0 hδ1

/-! ## M2-LINDELOF-DENSITY — Backlund's criterion, the direction from Lindelöf to the zeroes -/

/-- The Lindelöf hypothesis is the intended statement. -/
example : RiemannHypothesis.LindelofHypothesis =
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ s.im → ‖riemannZeta s‖ ≤ C * s.im ^ ε := rfl

/-- The counting set is the intended one: zeroes with `re ≥ σ` and ordinate in `(T₁, T₂]`. -/
example (σ T₁ T₂ : ℝ) : RiemannHypothesis.zerosRightOfWindow σ T₁ T₂ =
    {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂} := rfl

/-- **Unconditional**: Jensen's counting inequality for one disc, against the maximum of `‖ζ‖`
on the larger circle. -/
example {σ κ r R M : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hrR : r < R) (hR : R < 5 / 2)
    (hgeom : (3 - σ) ^ 2 + κ ^ 2 ≤ r ^ 2) (hM : 1 ≤ M)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ σ ≤ ρ.re) {y : ℝ} (hy : 4 ≤ y)
    (hbd : ∀ z ∈ Metric.sphere ((3 : ℂ) + (y : ℂ) * Complex.I) R, ‖riemannZeta z‖ ≤ M) :
    ((S.filter fun ρ => |ρ.im - y| ≤ κ).card : ℝ) * Real.log (R / r)
      ≤ Real.log M + Real.log 2 :=
  RiemannHypothesis.card_filter_le_log_max hκ hr hrR hR hgeom hM S hS hy hbd

/-- **Conditional on the Lindelöf hypothesis**: `N(σ, T+1) − N(σ, T) ≤ A + ε log T`. -/
example (hLH : RiemannHypothesis.LindelofHypothesis) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 5 ≤ T →
      ((RiemannHypothesis.zerosRightOfWindow σ T (T + 1)).ncard : ℝ) ≤ A + ε * Real.log T :=
  RiemannHypothesis.exists_ncard_zerosRightOfWindow_le hLH hσ hσ1 hε

/-- **Conditional on the Lindelöf hypothesis**: a unit window carries `o(log T)` zeroes with
real part at least `σ`. -/
example (hLH : RiemannHypothesis.LindelofHypothesis) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Filter.Tendsto
      (fun T : ℝ => ((RiemannHypothesis.zerosRightOfWindow σ T (T + 1)).ncard : ℝ) / Real.log T)
      Filter.atTop (nhds 0) :=
  RiemannHypothesis.tendsto_ncard_zerosRightOfWindow_div_log hLH hσ hσ1

/-- The two-sided counting set is the intended one. -/
example (δ T₁ T₂ : ℝ) : RiemannHypothesis.zerosOffCriticalLineWindow δ T₁ T₂ =
    {ρ : ℂ | riemannZeta ρ = 0 ∧ δ ≤ |ρ.re - 1 / 2| ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂} := rfl

/-- **Conditional on the Lindelöf hypothesis**: the two-sided form, for zeroes at distance at
least `δ` from the critical line on either side. -/
example (hLH : RiemannHypothesis.LindelofHypothesis) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    Filter.Tendsto
      (fun T : ℝ =>
        ((RiemannHypothesis.zerosOffCriticalLineWindow δ T (T + 1)).ncard : ℝ) / Real.log T)
      Filter.atTop (nhds 0) :=
  RiemannHypothesis.tendsto_ncard_zerosOffCriticalLineWindow_div_log hLH hδ0 hδ1

/-- **Unconditional**: the same window carries `O(log T)` zeroes with real part at least `σ`,
with an absolute implied constant. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ) (T : ℝ), 25 ≤ T →
    ((RiemannHypothesis.zerosRightOfWindow σ T (T + 1)).ncard : ℝ) ≤ C * Real.log T :=
  RiemannHypothesis.exists_ncard_zerosRightOfWindow_le_log

/-! ## M2-THREE-CIRCLES — Hadamard's three-circles theorem -/

/-- The closed annulus is the intended set. -/
example (r₁ r₃ : ℝ) : RiemannHypothesis.closedAnnulus r₁ r₃ = {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₃} := rfl

/-- **Unconditional**: the interpolation form of the three-circles theorem. -/
example {f : ℂ → ℂ} {r₁ r₃ a b : ℝ} (hr₁ : 0 < r₁) (hr : r₁ < r₃)
    (hf : AnalyticOnNhd ℂ f (RiemannHypothesis.closedAnnulus r₁ r₃))
    (ha : ∀ z : ℂ, ‖z‖ = r₁ → ‖f z‖ ≤ a) (hb : ∀ z : ℂ, ‖z‖ = r₃ → ‖f z‖ ≤ b)
    {z : ℂ} (hz : z ∈ RiemannHypothesis.closedAnnulus r₁ r₃) :
    ‖f z‖ ≤ a ^ (1 - (Real.log ‖z‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁))
      * b ^ ((Real.log ‖z‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) :=
  RiemannHypothesis.norm_le_rpow_mul_rpow_of_annulus hr₁ hr hf ha hb hz

/-- **Unconditional**: the classical form, with the exponents written as ratios of logarithms
of radii. -/
example {f : ℂ → ℂ} {r₁ r₃ a b : ℝ} (hr₁ : 0 < r₁) (hr : r₁ < r₃)
    (hf : AnalyticOnNhd ℂ f (RiemannHypothesis.closedAnnulus r₁ r₃))
    (ha : ∀ z : ℂ, ‖z‖ = r₁ → ‖f z‖ ≤ a) (hb : ∀ z : ℂ, ‖z‖ = r₃ → ‖f z‖ ≤ b)
    {z : ℂ} (hz : z ∈ RiemannHypothesis.closedAnnulus r₁ r₃) :
    ‖f z‖ ≤ a ^ (Real.log (r₃ / ‖z‖) / Real.log (r₃ / r₁))
      * b ^ (Real.log (‖z‖ / r₁) / Real.log (r₃ / r₁)) :=
  RiemannHypothesis.three_circles hr₁ hr hf ha hb hz

/-! ## M1-LITTLEWOOD-ZEROS — the modulus identity with zeroes inside the rectangle -/

example {f : ℂ → ℂ} {U : Set ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ ρ ∈ U, ¬ ∀ᶠ z in nhds ρ, f z = 0)
    (hsub : RiemannHypothesis.coordRect a b c d ⊆ U)
    (hfin : {z ∈ RiemannHypothesis.coordRect a b c d | f z = 0}.Finite) :
    (∫ σ in a..b, ∫ t in c..d, (logDeriv f ((σ : ℂ) + t * Complex.I)).re)
      = ∫ t in c..d, (Real.log ‖f ((b : ℂ) + t * Complex.I)‖
          - Real.log ‖f ((a : ℂ) + t * Complex.I)‖) :=
  RiemannHypothesis.integral_integral_re_logDeriv_eq_integral_log_norm_of_zeros hab hcd hU hf hne
    hsub hfin

/-! ## M1-LITTLEWOOD-BOUNDS — the terms of Littlewood's lemma for `ζ`, bounded -/

/-- A continuous real function whose cosine never vanishes moves by less than `π`. -/
example {theta : ℝ → ℝ} {c d : ℝ} (hc : ContinuousOn theta (Set.uIcc c d))
    (h : ∀ t ∈ Set.uIcc c d, Real.cos (theta t) ≠ 0) :
    |theta d - theta c| < Real.pi :=
  RiemannHypothesis.abs_sub_lt_pi_of_forall_cos_ne_zero hc h

/-- On `re s ≥ 3` the Dirichlet series of `ζ` is dominated by its first term. -/
example {s : ℂ} (hs : 3 ≤ s.re) : ‖riemannZeta s - 1‖ ≤ 1 / 2 :=
  RiemannHypothesis.norm_riemannZeta_sub_one_le_half_of_three_le_re hs

/-- The argument of `ζ` moves by less than `π` along any vertical segment of `re s = 3`. -/
example (c d : ℝ) :
    |(VIntegral (logDeriv riemannZeta) (3 : ℝ) c d).im| < Real.pi :=
  RiemannHypothesis.abs_im_VIntegral_logDeriv_riemannZeta_lt_pi c d

/-- The log-modulus of `ζ` on the line `re s = 3` contributes at most `log 2` per unit of
height. -/
example {c d : ℝ} (hcd : c ≤ d) :
    |∫ t in c..d, Real.log ‖riemannZeta (((3 : ℝ) : ℂ) + t * Complex.I)‖|
      ≤ Real.log 2 * (d - c) :=
  RiemannHypothesis.abs_integral_log_norm_riemannZeta_three_le hcd

/-- The mean of `log⁺ ‖ζ‖` on a vertical line with `σ ≥ σ₀ > 1/2` is `O(1)`. -/
example {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      (∫ t in a..b, Real.posLog ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ≤ C * b :=
  RiemannHypothesis.integral_posLog_norm_riemannZeta_le h0 h1

/-- Littlewood's lemma for `ζ` on a rectangle above the real axis, no longer confined to the
critical strip. -/
example {z w : ℂ} (hz : 0 < z.im) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros riemannZeta z w,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)
      = (∫ t in z.im..w.im,
            (Real.log ‖riemannZeta ((z.re : ℂ) + t * Complex.I)‖
              - Real.log ‖riemannZeta ((w.re : ℂ) + t * Complex.I)‖))
        + (∫ σ in z.re..w.re, (HIntegral (logDeriv riemannZeta) σ w.re z.im).im)
        - (∫ σ in z.re..w.re, (HIntegral (logDeriv riemannZeta) σ w.re w.im).im)
        + (w.re - z.re) * (VIntegral (logDeriv riemannZeta) w.re z.im w.im).im :=
  RiemannHypothesis.zeta_littlewood_lemma_above hz hre him hborder

/-- **Littlewood's lemma for `ζ` as an inequality**: every term is bounded except the two
horizontal argument terms, which are written out explicitly on the right. -/
example {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → ∀ T₁ T₂ : ℝ, 1 ≤ T₁ → T₁ ≤ T₂ →
      (∀ s ∈ RectangleBorder ((σ : ℂ) + T₁ * Complex.I) (((3 : ℝ) : ℂ) + T₂ * Complex.I),
        riemannZeta s ≠ 0) →
      2 * Real.pi * ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros riemannZeta
            ((σ : ℂ) + T₁ * Complex.I) (((3 : ℝ) : ℂ) + T₂ * Complex.I),
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - σ)
        ≤ C * T₂
          + (∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₁).im)
          - (∫ u in σ..(3 : ℝ), (HIntegral (logDeriv riemannZeta) u 3 T₂).im) :=
  RiemannHypothesis.exists_zeta_littlewood_bound h0 h1

/-! ## M1-BACKLUND-ARGUMENT — `S(t) = O(log t)` and the resulting density bound -/

/-- Backlund's bound: if the cosine of a continuous function vanishes at no more than `n` points
of `(a, b]`, the function moves by at most `(n + 1) π`. -/
example {theta : ℝ → ℝ} (n : ℕ) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn theta (Set.Icc a b))
    (hfin : {x ∈ Set.Ioc a b | Real.cos (theta x) = 0}.Finite)
    (hcard : {x ∈ Set.Ioc a b | Real.cos (theta x) = 0}.ncard ≤ n) :
    |theta b - theta a| ≤ (n + 1) * Real.pi :=
  RiemannHypothesis.abs_sub_le_of_ncard_cos_eq_zero n a b hab hc hfin hcard

/-- Jensen's counting inequality with an arbitrary ratio of radii, in maximum-modulus form. -/
example {f : ℂ → ℂ} {c : ℂ} {R r M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (hc : f c ≠ 0)
    (hM1 : 1 ≤ M) (hM : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) :
    ({z : ℂ | dist z c ≤ r ∧ f z = 0}.ncard : ℝ) * Real.log (R / r)
      ≤ Real.log M - Real.log ‖f c‖ :=
  RiemannHypothesis.ncard_setOf_zeros_le_radii hr hrR hf hc hM1 hM

/-- A crude polynomial bound for `ζ` to the right of `re s = 1/10`. -/
example {s : ℂ} (h : 1 / 10 ≤ s.re) (ht : 3 ≤ |s.im|) : ‖riemannZeta s‖ ≤ 80 * s.im ^ 2 :=
  RiemannHypothesis.norm_riemannZeta_le_sq_of_tenth_le_re h ht

/-- The reflected function computes the real part of `ζ` on the line `im s = T`. -/
example (T x : ℝ) :
    RiemannHypothesis.zetaRefl T ((x : ℂ) + (T : ℂ) * Complex.I)
      = ((riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)).re : ℂ) :=
  RiemannHypothesis.zetaRefl_horizontal T x

/-- **Backlund's count**: the real part of `ζ` has `O(log T)` zeroes on the segment
`[1/2, 3] × {T}`. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 6 ≤ T →
      ({x : ℝ | x ∈ Set.Icc (1 / 2 : ℝ) 3 ∧
          (riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)).re = 0}.Finite ∧
        ({x : ℝ | x ∈ Set.Icc (1 / 2 : ℝ) 3 ∧
          (riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)).re = 0}.ncard : ℝ) ≤ C * Real.log T) :=
  RiemannHypothesis.exists_ncard_re_riemannZeta_eq_zero_le

/-- **`S(t) = O(log t)`**: the variation of the argument of `ζ` along a horizontal segment
ending at the abscissa `3` is `O(log T)`. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 6 ≤ T → ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 3 →
      (∀ x ∈ Set.uIcc u (3 : ℝ), riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0) →
      |(HIntegral (logDeriv riemannZeta) u 3 T).im| ≤ C * Real.log T :=
  RiemannHypothesis.exists_abs_im_HIntegral_logDeriv_riemannZeta_le

/-- **Littlewood's lemma for `ζ` with every term bounded**: no unbounded quantity is left on the
right-hand side. -/
example {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → σ < 1 → ∀ T₁ T₂ : ℝ, 6 ≤ T₁ → T₁ ≤ T₂ →
      (∀ s ∈ RectangleBorder ((σ : ℂ) + T₁ * Complex.I) (((3 : ℝ) : ℂ) + T₂ * Complex.I),
        riemannZeta s ≠ 0) →
      2 * Real.pi * ∑ᶠ ρ ∈ RiemannHypothesis.rectZeros riemannZeta
            ((σ : ℂ) + T₁ * Complex.I) (((3 : ℝ) : ℂ) + T₂ * Complex.I),
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - σ) ≤ C * T₂ :=
  RiemannHypothesis.exists_zeta_littlewood_bound_total h0 h1

/-- **The density bound along the Littlewood route**: `N(σ; T₁, T₂) = O(T₂)` for `σ > 1/2`. -/
example {σ₀ σ : ℝ} (h0 : 1 / 2 < σ₀) (hσ : σ₀ < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₁ T₂ : ℝ, 6 ≤ T₁ → T₁ ≤ T₂ →
      (∀ s ∈ RectangleBorder ((σ₀ : ℂ) + T₁ * Complex.I) (((3 : ℝ) : ℂ) + T₂ * Complex.I),
        riemannZeta s ≠ 0) →
      (RiemannHypothesis.rectZeroCount riemannZeta
        ((σ : ℂ) + T₁ * Complex.I) (((3 : ℝ) : ℂ) + T₂ * Complex.I) : ℝ) ≤ C * T₂ :=
  RiemannHypothesis.exists_rectZeroCount_riemannZeta_le h0 hσ h1

/-! ## M1-CRITICAL-LINE-MEAN-SQUARE — the moments of `ζ` on the critical line -/

/-- **The mean square on the critical line**: `∫₀ᵀ ‖ζ(1/2 + i t)‖² dt = O_ε(T^{1+ε})`. -/
example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        ≤ C * T ^ (1 + ε) :=
  RiemannHypothesis.exists_integral_normSq_riemannZeta_le_critical_line hε

/-- **The first moment on the critical line**. -/
example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
        ≤ C * T ^ (1 + ε) :=
  RiemannHypothesis.exists_integral_norm_riemannZeta_le_critical_line hε

/-! ## M1-VAN-DER-CORPUT — the derivative tests for exponential integrals -/

/-- **The first-derivative test**: the bound `4/m` does not depend on the length of the
range. -/
example {a b m : ℝ} {F F' F'' : ℝ → ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hF''c : ContinuousOn F'' (Set.Icc a b))
    (hsign : (∀ x ∈ Set.Icc a b, 0 ≤ F'' x) ∨ (∀ x ∈ Set.Icc a b, F'' x ≤ 0))
    (hlb : ∀ x ∈ Set.Icc a b, m ≤ |F' x|) :
    ‖∫ x in a..b, RiemannHypothesis.VanDerCorput.expI F x‖ ≤ 4 / m :=
  RiemannHypothesis.VanDerCorput.norm_integral_expI_le_of_abs_deriv_ge hab hm hF hF' hF''c
    hsign hlb

/-- **The second-derivative test**: no lower bound on `|F'|` is assumed. -/
example {a b r : ℝ} {F F' F'' : ℝ → ℝ} (hab : a ≤ b) (hr : 0 < r)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hF''c : ContinuousOn F'' (Set.Icc a b))
    (hlb : ∀ x ∈ Set.Icc a b, r ≤ F'' x) :
    ‖∫ x in a..b, RiemannHypothesis.VanDerCorput.expI F x‖ ≤ 12 / Real.sqrt r :=
  RiemannHypothesis.VanDerCorput.norm_integral_expI_le_of_deriv_two_ge hab hr hF hF' hF''c hlb

/-! ## M1-KUSMIN-LANDAU — the first-derivative test for exponential sums -/

/-- **The discrete Kusmin–Landau inequality**: the bound `1 + 2/λ` does not depend on the number
of terms. -/
example {K : ℕ} {lam : ℝ} {u : ℕ → ℝ} (hlam : 0 < lam)
    (hlb : ∀ i, i < K → lam ≤ u (i + 1) - u i)
    (hub : ∀ i, i < K → u (i + 1) - u i ≤ 1 - lam)
    (hmono : (∀ i j, i ≤ j → j < K → u (i + 1) - u i ≤ u (j + 1) - u j) ∨
             (∀ i j, i ≤ j → j < K → u (j + 1) - u j ≤ u (i + 1) - u i)) :
    ‖∑ j ∈ Finset.range (K + 1), RiemannHypothesis.KusminLandau.e2pi (u j)‖ ≤ 1 + 2 / lam :=
  RiemannHypothesis.KusminLandau.norm_sum_e2pi_le hlam hlb hub hmono

/-- **The differentiable form**: `f'` monotone and trapped in `[λ, 1−λ]`. -/
example {K : ℕ} {lam c : ℝ} {f f' : ℝ → ℝ} (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc c (c + K), HasDerivAt f (f' x) x)
    (hlb : ∀ x ∈ Set.Icc c (c + K), lam ≤ f' x)
    (hub : ∀ x ∈ Set.Icc c (c + K), f' x ≤ 1 - lam)
    (hmono : MonotoneOn f' (Set.Icc c (c + K)) ∨ AntitoneOn f' (Set.Icc c (c + K))) :
    ‖∑ j ∈ Finset.range (K + 1), RiemannHypothesis.KusminLandau.e2pi (f (c + j))‖
      ≤ 1 + 2 / lam :=
  RiemannHypothesis.KusminLandau.norm_sum_e2pi_le_of_deriv hlam hf hlb hub hmono

/-- **The form used in practice**: `f'` at distance at least `λ` from every integer. -/
example {K : ℕ} {lam c : ℝ} {k : ℤ} {f f' : ℝ → ℝ} (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc c (c + K), HasDerivAt f (f' x) x)
    (hlb : ∀ x ∈ Set.Icc c (c + K), (k : ℝ) + lam ≤ f' x)
    (hub : ∀ x ∈ Set.Icc c (c + K), f' x ≤ (k : ℝ) + 1 - lam)
    (hmono : MonotoneOn f' (Set.Icc c (c + K)) ∨ AntitoneOn f' (Set.Icc c (c + K))) :
    ‖∑ j ∈ Finset.range (K + 1), RiemannHypothesis.KusminLandau.e2pi (f (c + j))‖
      ≤ 1 + 2 / lam :=
  RiemannHypothesis.KusminLandau.norm_sum_e2pi_le_of_deriv_sub_int hlam hf hlb hub hmono

/-- **The general range**: `f'` monotone or antitone and at distance at least `λ` from every
integer, with no restriction on how many integers it sweeps across; the bound is proportional to
the total variation `V = |f'(c+K) − f'(c)|` of the derivative. -/
example {K : ℕ} {lam c : ℝ} {f f' : ℝ → ℝ} (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc c (c + K), HasDerivAt f (f' x) x)
    (hsep : ∀ x ∈ Set.Icc c (c + K), ∀ m : ℤ, lam ≤ |f' x - m|)
    (hmono : MonotoneOn f' (Set.Icc c (c + K)) ∨ AntitoneOn f' (Set.Icc c (c + K))) :
    ‖∑ j ∈ Finset.range (K + 1), RiemannHypothesis.KusminLandau.e2pi (f (c + j))‖
      ≤ (|f' (c + K) - f' c| + 2) * (1 + 2 / lam) :=
  RiemannHypothesis.KusminLandau.norm_sum_e2pi_le_of_deriv_general hlam hf hsep hmono

/-- **The exact block count** of the general range: the number of maximal subranges on which
`⌊f'⌋` is constant. -/
example {lam : ℝ} (hlam : 0 < lam) (K : ℕ) (c : ℝ) (f f' : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc c (c + K), HasDerivAt f (f' x) x)
    (hsep : ∀ x ∈ Set.Icc c (c + K), ∀ m : ℤ, lam ≤ |f' x - m|)
    (hmono : MonotoneOn f' (Set.Icc c (c + K))) :
    ‖∑ j ∈ Finset.range (K + 1), RiemannHypothesis.KusminLandau.e2pi (f (c + j))‖
      ≤ ((⌊f' (c + K)⌋ - ⌊f' c⌋ + 1 : ℤ) : ℝ) * (1 + 2 / lam) :=
  RiemannHypothesis.KusminLandau.norm_sum_e2pi_le_of_deriv_floor hlam K c f f' hf hsep hmono

/-! ## M1-VDC-SECOND-DERIVATIVE — the second-derivative test for exponential sums -/

/-- **The bound with the separation `λ` free**, under the sole hypothesis that `f'` increases at
speed at least `r`; the size is `2 (V + 2)` blocks, each contributing `(1 + 2/λ) + (2λ/r + 1)`. -/
example {f g : ℝ → ℝ} {a lam r : ℝ} {L : ℕ} (hr : 0 < r) (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt f (g x) x)
    (hgrow : ∀ x ∈ Set.Icc a (a + (L : ℝ)), ∀ y ∈ Set.Icc a (a + (L : ℝ)), x ≤ y →
      r * (y - x) ≤ g y - g x) :
    ‖∑ j ∈ Finset.range L, RiemannHypothesis.KusminLandau.e2pi (f (a + j))‖
      ≤ 2 * ((g (a + (L : ℝ)) - g a) + 2) * ((1 + 2 / lam) + (2 * lam / r + 1)) :=
  RiemannHypothesis.VanDerCorputSums.norm_sum_e2pi_le_of_grow hr hlam hf hgrow

/-- **The balanced choice `λ = √r/2`.** -/
example {f g : ℝ → ℝ} {a r : ℝ} {L : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt f (g x) x)
    (hgrow : ∀ x ∈ Set.Icc a (a + (L : ℝ)), ∀ y ∈ Set.Icc a (a + (L : ℝ)), x ≤ y →
      r * (y - x) ≤ g y - g x) :
    ‖∑ j ∈ Finset.range L, RiemannHypothesis.KusminLandau.e2pi (f (a + j))‖
      ≤ 2 * ((g (a + (L : ℝ)) - g a) + 2) * (2 + 5 / Real.sqrt r) :=
  RiemannHypothesis.VanDerCorputSums.norm_sum_e2pi_le_of_grow_sqrt hr hr1 hf hgrow

/-- **van der Corput's second-derivative test for sums**: `r ≤ f'' ≤ R` gives
`‖∑_{j < L} e(f (a + j))‖ ≤ 2 (R L + 2) (2 + 5/√r)`. -/
example {f g g' : ℝ → ℝ} {a r R : ℝ} {L : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt g (g' x) x)
    (hlb : ∀ x ∈ Set.Icc a (a + (L : ℝ)), r ≤ g' x)
    (hub : ∀ x ∈ Set.Icc a (a + (L : ℝ)), g' x ≤ R) :
    ‖∑ j ∈ Finset.range L, RiemannHypothesis.KusminLandau.e2pi (f (a + j))‖
      ≤ 2 * (R * L + 2) * (2 + 5 / Real.sqrt r) :=
  RiemannHypothesis.VanDerCorputSums.norm_sum_e2pi_le_of_deriv_two hr hr1 hf hg hlb hub

/-- **The decreasing case**: `−R ≤ f'' ≤ −r` gives the same bound. -/
example {f g g' : ℝ → ℝ} {a r R : ℝ} {L : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt g (g' x) x)
    (hlb : ∀ x ∈ Set.Icc a (a + (L : ℝ)), -R ≤ g' x)
    (hub : ∀ x ∈ Set.Icc a (a + (L : ℝ)), g' x ≤ -r) :
    ‖∑ j ∈ Finset.range L, RiemannHypothesis.KusminLandau.e2pi (f (a + j))‖
      ≤ 2 * (R * L + 2) * (2 + 5 / Real.sqrt r) :=
  RiemannHypothesis.VanDerCorputSums.norm_sum_e2pi_le_of_deriv_two_neg hr hr1 hf hg hlb hub

/-- **The worked instance for the phase of `ζ`** on the dyadic block `[N, 2N)`. -/
example {N : ℕ} {t : ℝ} (hN : 0 < N) (ht : 0 < t) (hts : t ≤ 8 * Real.pi * (N : ℝ) ^ 2) :
    ‖∑ j ∈ Finset.range N,
        RiemannHypothesis.KusminLandau.e2pi
          (-(t / (2 * Real.pi)) * Real.log ((N : ℝ) + (j : ℝ)))‖
      ≤ 2 * (t / (2 * Real.pi * (N : ℝ)) + 2)
          * (2 + 5 / Real.sqrt (t / (8 * Real.pi * (N : ℝ) ^ 2))) :=
  RiemannHypothesis.VanDerCorputSums.norm_sum_e2pi_logPhase_le hN ht hts

/-! ## M1-WEYL-DIFFERENCING — van der Corput's A process -/

/-- **The van der Corput inequality**: a sum supported in `[0, N)` is controlled by its
correlations, with no dependence on the number of shifts used. -/
example {N H : ℕ} {z : ℤ → ℂ} (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) (hH : 0 < H) :
    (H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n‖ ^ 2
      ≤ ((N : ℝ) + H - 1)
        * ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ‖RiemannHypothesis.WeylDifferencing.corr z N k‖ :=
  RiemannHypothesis.WeylDifferencing.mul_normSq_sum_le hz hH

/-- **The weighted form**, with the Fejér weights `H − |k|`. -/
example {N H : ℕ} {z : ℤ → ℂ} (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n‖ ^ 2
      ≤ ((N : ℝ) + H - 1) * ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ),
          ((H : ℝ) - |k|) * ‖RiemannHypothesis.WeylDifferencing.corr z N k‖ :=
  RiemannHypothesis.WeylDifferencing.mul_normSq_sum_le_weighted hz hH

/-- **The A process for an exponential sum**: the differenced sums bound the original. -/
example (f : ℤ → ℝ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), RiemannHypothesis.KusminLandau.e2pi (f n)‖ ^ 2
      ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k),
            RiemannHypothesis.KusminLandau.e2pi (f (n + k) - f n)‖) :=
  RiemannHypothesis.WeylDifferencing.norm_sq_sum_e2pi_le f N H hH

/-! ## M1-WEYL-QUADRATIC — Weyl's bound for a quadratic exponential sum -/

/-- **The geometric-series bound**: a linear exponential sum is bounded independently of the
number of terms. -/
example {theta : ℝ} (hθ : RiemannHypothesis.WeylQuadratic.intDist theta ≠ 0) (M : ℕ) (c : ℝ) :
    ‖∑ j ∈ Finset.range M, RiemannHypothesis.KusminLandau.e2pi (theta * j + c)‖
      ≤ 1 / (2 * RiemannHypothesis.WeylQuadratic.intDist theta) :=
  RiemannHypothesis.WeylQuadratic.norm_geomSum_e2pi_le hθ M c

/-- **Weyl's inequality for a quadratic phase.** -/
example (a : ℝ) (N H : ℕ) (hH : 0 < H)
    (ha : ∀ k : ℤ, 0 < k → k < (H : ℤ) →
      RiemannHypothesis.WeylQuadratic.intDist (2 * a * k) ≠ 0) :
    (H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
        RiemannHypothesis.KusminLandau.e2pi (a * (n : ℝ) ^ 2)‖ ^ 2
      ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          1 / (2 * RiemannHypothesis.WeylQuadratic.intDist (2 * a * k))) :=
  RiemannHypothesis.WeylQuadratic.norm_sq_sum_e2pi_quadratic_le a N H hH ha

/-- **Square-root cancellation** when the multiples avoid the integers uniformly. -/
example (a d : ℝ) (N H : ℕ) (hH : 0 < H) (hd : 0 < d)
    (ha : ∀ k : ℤ, 0 < k → k < (H : ℤ) → d ≤ RiemannHypothesis.WeylQuadratic.intDist (2 * a * k)) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
        RiemannHypothesis.KusminLandau.e2pi (a * (n : ℝ) ^ 2)‖ ^ 2
      ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + ((H : ℝ) - 1) / d) / H :=
  RiemannHypothesis.WeylQuadratic.normSq_sum_e2pi_quadratic_le_of_le a d N H hH hd ha

/-! ## M1-WEYL-EQUIDISTRIBUTION — cancellation in quadratic Weyl sums for irrational α -/

/-- **The diophantine input for an irrational coefficient**: the finitely many multiples
`2αk`, `0 < k < H`, stay a fixed positive distance from the integers. -/
example {a : ℝ} (ha : Irrational a) (H : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∀ k : ℤ, 0 < k → k < (H : ℤ) →
      d ≤ RiemannHypothesis.WeylQuadratic.intDist (2 * a * k) :=
  RiemannHypothesis.WeylEquidistribution.exists_pos_le_intDist_of_irrational ha H

/-- **Weyl's inequality with the diophantine hypothesis discharged.** -/
example {a : ℝ} (ha : Irrational a) {H : ℕ} (hH : 0 < H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖RiemannHypothesis.WeylEquidistribution.quadSum a N‖ ^ 2
        ≤ ((N : ℝ) + H) * ((N : ℝ) + C) / H :=
  RiemannHypothesis.WeylEquidistribution.exists_normSq_quadSum_le ha hH

/-- **The quadratic Weyl sum is `o(N)` for an irrational coefficient.** -/
example {a : ℝ} (ha : Irrational a) :
    Filter.Tendsto
      (fun N : ℕ => ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
        RiemannHypothesis.KusminLandau.e2pi (a * (n : ℝ) ^ 2)‖ / N)
      Filter.atTop (nhds 0) :=
  RiemannHypothesis.WeylEquidistribution.tendsto_norm_quadSum_div_atTop ha

/-! ## M1-WEYL-CRITERION — Weyl's criterion and equidistribution of `α n²` -/

/-- **The mean of a nonconstant character vanishes.** -/
example {m : ℤ} (hm : m ≠ 0) :
    (∫ t : AddCircle (1 : ℝ), fourier m t ∂AddCircle.haarAddCircle) = 0 :=
  RiemannHypothesis.WeylCriterion.integral_fourier_eq_zero hm

/-- **Weyl's criterion**: a sequence is equidistributed modulo one — the averages of every
continuous function on the circle converge to its mean — exactly when its exponential sums at
every nonzero frequency are `o(N)`. -/
example (x : ℕ → ℝ) :
    (∀ f : C(AddCircle (1 : ℝ), ℂ),
        Filter.Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
            f ((x n : ℝ) : AddCircle (1 : ℝ)))
          Filter.atTop (nhds (∫ t, f t ∂AddCircle.haarAddCircle)))
      ↔ (∀ m : ℤ, m ≠ 0 →
        Filter.Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.range N,
            RiemannHypothesis.KusminLandau.e2pi ((m : ℝ) * x n)‖ / N) Filter.atTop (nhds 0)) :=
  RiemannHypothesis.WeylCriterion.equidistributedMod1_iff_weylSumsVanish x

/-- **The fractional parts of `α n²` are equidistributed for every irrational `α`.** -/
example {a : ℝ} (ha : Irrational a) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Filter.Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        f ((a * (n : ℝ) ^ 2 : ℝ) : AddCircle (1 : ℝ)))
      Filter.atTop (nhds (∫ t, f t ∂AddCircle.haarAddCircle)) :=
  RiemannHypothesis.WeylCriterion.equidistributedMod1_quadratic ha f

/-- **The notion is not vacuous**: a constant sequence is not equidistributed. -/
example : ¬ (∀ f : C(AddCircle (1 : ℝ), ℂ),
    Filter.Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ _n ∈ Finset.range N,
        f (((0 : ℝ)) : AddCircle (1 : ℝ)))
      Filter.atTop (nhds (∫ t, f t ∂AddCircle.haarAddCircle))) :=
  RiemannHypothesis.WeylCriterion.not_equidistributedMod1_const_zero

/-! ## M1-WEYL-COUNT — the counting form of equidistribution -/

/-- **The counting form of equidistribution**: the proportion of the first `N` terms whose
fractional part lies in `[a, b) ⊆ (0, 1)` tends to `b − a`. -/
example {x : ℕ → ℝ} (h : RiemannHypothesis.WeylCriterion.EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card : ℝ) / N)
      Filter.atTop (nhds (b - a)) :=
  RiemannHypothesis.WeylCount.tendsto_countIn_div h ha hab hb

/-- **Weyl's theorem for quadratic sequences, in its classical form.** -/
example {a b al : ℝ} (hal : Irrational al) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            a ≤ Int.fract (al * (n : ℝ) ^ 2) ∧ Int.fract (al * (n : ℝ) ^ 2) < b).card : ℝ) / N)
      Filter.atTop (nhds (b - a)) :=
  RiemannHypothesis.WeylCount.tendsto_countIn_div_quadratic hal ha hab hb

/-! ## M1-WEYL-COUNT-GENERAL — the counting form for an arbitrary subinterval -/

/-- **Equidistribution is invariant under translation.** -/
example {x : ℕ → ℝ} (h : RiemannHypothesis.WeylCriterion.EquidistributedMod1 x) (c : ℝ) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 (fun n => x n + c) :=
  RiemannHypothesis.WeylCount.equidistributedMod1_add_const h c

/-- **The counting form of equidistribution for every subinterval of `[0, 1]`**, including the
intervals with an endpoint at `0` or at `1`. -/
example {x : ℕ → ℝ} (h : RiemannHypothesis.WeylCriterion.EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card : ℝ) / N)
      Filter.atTop (nhds (b - a)) :=
  RiemannHypothesis.WeylCount.tendsto_countIn_div_of_le h ha hab hb

/-- **Weyl's theorem for quadratic sequences, for every subinterval of `[0, 1]`.** -/
example {a b al : ℝ} (hal : Irrational al) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            a ≤ Int.fract (al * (n : ℝ) ^ 2) ∧ Int.fract (al * (n : ℝ) ^ 2) < b).card : ℝ) / N)
      Filter.atTop (nhds (b - a)) :=
  RiemannHypothesis.WeylCount.tendsto_countIn_div_quadratic_of_le hal ha hab hb

/-! ## M1-WEYL-LINEAR — Weyl's theorem for the linear sequence `α n` -/

/-- **The fractional parts of `α n` are equidistributed** for every irrational `α`. -/
example {al : ℝ} (hal : Irrational al) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 (fun n : ℕ => al * (n : ℝ)) :=
  RiemannHypothesis.WeylCount.equidistributedMod1_linear hal

/-- **Weyl's theorem for the linear sequence, in its counting form.** -/
example {a b al : ℝ} (hal : Irrational al) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            a ≤ Int.fract (al * (n : ℝ)) ∧ Int.fract (al * (n : ℝ)) < b).card : ℝ) / N)
      Filter.atTop (nhds (b - a)) :=
  RiemannHypothesis.WeylCount.tendsto_countIn_div_linear hal ha hab hb

/-! ## M1-WEYL-COUNT-ARC — the counting form for an arbitrary arc of the circle -/

/-- **The counting form of equidistribution for a wrap-around arc `[a, 1) ∪ [0, b)`.** -/
example {x : ℕ → ℝ} (h : RiemannHypothesis.WeylCriterion.EquidistributedMod1 x) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            (a ≤ Int.fract (x n) ∧ Int.fract (x n) < 1) ∨
              (0 ≤ Int.fract (x n) ∧ Int.fract (x n) < b)).card : ℝ) / N)
      Filter.atTop (nhds ((1 - a) + b)) :=
  RiemannHypothesis.WeylCount.tendsto_countArc_div h hb hba ha

/-- **Weyl's theorem for `α n²` on a wrap-around arc.** -/
example {a b al : ℝ} (hal : Irrational al) (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            (a ≤ Int.fract (al * (n : ℝ) ^ 2) ∧ Int.fract (al * (n : ℝ) ^ 2) < 1) ∨
              (0 ≤ Int.fract (al * (n : ℝ) ^ 2) ∧ Int.fract (al * (n : ℝ) ^ 2) < b)).card : ℝ) / N)
      Filter.atTop (nhds ((1 - a) + b)) :=
  RiemannHypothesis.WeylCount.tendsto_countArc_div_quadratic hal hb hba ha

/-- **Weyl's theorem for `α n` on a wrap-around arc.** -/
example {a b al : ℝ} (hal : Irrational al) (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            (a ≤ Int.fract (al * (n : ℝ)) ∧ Int.fract (al * (n : ℝ)) < 1) ∨
              (0 ≤ Int.fract (al * (n : ℝ)) ∧ Int.fract (al * (n : ℝ)) < b)).card : ℝ) / N)
      Filter.atTop (nhds ((1 - a) + b)) :=
  RiemannHypothesis.WeylCount.tendsto_countArc_div_linear hal hb hba ha

/-! ## M1-WEYL-PORTMANTEAU — Weyl's criterion in its counting form -/

/-- **The counting form implies the vanishing of every exponential sum.** -/
example {x : ℕ → ℝ}
    (h : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      Filter.Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter fun n : ℕ =>
              a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card : ℝ) / N)
        Filter.atTop (nhds (b - a))) :
    ∀ m : ℤ, m ≠ 0 →
      Filter.Tendsto
        (fun N : ℕ =>
          ‖∑ n ∈ Finset.range N,
              Complex.exp ((2 * Real.pi * ((m : ℝ) * x n) : ℝ) * Complex.I)‖ / N)
        Filter.atTop (nhds 0) :=
  RiemannHypothesis.WeylPortmanteau.weylSumsVanish_of_countsEquidistribute h

/-- **Weyl's criterion, counting form**: equidistribution against continuous test functions is
equivalent to the counting statement for every subinterval of `[0, 1]`. -/
example (x : ℕ → ℝ) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 x ↔
      ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
        Filter.Tendsto
          (fun N : ℕ =>
            (((Finset.range N).filter fun n : ℕ =>
                a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card : ℝ) / N)
          Filter.atTop (nhds (b - a)) :=
  RiemannHypothesis.WeylPortmanteau.equidistributedMod1_iff_countsEquidistribute x

/-- **The same against the exponential sums.** -/
example (x : ℕ → ℝ) :
    (∀ m : ℤ, m ≠ 0 →
        Filter.Tendsto
          (fun N : ℕ =>
            ‖∑ n ∈ Finset.range N,
                Complex.exp ((2 * Real.pi * ((m : ℝ) * x n) : ℝ) * Complex.I)‖ / N)
          Filter.atTop (nhds 0)) ↔
      ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
        Filter.Tendsto
          (fun N : ℕ =>
            (((Finset.range N).filter fun n : ℕ =>
                a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card : ℝ) / N)
          Filter.atTop (nhds (b - a)) :=
  RiemannHypothesis.WeylPortmanteau.weylSumsVanish_iff_countsEquidistribute x

/-! ## M1-ZETA-CHI-AFE — the `χ` factor, and the approximate functional equation as a statement -/

/-- **The elementary sum** `∑_{1 ≤ n ≤ N} 1/√n ≤ 2√N`. -/
example (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, (1 / Real.sqrt n) ≤ 2 * Real.sqrt N :=
  RiemannHypothesis.sum_one_div_sqrt_le N

/-- **The functional equation in asymmetric form**: `ζ s = χ s · ζ (1 − s)`. -/
example {s : ℂ} (hs0 : s ≠ 0) (hs : ∀ n : ℕ, s ≠ 1 + n) :
    riemannZeta s = RiemannHypothesis.zetaChi s * riemannZeta (1 - s) :=
  RiemannHypothesis.riemannZeta_eq_zetaChi_mul hs0 hs

/-- **`χ` is unimodular on the critical line**, the reason the two Dirichlet polynomials of the
approximate functional equation contribute equally. -/
example (t : ℝ) : ‖RiemannHypothesis.zetaChi (1 / 2 + (t : ℂ) * I)‖ = 1 :=
  RiemannHypothesis.norm_zetaChi_criticalLine t

/-- **The dual sum is the conjugate of the direct sum on the critical line.** -/
example (N : ℕ) (t : ℝ) :
    RiemannHypothesis.zetaSumDual N (1 / 2 + (t : ℂ) * I)
      = (starRingEnd ℂ) (RiemannHypothesis.zetaSum N (1 / 2 + (t : ℂ) * I)) :=
  RiemannHypothesis.zetaSumDual_criticalLine N t

/-- **The trivial bound for the Dirichlet polynomial**, uniform in `t`. -/
example (N : ℕ) (t : ℝ) :
    ‖RiemannHypothesis.zetaSum N (1 / 2 + (t : ℂ) * I)‖ ≤ 2 * Real.sqrt N :=
  RiemannHypothesis.norm_zetaSum_criticalLine_le N t

/-- **The recorded hypothesis is the intended statement.**  `AFECriticalLine C` says exactly that
`ζ(1/2+it)` differs from the two Dirichlet polynomials of length `⌊√(t/2π)⌋` by `O(t^(−1/4))`.  It
is *not* proved in this repository; every theorem that uses it takes it as a hypothesis. -/
example (C : ℝ) : RiemannHypothesis.AFECriticalLine C =
    ∀ t : ℝ, 2 ≤ t →
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)
          - RiemannHypothesis.zetaSum (RiemannHypothesis.afeLength t) (1 / 2 + (t : ℂ) * I)
          - RiemannHypothesis.zetaChi (1 / 2 + (t : ℂ) * I)
            * RiemannHypothesis.zetaSumDual (RiemannHypothesis.afeLength t)
                (1 / 2 + (t : ℂ) * I)‖
        ≤ C * t ^ (-(1 / 4) : ℝ) := rfl

/-- **The conditional convexity bound.**  The hypothesis `AFECriticalLine C` is visible in the
statement; nothing here is unconditional. -/
example {C : ℝ} (hafe : RiemannHypothesis.AFECriticalLine C) {t : ℝ} (ht : 2 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ (C + 4) * t ^ ((1 : ℝ) / 4) :=
  RiemannHypothesis.norm_riemannZeta_criticalLine_le_of_afe hafe ht

/-! ## M1-VDC-THIRD-DERIVATIVE — the third-derivative test -/

/-- **van der Corput's third-derivative test**, with the number of shifts `H` left free. -/
example {f f' f'' f''' : ℝ → ℝ} {a r R : ℝ} {N H : ℕ} (hH : 0 < H) (hHN : H ≤ N)
    (hf : ∀ x ∈ Set.Icc a (a + (N : ℝ)), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a (a + (N : ℝ)), HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x ∈ Set.Icc a (a + (N : ℝ)), HasDerivAt f'' (f''' x) x)
    (hr : 0 < r) (hHr : (H : ℝ) * r ≤ 1)
    (hlb : ∀ x ∈ Set.Icc a (a + (N : ℝ)), r ≤ f''' x)
    (hub : ∀ x ∈ Set.Icc a (a + (N : ℝ)), f''' x ≤ R) :
    (H : ℝ) * ‖∑ j ∈ Finset.range N, RiemannHypothesis.KusminLandau.e2pi (f (a + j))‖ ^ 2
      ≤ ((N : ℝ) + H) * ((N : ℝ) + 8 * R * N * H ^ 2 + 16 * H
          + 20 * R * N * H * Real.sqrt H / Real.sqrt r
          + 80 * Real.sqrt H / Real.sqrt r) :=
  RiemannHypothesis.VanDerCorputThird.norm_sq_sum_e2pi_le_of_deriv_three
    hH hHN hf hf' hf'' hr hHr hlb hub

/-! ## M1-AFE-SUBCONVEXITY — the exponent `1/6` -/

/-- **Abel summation** against nonnegative nonincreasing weights. -/
example {L : ℕ} {w : ℕ → ℝ} {z : ℕ → ℂ} {B : ℝ}
    (hnn : ∀ i, 0 ≤ w i) (hanti : ∀ i j : ℕ, i ≤ j → w j ≤ w i)
    (hB : ∀ l, l ≤ L → ‖∑ j ∈ Finset.range l, z j‖ ≤ B) :
    ‖∑ j ∈ Finset.range L, (w j : ℂ) * z j‖ ≤ w 0 * B :=
  RiemannHypothesis.AFESubconvexity.norm_sum_weighted_le hnn hanti hB

/-- **The block bound for the phase of `ζ`**, at height `t = u⁶`. -/
example {M L : ℕ} {u : ℝ} (hu : 1 ≤ u) (hM : 30 * u ^ 2 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ u ^ 3)
    (hLM : L ≤ M) :
    ‖∑ j ∈ Finset.range L,
        RiemannHypothesis.KusminLandau.e2pi
          (-(u ^ 6 / (2 * Real.pi)) * Real.log ((M : ℝ) + (j : ℝ)))‖
      ≤ 60 * Real.sqrt M * u :=
  RiemannHypothesis.AFESubconvexity.norm_sum_e2pi_logPhase_block_le hu hM hMu hLM

/-- **The block of the Dirichlet polynomial itself** is `O(u)`, with no `√M`. -/
example {M L : ℕ} {u : ℝ} (hu : 1 ≤ u) (hM : 30 * u ^ 2 ≤ (M : ℝ)) (hMu : (M : ℝ) ≤ u ^ 3)
    (hLM : L ≤ M) :
    ‖∑ j ∈ Finset.range L, ((M + j : ℕ) : ℂ) ^ (-(1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I))‖ ≤ 60 * u :=
  RiemannHypothesis.AFESubconvexity.norm_sum_block_criticalLine_le hu hM hMu hLM

/-- **The unconditional dyadic bound** for the Dirichlet polynomial of length `N ≤ u³`. -/
example {N : ℕ} {u : ℝ} (hu : 1 ≤ u) (hN : (N : ℝ) ≤ u ^ 3) :
    ‖RiemannHypothesis.zetaSum N (1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)‖
      ≤ 60 * u * (Nat.log 2 N + 1) :=
  RiemannHypothesis.AFESubconvexity.norm_zetaSum_le_of_le_cube hu hN

/-- **The subconvexity bound `t^(1/6) log t`, conditional on the approximate functional
equation.**  The hypothesis is visible in the statement. -/
example {C : ℝ} (hafe : RiemannHypothesis.AFECriticalLine C) {t : ℝ} (ht : (10 : ℝ) ^ 9 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ C + 120 * t ^ ((1 : ℝ) / 6) * (Real.log t + 1) :=
  RiemannHypothesis.AFESubconvexity.norm_riemannZeta_criticalLine_le_of_afe hafe ht

/-! ## M1-SUBCONVEXITY-UNCONDITIONAL — the exponent `1/6`, with no hypothesis -/

/-- **One block of the phase of `ζ`, in the whole range** `30u² ≤ M ≤ 2u¹²`. -/
example {M L : ℕ} {u : ℝ} (hu : 10 ≤ u) (hM : 30 * u ^ 2 ≤ (M : ℝ))
    (hMu : (M : ℝ) ≤ 2 * u ^ 12) (hLM : L ≤ M) :
    ‖∑ j ∈ Finset.range L,
        RiemannHypothesis.KusminLandau.e2pi
          (-(u ^ 6 / (2 * Real.pi)) * Real.log ((M : ℝ) + (j : ℝ)))‖
      ≤ 60 * Real.sqrt M * u :=
  RiemannHypothesis.SubconvexityUnconditional.norm_sum_e2pi_logPhase_block_le_all hu hM hMu hLM

/-- **The dyadic bound for the Dirichlet polynomial of length `N ≤ 2u¹² = 2t²`.** -/
example {N : ℕ} {u : ℝ} (hu : 10 ≤ u) (hN : (N : ℝ) ≤ 2 * u ^ 12) :
    ‖RiemannHypothesis.zetaSum N (1 / 2 + ((u ^ 6 : ℝ) : ℂ) * I)‖
      ≤ 60 * u * (Nat.log 2 N + 1) :=
  RiemannHypothesis.SubconvexityUnconditional.norm_zetaSum_le_of_le_pow_twelve hu hN

/-- **The Euler–Maclaurin error at length `t² ≤ N ≤ 2t²` is at most `10`.** -/
example {N : ℕ} {t : ℝ} (ht : 2 ≤ t) (hN : t ^ 2 ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * t ^ 2) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - RiemannHypothesis.zetaSum N (1 / 2 + (t : ℂ) * I)‖
      ≤ 10 :=
  RiemannHypothesis.SubconvexityUnconditional.norm_riemannZeta_sub_zetaSum_le ht hN hN2

/-- **Subconvexity on the critical line, unconditionally**: no hypothesis but `10⁹ ≤ t`. -/
example {t : ℝ} (ht : (10 : ℝ) ^ 9 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ 200 * t ^ ((1 : ℝ) / 6) * (Real.log t + 1) :=
  RiemannHypothesis.SubconvexityUnconditional.norm_riemannZeta_criticalLine_le ht

/-! ## M1-SUBCONVEXITY-STRIP — the exponent `(1-σ)/3` on every line of the right half strip -/

/-- **One block of the Dirichlet polynomial on the line `re s = σ`.** -/
example {M L : ℕ} {u sg : ℝ} (hu : 10 ≤ u) (hsg : 1 / 2 ≤ sg) (hM : 30 * u ^ 2 ≤ (M : ℝ))
    (hMu : (M : ℝ) ≤ 2 * u ^ 12) (hLM : L ≤ M) :
    ‖∑ j ∈ Finset.range L, ((M + j : ℕ) : ℂ) ^ (-((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I))‖
      ≤ 60 * u ^ (2 - 2 * sg) :=
  RiemannHypothesis.SubconvexityStrip.norm_sum_block_strip_le hu hsg hM hMu hLM

/-- **The Dirichlet polynomial of length `N ≤ 2t²` on the line `re s = σ`.** -/
example {N : ℕ} {u sg : ℝ} (hu : 10 ≤ u) (hsg : 1 / 2 ≤ sg) (hsg1 : sg ≤ 1)
    (hN : (N : ℝ) ≤ 2 * u ^ 12) :
    ‖RiemannHypothesis.zetaSum N ((sg : ℂ) + ((u ^ 6 : ℝ) : ℂ) * I)‖
      ≤ 120 * u ^ (2 - 2 * sg) * (Nat.log 2 N + 1) :=
  RiemannHypothesis.SubconvexityStrip.norm_zetaSum_strip_le hu hsg hsg1 hN

/-- **Subconvexity inside the strip, unconditionally.** -/
example {sg t : ℝ} (hsg : 1 / 2 ≤ sg) (hsg1 : sg ≤ 1) (ht : (10 : ℝ) ^ 9 ≤ t) :
    ‖riemannZeta ((sg : ℂ) + (t : ℂ) * I)‖ ≤ 400 * t ^ ((1 - sg) / 3) * (Real.log t + 1) :=
  RiemannHypothesis.SubconvexityStrip.norm_riemannZeta_strip_le hsg hsg1 ht

/-! ## M1-SUBCONVEXITY-LEFT — the exponent `1/2 - 2σ/3` on the left of the critical line -/

/-- **The Weyl exponent `1/6` on the critical line, at every height `|t| ≥ 3`.** -/
example : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 3 ≤ |t| →
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ A * |t| ^ ((1 : ℝ) / 6) * (1 + Real.log |t|) :=
  RiemannHypothesis.exists_bound_criticalLine_sixth

/-- **Subconvexity on `0 ≤ σ ≤ 1/2`, unconditionally.** -/
example : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 / 2 → 3 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ C * (1 + Real.log |s.im|) * |s.im| ^ (1 / 2 - 2 * s.re / 3) :=
  RiemannHypothesis.norm_riemannZeta_le_subconvexity_left

/-! ## M1-SUBCONVEXITY-CLOSED-STRIP — one subconvex bound for the whole closed strip -/

/-- **The exponent `(1-σ)/3` on `1/2 ≤ σ ≤ 1` at every height, with no threshold.** -/
example : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ C * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 3) :=
  RiemannHypothesis.norm_riemannZeta_le_subconvexity_right

/-- **Subconvexity on the whole closed critical strip.** -/
example : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ C * (1 + Real.log |s.im|)
      * |s.im| ^ max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) :=
  RiemannHypothesis.norm_riemannZeta_le_subconvexity_closed_strip

/-! ## M1-SUBCONVEXITY-LOGFREE — the subconvex bound with no logarithm -/

/-- **Log-free subconvexity on the closed strip, with an `ε` in the exponent.** -/
example {ep : ℝ} (hep : 0 < ep) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
      ‖riemannZeta s‖
        ≤ C * |s.im| ^ (max ((1 - s.re) / 3) (1 / 2 - 2 * s.re / 3) + ep) :=
  RiemannHypothesis.norm_riemannZeta_le_subconvexity_logfree hep

/-- **Log-free subconvexity at a fixed abscissa**, at an exponent strictly below the
convexity exponent `(1-σ)/2`, with no logarithm and no `ε`. -/
example {sg : ℝ} (h0 : 0 < sg) (h1 : sg < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta ((sg : ℂ) + (t : ℂ) * I)‖
        ≤ C * |t| ^ ((1 - sg) / 2 - min sg (1 - sg) / 12) :=
  RiemannHypothesis.norm_riemannZeta_le_subconvexity_logfree_fixed h0 h1

/-- **The same bound in asymptotic form.** -/
example {sg : ℝ} (h0 : 0 < sg) (h1 : sg < 1) :
    (fun t : ℝ => riemannZeta ((sg : ℂ) + (t : ℂ) * I))
      =O[atTop] fun t : ℝ => t ^ ((1 - sg) / 2 - min sg (1 - sg) / 12) :=
  RiemannHypothesis.isBigO_riemannZeta_subconvexity_logfree h0 h1

/-! ## M1-GROWTH — the convexity bound with no logarithm and no epsilon -/

/-- **The logarithm-free convexity bound** `‖ζ(σ + i t)‖ ≤ C |t|^((1-σ)/2)`, for every fixed
`σ` strictly inside the critical strip. -/
example {sg : ℝ} (h0 : 0 < sg) (h1 : sg < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta ((sg : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ ((1 - sg) / 2) :=
  RiemannHypothesis.norm_riemannZeta_le_convexity_logfree h0 h1

/-- **The same bound in asymptotic form**: `ζ(σ + i t) = O(t^((1-σ)/2))` as `t → ∞`. -/
example {sg : ℝ} (h0 : 0 < sg) (h1 : sg < 1) :
    (fun t : ℝ => riemannZeta ((sg : ℂ) + (t : ℂ) * I))
      =O[atTop] fun t : ℝ => t ^ ((1 - sg) / 2) :=
  RiemannHypothesis.isBigO_riemannZeta_convexity_logfree h0 h1

/-- **The bound used by the zero-free region**: `‖ζ(σ + i t)‖ ≤ 2 log|t| / (σ - 1)` for
`1 < σ ≤ 2`. -/
example {s : ℂ} (h1 : 1 < s.re) (h2 : s.re ≤ 2) (ht : 3 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 2 * Real.log |s.im| / (s.re - 1) :=
  RiemannHypothesis.norm_riemannZeta_le_log_div_of_one_lt_re h1 h2 ht

/-! ## M2-METHOD-CEILING — the ceilings of the counting routes -/

/-- **The exact ceiling of the distinctness-budget route**: `p` is derivable iff `p ≤ c − b`. -/
example {c b p : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    (∀ W : RiemannHypothesis.WindowCounts, W.SatisfiesBudget c b →
        p * W.total ≤ W.onLineMult) ↔ p ≤ c - b :=
  RiemannHypothesis.WindowCounts.budget_ceiling hb hbc hc

/-- **The exact ceiling of the multiplicity-aware route**: `p` is derivable iff `p ≤ 1 − b`. -/
example {b p : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (∀ W : RiemannHypothesis.WindowCounts, W.SatisfiesBudgetMult b →
        p * W.total ≤ W.onLineMult) ↔ p ≤ 1 - b :=
  RiemannHypothesis.WindowCounts.budgetMult_ceiling hb hb1

/-- **`80 %` is not derivable from the repository's distinctness and off-line budgets.** -/
example :
    ¬ ∀ W : RiemannHypothesis.WindowCounts, W.SatisfiesBudget (5 / 6) 0.13136 →
        (4 / 5) * W.total ≤ W.onLineMult :=
  RiemannHypothesis.WindowCounts.eighty_percent_not_derivable_from_budget

/-! ## M2-LINDELOF-FROM-RH — the Lindelöf bound away from the critical line, under RH -/

/-- **Conditional on `ZetaStripForm`**: for `1/2 + δ ≤ re s ≤ 5/2` and `im s ≥ 100`, the
Borel–Carathéodory / three-circles bound for `ζ`. -/
example (h : RiemannHypothesis.ZetaStripForm) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) {s : ℂ}
    (hre : 1 / 2 + δ ≤ s.re) (hre2 : s.re ≤ 5 / 2) (ht : 100 ≤ s.im) :
    ‖riemannZeta s‖
      ≤ 3 * Real.exp (4 * (60 * Real.log s.im / δ)
          ^ (Real.log (5 - 2 * δ) / Real.log (5 - δ))) :=
  RiemannHypothesis.norm_riemannZeta_le_exp_of_zetaStripForm h hδ0 hδ1 hre hre2 ht

/-- **Conditional on `ZetaStripForm`**: for every `δ > 0` and `ε > 0`, the Lindelöf bound
`ζ(s) = O_ε((im s)^ε)` uniformly for `re s ≥ 1/2 + δ`. -/
example (h : RiemannHypothesis.ZetaStripForm) {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → T₀ ≤ s.im →
      ‖riemannZeta s‖ ≤ C * s.im ^ ε :=
  RiemannHypothesis.exists_bound_riemannZeta_of_zetaStripForm h hδ0 hδ1 hε

/-- **Conditional on `ZetaStripForm`**: the two-sided form, with `|im s|`. -/
example (h : RiemannHypothesis.ZetaStripForm) {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → T₀ ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ ε :=
  RiemannHypothesis.exists_bound_riemannZeta_abs_im_of_zetaStripForm h hδ0 hδ1 hε

/-! ## M2-LARGE-VALUES — Halász–Montgomery and the large-values estimate for Dirichlet polynomials -/

/-- **The Halász–Montgomery inequality**, coordinate form: a bound on the Gram row sums bounds the
squared coefficients of the expansion. -/
example {ι κ : Type*} (s : Finset ι) (m : Finset κ) (φ : ι → κ → ℂ) (ξ : κ → ℂ) {Δ : ℝ}
    (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ i ∈ s, ∑ j ∈ s, ‖∑ n ∈ m, (starRingEnd ℂ) (φ i n) * φ j n‖ ≤ Δ) :
    ∑ i ∈ s, ‖∑ n ∈ m, (starRingEnd ℂ) (φ i n) * ξ n‖ ^ 2 ≤ Δ * ∑ n ∈ m, ‖ξ n‖ ^ 2 :=
  RiemannHypothesis.HalaszMontgomery.sum_normSq_le_of_rowSum_le s m φ ξ hΔ0 hΔ

/-- **The Halász–Montgomery inequality** in a complex inner product space. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*} (s : Finset ι)
    (φ : ι → E) (ξ : E) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ i ∈ s, ∑ j ∈ s, ‖inner ℂ (φ i) (φ j)‖ ≤ Δ) :
    ∑ i ∈ s, ‖inner ℂ (φ i) ξ‖ ^ 2 ≤ Δ * ‖ξ‖ ^ 2 :=
  RiemannHypothesis.HalaszMontgomery.halasz_montgomery s φ ξ hΔ0 hΔ

/-- **Large values of a Dirichlet polynomial**: the number of sampled points at which
`|D(t i)| ≥ V` is at most `Δ ‖a‖² / V²`, where `Δ` bounds the Gram row sums. -/
example {ι : Type*} (s : Finset ι) (t : ι → ℝ) (a : ℕ → ℂ) (N : ℕ) {Δ V : ℝ} (hΔ0 : 0 ≤ Δ)
    (hV : 0 < V)
    (hΔ : ∀ i ∈ s, ∑ j ∈ s,
        ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))‖ ≤ Δ)
    (hbig : ∀ i ∈ s, V ≤ ‖RiemannHypothesis.dirichletPoly a N ((t i : ℂ) * Complex.I)‖) :
    (s.card : ℝ) ≤ Δ * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / V ^ 2 :=
  RiemannHypothesis.HalaszMontgomery.card_le_of_dirichletPoly_large s t a N hΔ0 hV hΔ hbig

/-! ## M2-LARGE-SIEVE — the large sieve inequality -/

/-- **The large sieve inequality** for `δ`-separated points, with the constant
`N + δ⁻¹(1 + log (2δ)⁻¹)`. -/
example {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ RiemannHypothesis.LargeSieve.intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ‖∑ n ∈ Finset.range N,
        a n * RiemannHypothesis.KusminLandau.e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ ((N : ℝ) + δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹))) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 :=
  RiemannHypothesis.LargeSieve.large_sieve hδ hδ2 hsep a N

/-- **Large values of an exponential polynomial** over `δ`-separated points. -/
example {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ V : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ RiemannHypothesis.LargeSieve.intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ)
    (hbig : ∀ i ∈ s, V ≤ ‖∑ n ∈ Finset.range N,
      a n * RiemannHypothesis.KusminLandau.e2pi ((n : ℝ) * t i)‖) :
    (s.card : ℝ) ≤ ((N : ℝ) + δ⁻¹ * (1 + Real.log ((2 * δ)⁻¹)))
      * (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) / V ^ 2 :=
  RiemannHypothesis.LargeSieve.card_le_of_large_values hδ hδ2 hV hsep a N hbig

/-- **The ceiling of the large-values estimate**: the constant `1` in `R ≤ Δ ‖a‖²/V²` cannot be
improved, because the orthonormal configuration attains the Halász–Montgomery inequality. -/
example {c : ℝ}
    (hc : ∀ (R : ℕ) (φ : Fin R → Fin R → ℂ) (ξ : Fin R → ℂ) (Δ V : ℝ), 0 ≤ Δ → 0 < V →
      (∀ i, ∑ j, ‖∑ n, (starRingEnd ℂ) (φ i n) * φ j n‖ ≤ Δ) →
      (∀ i, V ≤ ‖∑ n, (starRingEnd ℂ) (φ i n) * ξ n‖) →
      (R : ℝ) ≤ c * Δ * (∑ n, ‖ξ n‖ ^ 2) / V ^ 2) :
    1 ≤ c :=
  RiemannHypothesis.HalaszMontgomery.largeValues_constant_ge_one hc

/-- **The ceiling of the large sieve**: every admissible constant is at least `max N (2δ)⁻¹`, so
only the logarithmic factor separates the constant proved in the repository from the optimum. -/
example {C : ℝ → ℕ → ℝ} (hC : RiemannHypothesis.LargeSieve.AdmissibleConstant C) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {N : ℕ} (hN : 0 < N) :
    max (N : ℝ) ((2 * δ)⁻¹) ≤ C δ N :=
  RiemannHypothesis.LargeSieve.le_of_admissibleConstant hC hδ hδ2 hN

/-! ## M2-LARGE-SIEVE-GALLAGHER — the large sieve without a logarithm -/

/-- **The large sieve inequality, Gallagher's form**, with the constant `δ⁻¹ + π N`. -/
example {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ RiemannHypothesis.LargeSieve.intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ s, ‖∑ n ∈ Finset.range N,
        a n * RiemannHypothesis.KusminLandau.e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ (δ⁻¹ + Real.pi * N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 :=
  RiemannHypothesis.LargeSieveGallagher.large_sieve_gallagher hδ hδ2 hsep a N

/-- **Parseval over one period** for an exponential polynomial with frequencies `n − c`. -/
example (a : ℕ → ℂ) (N : ℕ) (c : ℝ) :
    (∫ θ in (0:ℝ)..1, ‖RiemannHypothesis.LargeSieveGallagher.expPoly a N c θ‖ ^ 2)
      = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 :=
  RiemannHypothesis.LargeSieveGallagher.integral_normSq_expPoly a N c

/-- **Gallagher's lemma with the cross term.** -/
example {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ A B : ℝ} (hδ : 0 < δ) (hAB : A ≤ B)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (A + δ / 2) (B - δ / 2)) :
    δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2
      ≤ (∫ x in A..B, ‖f x‖ ^ 2) + (δ / 2) * ∫ x in A..B, 2 * ‖f x‖ * ‖f' x‖ :=
  RiemannHypothesis.LargeSieveGallagher.sum_normSq_le_of_separated_sharp hf hf' hδ hAB hsep hmem

/-- **Large values of an exponential polynomial**, counted with the constant `δ⁻¹ + π N`. -/
example {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ V : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ RiemannHypothesis.LargeSieve.intDist (t i - t j))
    (a : ℕ → ℂ) (N : ℕ)
    (hbig : ∀ i ∈ s, V ≤ ‖∑ n ∈ Finset.range N,
      a n * RiemannHypothesis.KusminLandau.e2pi ((n : ℝ) * t i)‖) :
    (s.card : ℝ)
      ≤ (δ⁻¹ + Real.pi * N) * (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) / V ^ 2 :=
  RiemannHypothesis.LargeSieveGallagher.card_le_of_large_values_gallagher hδ hδ2 hV hsep a N hbig

/-! ## M2-LARGE-SIEVE-FAREY — the arithmetic large sieve -/

/-- **The arithmetic large sieve**, over the reduced fractions `b / q` with `q ≤ Q`. -/
example {Q : ℕ} (hQ : 2 ≤ Q) (a : ℕ → ℂ) (N : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ Finset.range N,
          a n * RiemannHypothesis.KusminLandau.e2pi ((n : ℝ) * ((b : ℝ) / (q : ℝ)))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 :=
  RiemannHypothesis.LargeSieveFarey.large_sieve_farey_pairs hQ a N

/-- **Farey fractions of order `Q` are `Q⁻²`-separated modulo one.** -/
example {x y : ℚ} {Q : ℕ} (hx : x ∈ Set.Ico (0 : ℚ) 1) (hy : y ∈ Set.Ico (0 : ℚ) 1)
    (hxd : x.den ≤ Q) (hyd : y.den ≤ Q) (hxy : x ≠ y) :
    1 / ((Q : ℝ) ^ 2) ≤ RiemannHypothesis.LargeSieve.intDist ((x : ℝ) - (y : ℝ)) :=
  RiemannHypothesis.LargeSieveFarey.inv_sq_le_intDist_sub hx hy hxd hyd hxy

/-- **The large sieve at rationals of bounded denominator.** -/
example {s : Finset ℚ} {Q : ℕ} (hQ : 2 ≤ Q)
    (hmem : ∀ x ∈ s, x ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ x ∈ s, x.den ≤ Q)
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ x ∈ s, ‖∑ n ∈ Finset.range N,
        a n * RiemannHypothesis.KusminLandau.e2pi ((n : ℝ) * (x : ℝ))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 :=
  RiemannHypothesis.LargeSieveFarey.large_sieve_farey hQ hmem hden a N

/-- **Large values at Farey fractions.** -/
example {s : Finset ℚ} {Q : ℕ} {V : ℝ} (hQ : 2 ≤ Q) (hV : 0 < V)
    (hmem : ∀ x ∈ s, x ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ x ∈ s, x.den ≤ Q)
    (a : ℕ → ℂ) (N : ℕ)
    (hbig : ∀ x ∈ s, V ≤ ‖∑ n ∈ Finset.range N,
      a n * RiemannHypothesis.KusminLandau.e2pi ((n : ℝ) * (x : ℝ))‖) :
    (s.card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) / V ^ 2 :=
  RiemannHypothesis.LargeSieveFarey.card_le_of_large_values_farey hQ hV hmem hden a N hbig

/-! ## M2-LARGE-SIEVE-DUAL — the dual large sieve -/

/-- **The duality principle for a finite matrix.** -/
example {ι κ : Type*} {s : Finset ι} {u : Finset κ} (phi : ι → κ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a : κ → ℂ, ∑ i ∈ s, ‖∑ n ∈ u, a n * phi i n‖ ^ 2 ≤ C * ∑ n ∈ u, ‖a n‖ ^ 2)
    (x : ι → ℂ) :
    ∑ n ∈ u, ‖∑ i ∈ s, x i * (starRingEnd ℂ) (phi i n)‖ ^ 2 ≤ C * ∑ i ∈ s, ‖x i‖ ^ 2 :=
  RiemannHypothesis.LargeSieveDual.sum_normSq_adjoint_le phi hC h x

/-- **The dual large sieve**, with the constant `δ⁻¹ + π N`. -/
example {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ RiemannHypothesis.LargeSieve.intDist (t i - t j))
    (x : ι → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖∑ i ∈ s,
        x i * RiemannHypothesis.KusminLandau.e2pi ((n : ℝ) * t i)‖ ^ 2
      ≤ (δ⁻¹ + Real.pi * N) * ∑ i ∈ s, ‖x i‖ ^ 2 :=
  RiemannHypothesis.LargeSieveDual.large_sieve_dual hδ hδ2 hsep x N

/-- **The dual large sieve at Farey fractions**, with the constant `Q² + π N`. -/
example {s : Finset ℚ} {Q : ℕ} (hQ : 2 ≤ Q)
    (hmem : ∀ y ∈ s, y ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ y ∈ s, y.den ≤ Q)
    (x : ℚ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖∑ y ∈ s,
        x y * RiemannHypothesis.KusminLandau.e2pi ((n : ℝ) * (y : ℝ))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * ∑ y ∈ s, ‖x y‖ ^ 2 :=
  RiemannHypothesis.LargeSieveDual.large_sieve_dual_farey hQ hmem hden x N

/-! ## M2-ZERO-DETECTION — the mollifier identity -/

open scoped ArithmeticFunction.Moebius in
/-- The coefficients of `ζ M_y` vanish in the initial range `2 ≤ n ≤ y`. -/
example {y n : ℕ} (hn : 2 ≤ n) (hny : n ≤ y) :
    ∑ d ∈ n.divisors.filter (fun d => d ≤ y), ((ArithmeticFunction.moebius d : ℤ) : ℂ) = 0 :=
  RiemannHypothesis.Mollifier.detectCoeff_eq_zero_of_le hn hny

/-- **The mollifier identity** for `re s > 1`: `ζ(s) M_y(s) = 1 + ∑_{n > y} c_n n^{-s}`. -/
example {y : ℕ} (hy : 1 ≤ y) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * RiemannHypothesis.Mollifier.mollifier y s
      = 1 + LSeries (RiemannHypothesis.Mollifier.tailCoeff y) s :=
  RiemannHypothesis.Mollifier.zeta_mul_mollifier_eq_one_add_tail hy hs

open scoped ArithmeticFunction.Moebius in
/-- **The finite mollifier identity**, valid for every `s`: the mollified partial sum equals `1`
plus a Dirichlet polynomial supported on `m > y`. -/
example {y K : ℕ} (hy : 1 ≤ y) (hyK : y ≤ K) (s : ℂ) :
    (∑ d ∈ Finset.Icc 1 y, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (d : ℂ) ^ (-s)) *
        (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s))
      = 1 + ∑ m ∈ Finset.Ioc y (y * K),
          RiemannHypothesis.Mollifier.finiteDetectCoeff y K m * (m : ℂ) ^ (-s) :=
  RiemannHypothesis.Mollifier.mollified_partialSum_eq_one_add_tail hy hyK s

/-! ## M2-MOLLIFIED-MEAN-SQUARE — the mean square of the mollified partial sum -/

/-- **`∑_n d(n)² n^{-a}` converges for every `a > 1`.** -/
example {a : ℝ} (ha : 1 < a) :
    Summable fun n : ℕ =>
      (RiemannHypothesis.divisorCount (n + 1) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-a) :=
  RiemannHypothesis.summable_divisorCount_sq_rpow ha

/-- The mean-square weight of the mollifier tail coefficients is small for a long mollifier. -/
example {σ ε : ℝ} (hσ : 1 / 2 < σ) (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧
      ∑' n : ℕ, ‖RiemannHypothesis.Mollifier.tailCoeff y (n + 1)‖ ^ 2 *
        ((n : ℝ) + 1) ^ (-(2 * σ)) < ε :=
  RiemannHypothesis.exists_tsum_normSq_tailCoeff_lt hσ hε

/-- `M_y · P_K - 1` is a Dirichlet polynomial supported on `m > y`. -/
example {y K : ℕ} (hy : 1 ≤ y) (hyK : y ≤ K) (s : ℂ) :
    RiemannHypothesis.Mollifier.mollifier y s * (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-s)) - 1
      = RiemannHypothesis.dirichletPoly (RiemannHypothesis.mollifiedTailCoeff y K) (y * K) s :=
  RiemannHypothesis.mollifiedTail_eq hy hyK s

/-- **The mean square of the mollified partial sum**: for every `σ > 1/2` and `ε > 0` there is a
mollifier length `y ≥ 1` with `∫₀ᵀ ‖M_y P_K - 1‖² ≤ (T + 8 yK (1 + log (yK))) ε` for all
`K ≥ y` and `T ≥ 0`. -/
example {σ ε : ℝ} (hσ : 1 / 2 < σ) (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧ ∀ K : ℕ, y ≤ K → ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖RiemannHypothesis.Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
          (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖ ^ 2)
        ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K))) * ε :=
  RiemannHypothesis.exists_integral_normSq_mollified_partialSum_sub_one_le hσ hε

/-- **The large values estimate** for the mollified partial sum (Chebyshev). -/
example {σ ε : ℝ} (hσ : 1 / 2 < σ) (hε : 0 < ε) :
    ∃ y : ℕ, 1 ≤ y ∧ ∀ K : ℕ, y ≤ K → ∀ T : ℝ, 0 ≤ T → ∀ V : ℝ, 0 < V →
      (MeasureTheory.volume {t : ℝ | t ∈ Set.Ioc (0 : ℝ) T ∧
          V ≤ ‖RiemannHypothesis.Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) *
            (∑ k ∈ Finset.Icc 1 K, (k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) - 1‖}).toReal
        ≤ (T + 8 * ((y * K : ℕ) : ℝ) * (1 + Real.log (y * K))) * ε / V ^ 2 :=
  RiemannHypothesis.exists_volume_norm_mollified_partialSum_sub_one_ge_le hσ hε

/-! ## M2-DISCRETE-MEANVALUE — Gallagher's lemma and the discrete mean value theorem -/

/-- **Gallagher's lemma**: a Sobolev bound for a sum over `δ`-separated points. -/
example {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ A B : ℝ} (hδ : 0 < δ) (hAB : A ≤ B)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (A + δ / 2) (B - δ / 2)) :
    δ * ∑ i ∈ s, ‖f (t i)‖ ^ 2
      ≤ 2 * (∫ x in A..B, ‖f x‖ ^ 2) + δ ^ 2 * ∫ x in A..B, ‖f' x‖ ^ 2 :=
  RiemannHypothesis.Gallagher.sum_normSq_le_of_separated hf hf' hδ hAB hsep hmem

/-- The derivative of a Dirichlet polynomial along a vertical line. -/
example (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    HasDerivAt (fun x : ℝ => RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (x : ℂ) * I))
      (-I * RiemannHypothesis.dirichletPoly (RiemannHypothesis.logCoeff a) N
        ((σ : ℂ) + (t : ℂ) * I)) t :=
  RiemannHypothesis.hasDerivAt_dirichletPoly_line a N σ t

/-- **The discrete mean value theorem for Dirichlet polynomials** at `δ`-separated points. -/
example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2)) :
    ∑ i ∈ s, ‖RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2
      ≤ (2 / δ + δ * Real.log N ^ 2) * (T + 8 * (N : ℝ) * (1 + Real.log N))
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
  RiemannHypothesis.sum_normSq_dirichletPoly_at_separated_le a N σ hδ hT hsep hmem

/-- **The large values count** at `δ`-separated points. -/
example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T V : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2))
    (hbig : ∀ i ∈ s, V ≤ ‖RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖) :
    (s.card : ℝ)
      ≤ (2 / δ + δ * Real.log N ^ 2) * (T + 8 * (N : ℝ) * (1 + Real.log N))
          * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / V ^ 2 :=
  RiemannHypothesis.card_le_of_dirichletPoly_large_separated a N σ hδ hT hV hsep hmem hbig

/-! ## M2-MEANVALUE-MV — the mean value theorem with the error term inside the sum -/

/-- The Gaussian oscillatory integral `∫ exp (i θ t) exp (-b t²) dt = √(π/b) exp (-θ²/(4b))`. -/
example (b θ : ℝ) (hb : 0 < b) :
    ∫ t : ℝ, Complex.exp ((t : ℂ) * θ * I) * Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)
      = ((Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b)) : ℝ) : ℂ) :=
  RiemannHypothesis.integral_exp_mul_I_gaussian b θ hb

/-- The Gaussian-weighted mean square as a bilinear form in the coefficients. -/
example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ, ‖RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        Real.exp (-(b * t ^ 2)))
      ≤ Real.sqrt (Real.pi / b) * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (‖a m‖ * (m : ℝ) ^ (-σ)) * (‖a n‖ * (n : ℝ) ^ (-σ)) *
            Real.exp (-(Real.log n - Real.log m) ^ 2 / (4 * b)) :=
  RiemannHypothesis.integral_normSq_dirichletPoly_gaussian_le a N σ hb

/-- The row sums of the Gaussian kernel: `∑_{n ≤ N} exp (-L² (log n - log m)²) ≤ 1 + 6 m / L`. -/
example {L : ℝ} (hL : 3 ≤ L) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.exp (-(L ^ 2 * (Real.log n - Real.log m) ^ 2))
      ≤ 1 + 6 * m / L :=
  RiemannHypothesis.sum_exp_neg_sq_log_sub_le hL hm N

/-- **The mean value theorem for Dirichlet polynomials, in Montgomery–Vaughan shape**: the
error term is inside the sum. -/
example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 6 ≤ T) :
    (∫ t in (-T)..T, ‖RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 58 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) :=
  RiemannHypothesis.integral_normSq_dirichletPoly_le_mv a N σ hT

/-- The same over `[0, T]`. -/
example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 6 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 58 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) :=
  RiemannHypothesis.integral_Icc_normSq_dirichletPoly_le_mv a N σ hT

/-! ## M2-DISCRETE-MEANVALUE-MV — the discrete bound with the error term inside the sum -/

/-- The `(T + n)`-weighted coefficient comparison for `a n log n`. -/
example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∑ n ∈ Finset.Icc 1 N, ‖RiemannHypothesis.logCoeff a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n)
      ≤ Real.log N ^ 2 *
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) :=
  RiemannHypothesis.sum_normSq_logCoeff_weighted_le a N σ hT

/-- **The discrete mean value theorem, in Montgomery–Vaughan shape.** -/
example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 6 ≤ T)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2)) :
    ∑ i ∈ s, ‖RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖ ^ 2
      ≤ 58 * (2 / δ + δ * Real.log N ^ 2)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n) :=
  RiemannHypothesis.sum_normSq_dirichletPoly_at_separated_le_mv a N σ hδ hT hsep hmem

/-- **The large values count** at `δ`-separated points, in Montgomery–Vaughan shape. -/
example (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ T V : ℝ}
    (hδ : 0 < δ) (hT : 6 ≤ T) (hV : 0 < V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    (hmem : ∀ i ∈ s, t i ∈ Set.Icc (δ / 2) (T - δ / 2))
    (hbig : ∀ i ∈ s, V ≤ ‖RiemannHypothesis.dirichletPoly a N ((σ : ℂ) + (t i : ℂ) * I)‖) :
    (s.card : ℝ)
      ≤ 58 * (2 / δ + δ * Real.log N ^ 2)
          * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * (T + n)) / V ^ 2 :=
  RiemannHypothesis.card_le_of_dirichletPoly_large_separated_mv a N σ hδ hT hV hsep hmem hbig

/-! ## M1-WEYL-DIFFERENCE — van der Corput's difference theorem -/

/-- **The A process for a `ℕ`-indexed sequence**: `H ‖∑_{n<N} e(m xₙ)‖²` is bounded by the
differenced sums. -/
example (x : ℕ → ℝ) (m : ℝ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖∑ n ∈ Finset.range N, RiemannHypothesis.KusminLandau.e2pi (m * x n)‖ ^ 2
      ≤ ((N : ℝ) + H - 1)
        * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H,
            ‖∑ n ∈ Finset.range (N - k),
                RiemannHypothesis.KusminLandau.e2pi (m * (x (n + k) - x n))‖) :=
  RiemannHypothesis.WeylDifference.mul_normSq_weylSum_le x m N H hH

/-- **van der Corput's difference theorem**: if every difference sequence is equidistributed
modulo one, so is the sequence itself. -/
example {x : ℕ → ℝ}
    (h : ∀ k : ℕ, 0 < k →
      RiemannHypothesis.WeylCriterion.EquidistributedMod1 (fun n : ℕ => x (n + k) - x n)) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 x :=
  RiemannHypothesis.WeylDifference.equidistributedMod1_of_diff h

/-! ## M1-WEYL-POLYNOMIAL — Weyl's theorem for an arbitrary polynomial -/

/-- The forward difference of a polynomial of degree `d ≥ 1` has degree `d − 1` and leading
coefficient `d · a_d · k`. -/
example (p : Polynomial ℝ) (k : ℕ) (hd : 1 ≤ p.natDegree) :
    (Polynomial.taylor (k : ℝ) p - p).coeff (p.natDegree - 1)
      = (p.natDegree : ℝ) * p.coeff p.natDegree * k :=
  RiemannHypothesis.WeylPolynomial.coeff_diffPoly_pred p k hd

/-- **Weyl's theorem**: the values of a real polynomial of degree at least one with irrational
leading coefficient are equidistributed modulo one. -/
example {p : Polynomial ℝ} (hd : 1 ≤ p.natDegree) (hirr : Irrational (p.coeff p.natDegree)) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 (fun n : ℕ => p.eval (n : ℝ)) :=
  RiemannHypothesis.WeylPolynomial.equidistributedMod1_polyEval hd hirr

/-- **Weyl's theorem in its counting form.** -/
example {p : Polynomial ℝ} (hd : 1 ≤ p.natDegree) (hirr : Irrational (p.coeff p.natDegree))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            a ≤ Int.fract (p.eval (n : ℝ)) ∧ Int.fract (p.eval (n : ℝ)) < b).card : ℝ) / N)
      Filter.atTop (nhds (b - a)) :=
  RiemannHypothesis.WeylPolynomial.tendsto_countIn_div_polyEval hd hirr ha hab hb

/-- **The fractional parts of `α n^d` are equidistributed** for every irrational `α` and
`d ≥ 1`. -/
example {al : ℝ} (hal : Irrational al) {d : ℕ} (hd : 1 ≤ d) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 (fun n : ℕ => al * (n : ℝ) ^ d) :=
  RiemannHypothesis.WeylPolynomial.equidistributedMod1_monomial hal hd

/-- The counting form for `α n^d`. -/
example {al a b : ℝ} (hal : Irrational al) {d : ℕ} (hd : 1 ≤ d)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ =>
            a ≤ Int.fract (al * (n : ℝ) ^ d) ∧ Int.fract (al * (n : ℝ) ^ d) < b).card : ℝ) / N)
      Filter.atTop (nhds (b - a)) :=
  RiemannHypothesis.WeylPolynomial.tendsto_countIn_div_monomial hal hd ha hab hb

/-! ## M1-WEYL-POLYNOMIAL-GENERAL — Weyl's exact criterion for a polynomial sequence -/

/-- Equidistribution modulo one only depends on the sequence modulo one. -/
example {x y : ℕ → ℝ} (h : ∀ n, ∃ k : ℤ, x n = y n + k)
    (hy : RiemannHypothesis.WeylCriterion.EquidistributedMod1 y) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 x :=
  RiemannHypothesis.WeylPolynomial.equidistributedMod1_of_sub_int h hy

/-- A sequence all of whose arithmetic subsequences are equidistributed is equidistributed. -/
example {x : ℕ → ℝ} {v : ℕ} (hv : 0 < v)
    (h : ∀ r < v, RiemannHypothesis.WeylCriterion.EquidistributedMod1 fun k => x (v * k + r)) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 x :=
  RiemannHypothesis.WeylPolynomial.equidistributedMod1_of_residue_classes hv h

/-- One irrational coefficient of positive index makes the values of a polynomial
equidistributed modulo one — no hypothesis on the leading coefficient. -/
example {p : Polynomial ℝ} {j : ℕ} (hj : 1 ≤ j) (hirr : Irrational (p.coeff j)) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 (fun n : ℕ => p.eval (n : ℝ)) :=
  RiemannHypothesis.WeylPolynomial.equidistributedMod1_polyEval_of_exists_irrational hj hirr

/-- If every coefficient of positive index is rational, the values are not equidistributed. -/
example {p : Polynomial ℝ} (h : ∀ j, 1 ≤ j → ¬ Irrational (p.coeff j)) :
    ¬ RiemannHypothesis.WeylCriterion.EquidistributedMod1 (fun n : ℕ => p.eval (n : ℝ)) :=
  RiemannHypothesis.WeylPolynomial.not_equidistributedMod1_polyEval_of_forall_rat h

/-- **Weyl's criterion for polynomial sequences.** -/
example (p : Polynomial ℝ) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 (fun n : ℕ => p.eval (n : ℝ))
      ↔ ∃ j, 1 ≤ j ∧ Irrational (p.coeff j) :=
  RiemannHypothesis.WeylPolynomial.equidistributedMod1_polyEval_iff p

/-! ## M1-WEYL-QUADRATIC-QUANTITATIVE — the diophantine input, and an effective `N^(3/4)` bound -/

/-- A fraction with denominator `q` that is not an integer is at distance at least `1/q` from
the integers. -/
example {m : ℤ} {q : ℕ} (hq : 0 < q) (hdvd : ¬ ((q : ℤ) ∣ m)) :
    1 / (q : ℝ) ≤ RiemannHypothesis.WeylQuadratic.intDist ((m : ℝ) / q) :=
  RiemannHypothesis.WeylQuadratic.inv_le_intDist_intCast_div hq hdvd

/-- The distance to the nearest integer is `1`-Lipschitz. -/
example (x y : ℝ) :
    RiemannHypothesis.WeylQuadratic.intDist y
      ≤ RiemannHypothesis.WeylQuadratic.intDist x + |x - y| :=
  RiemannHypothesis.WeylQuadratic.intDist_le_intDist_add_abs_sub x y

/-- **The diophantine input to Weyl's inequality**: a rational approximation of denominator `q`
keeps the multiples `βk`, `0 < 2k ≤ q`, at distance `1/(2q)` from the integers. -/
example {be : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |be - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) {k : ℤ} (hk0 : 0 < k) (hk : 2 * k ≤ (q : ℤ)) :
    1 / (2 * (q : ℝ)) ≤ RiemannHypothesis.WeylQuadratic.intDist (be * k) :=
  RiemannHypothesis.WeylQuadratic.inv_two_mul_le_intDist_of_approx hq hcop happ hk0 hk

/-- **The quantitative Weyl inequality for a quadratic phase.** -/
example {al : ℝ} {a : ℤ} {q : ℕ} (hq : 4 ≤ q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |2 * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N : ℕ) :
    ‖RiemannHypothesis.WeylEquidistribution.quadSum al N‖ ^ 2
      ≤ 4 * ((N : ℝ) + q) * ((N : ℝ) + (q : ℝ) ^ 2) / q :=
  RiemannHypothesis.WeylQuadratic.normSq_quadSum_le_of_approx hq hcop happ N

/-- The fourth-power form with a denominator of the size of `√N`. -/
example {al : ℝ} {a : ℤ} {q N : ℕ} (hN : 16 ≤ N) (hcop : IsCoprime (q : ℤ) a)
    (hq1 : (N : ℝ) ≤ (q : ℝ) ^ 2) (hq2 : (q : ℝ) ^ 2 ≤ 4 * N)
    (happ : |2 * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖RiemannHypothesis.WeylEquidistribution.quadSum al N‖ ^ 4 ≤ 1600 * (N : ℝ) ^ 3 :=
  RiemannHypothesis.WeylQuadratic.norm_quadSum_pow_four_le_of_approx_sqrt hN hcop hq1 hq2 happ

/-- **An effective bound**: `‖∑_{0 ≤ n < N} e(α n²)‖ ≤ 7 N^(3/4)`. -/
example {al : ℝ} {a : ℤ} {q N : ℕ} (hN : 16 ≤ N) (hcop : IsCoprime (q : ℤ) a)
    (hq1 : (N : ℝ) ≤ (q : ℝ) ^ 2) (hq2 : (q : ℝ) ^ 2 ≤ 4 * N)
    (happ : |2 * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖RiemannHypothesis.WeylEquidistribution.quadSum al N‖ ≤ 7 * (N : ℝ) ^ ((3 : ℝ) / 4) :=
  RiemannHypothesis.WeylQuadratic.norm_quadSum_le_of_approx_sqrt hN hcop hq1 hq2 happ

/-! ## M1-WEYL-MIN-SUM — the counting lemma, and the Weyl exponent `1/2` -/

/-- **The block bound.**  Over any `q` consecutive integers, a majorant `g` of
`min(N, 1/(2‖βk‖))` has total mass at most `4N + q(1 + log q)`. -/
example {be : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |be - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) {N : ℝ} (hN : 0 ≤ N) {g : ℤ → ℝ}
    (hg0 : ∀ k, 0 ≤ g k) (hgN : ∀ k, g k ≤ N)
    (hgd : ∀ k, g k * (2 * RiemannHypothesis.WeylQuadratic.intDist (be * k)) ≤ 1) (x : ℤ) :
    ∑ k ∈ Finset.Ioc x (x + q), g k ≤ 4 * N + q * (1 + Real.log q) :=
  RiemannHypothesis.WeylQuadratic.sum_block_le hq hcop happ hN hg0 hgN hgd x

/-- **The counting lemma**: `∑_{0 < k ≤ H} min(N, 1/(2‖βk‖)) ≤ (H/q + 1)(4N + q(1 + log q))`. -/
example {be : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |be - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) {N : ℝ} (hN : 0 ≤ N) {g : ℤ → ℝ}
    (hg0 : ∀ k, 0 ≤ g k) (hgN : ∀ k, g k ≤ N)
    (hgd : ∀ k, g k * (2 * RiemannHypothesis.WeylQuadratic.intDist (be * k)) ≤ 1) (H : ℕ) :
    ∑ k ∈ Finset.Ioc (0 : ℤ) (H : ℤ), g k
      ≤ ((H : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) :=
  RiemannHypothesis.WeylQuadratic.sum_Ioc_le hq hcop happ hN hg0 hgN hgd H

/-- **Weyl's inequality for a quadratic phase with the counting lemma**, with the differencing
carried out to length `N` rather than `q/2`. -/
example {al : ℝ} {a : ℤ} {q N : ℕ} (hq : 0 < q) (hN : 0 < N) (hcop : IsCoprime (q : ℤ) a)
    (happ : |2 * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖RiemannHypothesis.WeylEquidistribution.quadSum al N‖ ^ 2
      ≤ 2 * N + 4 * ((N : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) :=
  RiemannHypothesis.WeylQuadratic.normSq_quadSum_le_of_approx_count hq hN hcop happ

/-- **Square-root cancellation** for a denominator `N ≤ q ≤ 2N`. -/
example {al : ℝ} {a : ℤ} {q N : ℕ} (hN : 0 < N) (hq1 : N ≤ q) (hq2 : q ≤ 2 * N)
    (hcop : IsCoprime (q : ℤ) a) (happ : |2 * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖RiemannHypothesis.WeylEquidistribution.quadSum al N‖ ^ 2
      ≤ 66 * N * (1 + Real.log (2 * N)) :=
  RiemannHypothesis.WeylQuadratic.normSq_quadSum_le_of_approx_large hN hq1 hq2 hcop happ

/-- **The exponent `1/2`, up to a logarithm**: `‖∑_{0 ≤ n < N} e(α n²)‖ ≤ 9 √(N (1 + log 2N))`. -/
example {al : ℝ} {a : ℤ} {q N : ℕ} (hN : 0 < N) (hq1 : N ≤ q) (hq2 : q ≤ 2 * N)
    (hcop : IsCoprime (q : ℤ) a) (happ : |2 * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖RiemannHypothesis.WeylEquidistribution.quadSum al N‖
      ≤ 9 * Real.sqrt ((N : ℝ) * (1 + Real.log (2 * N))) :=
  RiemannHypothesis.WeylQuadratic.norm_quadSum_le_of_approx_large hN hq1 hq2 hcop happ

/-! ## M1-WEYL-BADLY-APPROXIMABLE — an unconditional rate for a badly approximable coefficient -/

/-- **Dirichlet's approximation theorem** in the numerator/denominator form used here. -/
example (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ q ≤ n ∧ IsCoprime (q : ℤ) a ∧
      |x - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (n + 1)) :=
  RiemannHypothesis.WeylQuadratic.exists_coprime_approx x hn

/-- For a badly approximable `x` the Dirichlet denominator is large. -/
example {x c : ℝ}
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |x - (a : ℝ) / q|)
    {a : ℤ} {q n : ℕ} (hq : 0 < q) (happ : |x - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (n + 1))) :
    c * ((n : ℝ) + 1) ≤ q :=
  RiemannHypothesis.WeylQuadratic.le_den_of_badlyApproximable hbad hq happ

/-- **An unconditional rate**: no hypothesis on the size of a denominator is left to the caller,
only the Diophantine condition on `2α`. -/
example {al c : ℝ} (hc : 0 < c)
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |2 * al - (a : ℝ) / q|)
    {N : ℕ} (hN : 0 < N) :
    ‖RiemannHypothesis.WeylEquidistribution.quadSum al N‖
      ≤ Real.sqrt ((16 / c + 26) * N * (1 + Real.log N)) :=
  RiemannHypothesis.WeylQuadratic.norm_quadSum_le_of_badlyApproximable hc hbad hN

/-- `√2` is badly approximable, with constant `1/4`. -/
example : RiemannHypothesis.WeylQuadratic.BadlyApproximable (Real.sqrt 2) :=
  RiemannHypothesis.WeylQuadratic.badlyApproximable_sqrt_two'

/-- **Square-root cancellation for an explicit irrational coefficient**, unconditionally in `N`. -/
example {N : ℕ} (hN : 0 < N) :
    ‖RiemannHypothesis.WeylEquidistribution.quadSum (Real.sqrt 2 / 2) N‖
      ≤ Real.sqrt (90 * N * (1 + Real.log N)) :=
  RiemannHypothesis.WeylQuadratic.norm_quadSum_sqrt_two_le hN

/-- **Every quadratic irrational is badly approximable.** -/
example {x : ℝ} {A B C : ℤ} (hA : A ≠ 0)
    (hroot : (A : ℝ) * x ^ 2 + B * x + C = 0) (hirr : Irrational x) :
    RiemannHypothesis.WeylQuadratic.BadlyApproximable x :=
  RiemannHypothesis.WeylQuadratic.badlyApproximable_of_quadratic hA hroot hirr

/-- **Square-root cancellation whenever `2α` is a quadratic irrational.** -/
example {al : ℝ} {A B C : ℤ} (hA : A ≠ 0)
    (hroot : (A : ℝ) * (2 * al) ^ 2 + B * (2 * al) + C = 0) (hirr : Irrational (2 * al)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ‖RiemannHypothesis.WeylEquidistribution.quadSum al N‖
        ≤ Real.sqrt (K * N * (1 + Real.log N)) :=
  RiemannHypothesis.WeylQuadratic.exists_norm_quadSum_le_of_quadratic hA hroot hirr

/-! ## M1-WEYL-CUBIC — Weyl's bound for a cubic exponential sum -/

/-- **The first differencing**: the A process applied to the cubic phase. -/
example (al : ℝ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖RiemannHypothesis.WeylCubic.cubeSum al N‖ ^ 2
      ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          RiemannHypothesis.WeylCubic.cubeInner al N k) :=
  RiemannHypothesis.WeylCubic.mul_normSq_cubeSum_le al N H hH

/-- **The second differencing**: for a fixed shift the once-differenced sum has a quadratic
phase, and the A process bounds it by the majorants of the frequencies `6 α k l`. -/
example (al : ℝ) {N H : ℕ} (hH : 0 < H) {k : ℤ} (hk : 0 < k) (hkN : k ≤ (N : ℤ)) :
    (H : ℝ) * RiemannHypothesis.WeylCubic.cubeInner al N k ^ 2
      ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          RiemannHypothesis.WeylCubic.dioMaj (6 * al) N (k * l)) :=
  RiemannHypothesis.WeylCubic.mul_sq_cubeInner_le al hH hk hkN

/-- **The double sum**, folded onto `m = k l` and bounded by the counting lemma. -/
example {be : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |be - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H : ℕ) :
    ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), ∑ l ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
        RiemannHypothesis.WeylCubic.dioMaj be N (k * l)
      ≤ (H : ℝ) * (((H : ℝ) ^ 2 / q + 1) * (4 * N + q * (1 + Real.log q))) :=
  RiemannHypothesis.WeylCubic.sum_double_le hq hcop happ N H

/-- **Weyl's inequality for a cubic phase**: from a coprime approximation to `6α` with a
denominator at most `4N`, `‖∑_{0 ≤ n < N} e(α n³)‖⁸ ≤ 2²² (4N/q + 1)² N⁷ (1 + log 4N)²`. -/
example {al : ℝ} {a : ℤ} {q N : ℕ} (hN : 0 < N) (hq : 0 < q) (hqN : (q : ℝ) ≤ 4 * N)
    (hcop : IsCoprime (q : ℤ) a) (happ : |6 * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖RiemannHypothesis.WeylCubic.cubeSum al N‖ ^ 8
      ≤ 2 ^ 22 * (4 * (N : ℝ) / q + 1) ^ 2 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 :=
  RiemannHypothesis.WeylCubic.norm_cubeSum_pow_eight_le_of_approx hN hq hqN hcop happ

/-- **An unconditional rate** for a badly approximable coefficient: no hypothesis on the size of
a denominator is left to the caller. -/
example {al c : ℝ} (hc : 0 < c)
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |6 * al - (a : ℝ) / q|)
    {N : ℕ} (hN : 0 < N) :
    ‖RiemannHypothesis.WeylCubic.cubeSum al N‖ ^ 8
      ≤ 2 ^ 22 * (4 / c + 1) ^ 2 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 :=
  RiemannHypothesis.WeylCubic.norm_cubeSum_pow_eight_le_of_badlyApproximable hc hbad hN

/-- **A power saving for an explicit irrational coefficient**, unconditionally in `N`. -/
example {N : ℕ} (hN : 0 < N) :
    ‖RiemannHypothesis.WeylCubic.cubeSum (Real.sqrt 2 / 6) N‖ ^ 8
      ≤ 2 ^ 31 * (N : ℝ) ^ 7 * (1 + Real.log (4 * N)) ^ 2 :=
  RiemannHypothesis.WeylCubic.norm_cubeSum_sqrt_two_le hN

/-! ## M1-WEYL-GENERAL — Weyl's inequality in arbitrary degree -/

/-- **The `r`-fold shifted majorant sum** obeys the recursion the row describes. -/
example (be : ℝ) (N H : ℕ) (m : ℤ) :
    RiemannHypothesis.WeylGeneral.weylMulti be N H 0 m
      = RiemannHypothesis.WeylCubic.dioMaj be N m :=
  RiemannHypothesis.WeylGeneral.weylMulti_zero be N H m

example (be : ℝ) (N H r : ℕ) (m : ℤ) :
    RiemannHypothesis.WeylGeneral.weylMulti be N H (r + 1) m
      = ∑ k ∈ Finset.range H,
          RiemannHypothesis.WeylGeneral.weylMulti be N H r (m * (k : ℤ)) :=
  RiemannHypothesis.WeylGeneral.weylMulti_succ be N H r m

/-- **Differencing lowers the degree** and multiplies the leading coefficient by `(d + 1) k`. -/
example {d : ℕ} {al : ℝ} {f : ℤ → ℝ}
    (hf : RiemannHypothesis.WeylGeneral.IsPolyPhase (d + 1) al f) (k : ℤ) :
    RiemannHypothesis.WeylGeneral.IsPolyPhase d ((d + 1 : ℕ) * (k : ℝ) * al)
      (fun n => f (n + k) - f n) :=
  RiemannHypothesis.WeylGeneral.IsPolyPhase.diff hf k

/-- **Weyl's inequality in degree `d + 1`**, for an arbitrary polynomial phase and `H ≥ 1`
shifts, with no additive error term. -/
example (d : ℕ) {al : ℝ} {f : ℤ → ℝ}
    (hf : RiemannHypothesis.WeylGeneral.IsPolyPhase (d + 1) al f) (N H : ℕ) (hH : 0 < H) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), RiemannHypothesis.KusminLandau.e2pi (f n)‖ ^ (2 ^ d)
        * ((H : ℝ) ^ d * ((N : ℝ) + H))
      ≤ 8 ^ (2 ^ d) * ((N : ℝ) + H) ^ (2 ^ d)
        * RiemannHypothesis.WeylGeneral.weylMulti ((d + 1).factorial * al) N H d 1 :=
  RiemannHypothesis.WeylGeneral.norm_polyPhaseSum_pow_le d hf N H hH

/-- **The `(r+1)`-fold majorant sum, folded onto the product of the shifts.** -/
example (be : ℝ) (N H : ℕ) (r : ℕ) {m : ℤ} (hm : 0 < m) :
    RiemannHypothesis.WeylGeneral.weylMulti be N H (r + 1) m
      ≤ ((r : ℝ) + 1) * (H : ℝ) ^ r * N
        + (H : ℝ) ^ r * RiemannHypothesis.WeylGeneral.dioSum be N (m * (H : ℤ) ^ (r + 1)) :=
  RiemannHypothesis.WeylGeneral.weylMulti_le_dioSum be N H r hm

/-- **The majorant sum estimated by the counting lemma of `M1-WEYL-MIN-SUM`.** -/
example {be : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |be - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H r : ℕ) :
    RiemannHypothesis.WeylGeneral.weylMulti be N H (r + 1) 1
      ≤ ((r : ℝ) + 1) * (H : ℝ) ^ r * N
        + (H : ℝ) ^ r * (((H : ℝ) ^ (r + 1) / q + 1) * (4 * N + q * (1 + Real.log q))) :=
  RiemannHypothesis.WeylGeneral.weylMulti_le_of_approx hq hcop happ N H r

/-- **The power saving for a monomial phase of arbitrary degree**: for `H^(r+1) ≤ q ≤ N`,
`‖∑_{0 ≤ n < N} e(α n^(r+2))‖^(2^(r+1)) H ≤ 16^(2^(r+1)) N^(2^(r+1)) (r + 11 + 2 log N)`. -/
example {al : ℝ} {a : ℤ} {q : ℕ} (r : ℕ) (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |((r + 2).factorial : ℝ) * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {N H : ℕ} (hH : 0 < H) (hHq : (H : ℝ) ^ (r + 1) ≤ q) (hqN : q ≤ N) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
          RiemannHypothesis.KusminLandau.e2pi (al * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1)) * H
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1)) * ((r : ℝ) + 11 + 2 * Real.log N) :=
  RiemannHypothesis.WeylGeneral.norm_monomialSum_pow_mul_le_of_approx r hq hcop happ hH hHq hqN

/-! ## M1-WEYL-DIVISOR — the divisor bound, and Weyl's classical exponent -/

/-- **The divisor bound** `τ(n) ≤ C_ε n^ε`. -/
example {ep : ℝ} (hep : 0 < ep) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ ep :=
  RiemannHypothesis.DivisorBound.exists_card_divisors_le hep

/-- **The `(r+1)`-fold majorant sum folded onto the product of the shifts**, each product
counted with the number `τ^r` of its factorizations. -/
example (be : ℝ) (N H : ℕ) (s : ℕ) (m : ℤ) :
    RiemannHypothesis.WeylGeneral.weylMulti be N H (s + 1) m
      ≤ ((s : ℝ) + 1) * (H : ℝ) ^ s * N
        + ∑ u ∈ Finset.Icc 1 (H ^ (s + 1)), ((u.divisors.card : ℝ)) ^ s *
            RiemannHypothesis.WeylCubic.dioMaj be N (m * (u : ℤ)) :=
  RiemannHypothesis.WeylDivisor.weylMulti_le_divisorSum be N H s m

/-- **The majorant sum estimated with the divisor loss** `(C (H^(s+1))^ε)^s` in place of the
crude factor `H^s`. -/
example {be : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |be - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H s : ℕ) {ep C : ℝ} (hep : 0 < ep)
    (hC : 1 ≤ C) (hbound : ∀ n : ℕ, 0 < n → ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ ep) :
    RiemannHypothesis.WeylGeneral.weylMulti be N H (s + 1) 1
      ≤ ((s : ℝ) + 1) * (H : ℝ) ^ s * N
        + (C * ((H : ℝ) ^ (s + 1)) ^ ep) ^ s
          * (((H : ℝ) ^ (s + 1) / q + 1) * (4 * N + q * (1 + Real.log q))) :=
  RiemannHypothesis.WeylDivisor.weylMulti_le_of_approx_divisor hq hcop happ N H s hep hC hbound

/-- **Weyl's inequality with the classical exponent**, for `N ≤ q ≤ N^(r+1)`. -/
example {al : ℝ} {a : ℤ} {q : ℕ} (r : ℕ) (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |((r + 2).factorial : ℝ) * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {N : ℕ} (hN : 0 < N) (hqN : N ≤ q) (hqNr : (q : ℝ) ≤ (N : ℝ) ^ (r + 1))
    {ep C : ℝ} (hep : 0 < ep) (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ ep) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
          RiemannHypothesis.KusminLandau.e2pi (al * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1)) * N
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C * ((N : ℝ) ^ (r + 1)) ^ ep) ^ r
        * ((r : ℝ) + 11 + 2 * ((r : ℝ) + 1) * Real.log N) :=
  RiemannHypothesis.WeylDivisor.norm_monomialSum_pow_mul_le_of_approx_divisor r hq hcop happ hN
    hqN hqNr hep hC hbound

/-- **Weyl's exponent `1 − 1/2^(d−1) + ε`** for the monomial phase of degree `d = r + 2`. -/
example (r : ℕ) {ep : ℝ} (hep : 0 < ep) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (al : ℝ) (a : ℤ) (q N : ℕ), 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N → N ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 1) →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
            RiemannHypothesis.KusminLandau.e2pi (al * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1)) * N
        ≤ C * (N : ℝ) ^ (2 ^ (r + 1)) * (N : ℝ) ^ ep :=
  RiemannHypothesis.WeylDivisor.exists_norm_monomialSum_pow_mul_le r hep

/-! ## M1-WEYL-CLASSICAL — Weyl's inequality in its classical three-term form -/

/-- **The three-term form for an arbitrary polynomial phase** of degree at most `r + 2` with
`n^(r+2)`-coefficient `al`. -/
example (r : ℕ) {ep : ℝ} (hep : 0 < ep) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (al : ℝ) (f : ℤ → ℝ) (a : ℤ) (q N : ℕ),
      RiemannHypothesis.WeylGeneral.IsPolyPhase (r + 2) al f → 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), RiemannHypothesis.KusminLandau.e2pi (f n)‖
        ≤ C * (N : ℝ) ^ (1 + ep)
          * (1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ (r + 2)) ^ ((1 : ℝ) / 2 ^ (r + 1)) :=
  RiemannHypothesis.WeylClassical.exists_norm_polyPhaseSum_le_three_term r hep

/-- **The three-term form with explicit constants**, for every denominator `q > 0`. -/
example {al : ℝ} {a : ℤ} {q : ℕ} (r : ℕ) (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a)
    (happ : |((r + 2).factorial : ℝ) * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {N : ℕ} (hN : 0 < N) {ep C : ℝ} (hep : 0 < ep) (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ ep) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
          RiemannHypothesis.KusminLandau.e2pi (al * (n : ℝ) ^ (r + 2))‖ ^ (2 ^ (r + 1))
      ≤ 16 ^ (2 ^ (r + 1)) * (N : ℝ) ^ (2 ^ (r + 1))
        * (C * ((N : ℝ) ^ (r + 1)) ^ ep) ^ r * ((r : ℝ) + 21 + 4 * Real.log q)
        * (1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ (r + 2)) :=
  RiemannHypothesis.WeylClassical.norm_monomialSum_pow_le_three_term r hq hcop happ hN hep hC
    hbound

/-- **Weyl's inequality, classical form**: for every `ep > 0` there is a `C ≥ 1` with
`‖∑_{n<N} e(al n^d)‖ ≤ C N^(1+ep) (1/q + 1/N + q/N^d)^(1/2^(d−1))`, `d = r + 2`. -/
example (r : ℕ) {ep : ℝ} (hep : 0 < ep) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (al : ℝ) (a : ℤ) (q N : ℕ), 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
            RiemannHypothesis.KusminLandau.e2pi (al * (n : ℝ) ^ (r + 2))‖
        ≤ C * (N : ℝ) ^ (1 + ep)
          * (1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ (r + 2)) ^ ((1 : ℝ) / 2 ^ (r + 1)) :=
  RiemannHypothesis.WeylClassical.exists_norm_monomialSum_le_three_term r hep

/-! ## M1-WEYL-BADLY-GENERAL — Weyl's exponent for a badly approximable coefficient -/

/-- **Weyl's exponent for a badly approximable leading coefficient**, for an arbitrary polynomial
phase of degree at most `r + 2`. -/
example (r : ℕ) {ep c : ℝ} (hep : 0 < ep) (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (al : ℝ) (f : ℤ → ℝ),
      RiemannHypothesis.WeylGeneral.IsPolyPhase (r + 2) al f →
      (∀ (a : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ 2 ≤ |((r + 2).factorial : ℝ) * al - (a : ℝ) / q|) →
      ∀ N : ℕ, 0 < N →
        ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), RiemannHypothesis.KusminLandau.e2pi (f n)‖
          ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ep) :=
  RiemannHypothesis.WeylBadlyGeneral.exists_norm_polyPhaseSum_le_of_badlyApproximable r hep hc

/-- **Weyl's exponent in arbitrary degree, unconditionally in `N`**, for a coefficient whose
`d!` multiple is badly approximable. -/
example (r : ℕ) {ep c : ℝ} (hep : 0 < ep) (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ al : ℝ,
      (∀ (a : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ 2 ≤ |((r + 2).factorial : ℝ) * al - (a : ℝ) / q|) →
      ∀ N : ℕ, 0 < N →
        ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
            RiemannHypothesis.KusminLandau.e2pi (al * (n : ℝ) ^ (r + 2))‖
          ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ep) :=
  RiemannHypothesis.WeylBadlyGeneral.exists_norm_monomialSum_le_of_badlyApproximable r hep hc

/-- **The explicit coefficient `√2/d!` in every degree.** -/
example (r : ℕ) {ep : ℝ} (hep : 0 < ep) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
          RiemannHypothesis.KusminLandau.e2pi
            (Real.sqrt 2 / ((r + 2).factorial : ℝ) * (n : ℝ) ^ (r + 2))‖
        ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ep) :=
  RiemannHypothesis.WeylBadlyGeneral.exists_norm_monomialSum_sqrt_two_le r hep

/-! ## M1-WEYL-INTERVAL — Weyl's inequality over an arbitrary interval -/

/-- **A translate of a polynomial phase is a polynomial phase** of the same degree, with the same
leading coefficient. -/
example {d : ℕ} {al : ℝ} {f : ℤ → ℝ} (hf : RiemannHypothesis.WeylGeneral.IsPolyPhase d al f)
    (M : ℤ) :
    RiemannHypothesis.WeylGeneral.IsPolyPhase d al (fun n : ℤ => f (n + M)) :=
  hf.comp_add M

/-- **Weyl's inequality, classical form, over an arbitrary interval**, uniformly in the starting
point `M`. -/
example (r : ℕ) {ep : ℝ} (hep : 0 < ep) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (al : ℝ) (f : ℤ → ℝ) (a : ℤ) (q N : ℕ) (M : ℤ),
      RiemannHypothesis.WeylGeneral.IsPolyPhase (r + 2) al f → 0 < q → IsCoprime (q : ℤ) a →
      |((r + 2).factorial : ℝ) * al - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → 0 < N →
      (q : ℝ) ≤ (N : ℝ) ^ (r + 2) →
      ‖∑ n ∈ Finset.Ico M (M + N), RiemannHypothesis.KusminLandau.e2pi (f n)‖
        ≤ C * (N : ℝ) ^ (1 + ep)
          * (1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ (r + 2)) ^ ((1 : ℝ) / 2 ^ (r + 1)) :=
  RiemannHypothesis.WeylInterval.exists_norm_polyPhaseSum_Ico_le_three_term r hep

/-- **Weyl's exponent for a badly approximable coefficient, over an arbitrary interval.** -/
example (r : ℕ) {ep c : ℝ} (hep : 0 < ep) (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (al : ℝ) (f : ℤ → ℝ),
      RiemannHypothesis.WeylGeneral.IsPolyPhase (r + 2) al f →
      (∀ (a : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ 2 ≤ |((r + 2).factorial : ℝ) * al - (a : ℝ) / q|) →
      ∀ (N : ℕ) (M : ℤ), 0 < N →
        ‖∑ n ∈ Finset.Ico M (M + N), RiemannHypothesis.KusminLandau.e2pi (f n)‖
          ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ep) :=
  RiemannHypothesis.WeylInterval.exists_norm_polyPhaseSum_Ico_le_of_badlyApproximable r hep hc

/-- **The explicit coefficient `√2/d!` over an arbitrary interval.** -/
example (r : ℕ) {ep : ℝ} (hep : 0 < ep) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (M : ℤ), 0 < N →
      ‖∑ n ∈ Finset.Ico M (M + N),
          RiemannHypothesis.KusminLandau.e2pi
            (Real.sqrt 2 / ((r + 2).factorial : ℝ) * (n : ℝ) ^ (r + 2))‖
        ≤ C * (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (r + 1) + ep) :=
  RiemannHypothesis.WeylInterval.exists_norm_monomialSum_Ico_sqrt_two_le r hep

/-! ## M2-LARGE-SIEVE-SIFTED — the large sieve for sifted sets -/

/-- **Orthogonality of the additive characters modulo `q`.** -/
example {q : ℕ} (hq : 0 < q) (m : ℤ) :
    ∑ b ∈ Finset.range q, RiemannHypothesis.KusminLandau.e2pi ((m : ℝ) * b / q)
      = if (q : ℤ) ∣ m then (q : ℂ) else 0 :=
  RiemannHypothesis.LargeSieveSifted.sum_e2pi_mul_div hq m

/-- **Parseval's identity** for the exponential sums of an indicator. -/
example (A : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    ∑ b ∈ Finset.range q, ‖RiemannHypothesis.LargeSieveSifted.indSum A q b‖ ^ 2
      = (q : ℝ) * ∑ r ∈ Finset.range q,
          ((RiemannHypothesis.LargeSieveSifted.fiberCard A q r : ℝ)) ^ 2 :=
  RiemannHypothesis.LargeSieveSifted.sum_normSq_indSum A hq

/-- **The lower bound at a prime modulus.** -/
example (A : Finset ℕ) {p w : ℕ} (hp : p.Prime) (hw : 0 < w)
    (hAw : (A.image (fun n => n % p)).card ≤ w) :
    (A.card : ℝ) ^ 2 * (((p : ℝ) - w) / w)
      ≤ ∑ b ∈ (Finset.range p).filter (fun b => Nat.Coprime b p),
          ‖RiemannHypothesis.LargeSieveSifted.indSum A p b‖ ^ 2 :=
  RiemannHypothesis.LargeSieveSifted.sq_card_mul_le_sum_prime A hp hw hAw

/-- **The large sieve for sifted sets**: a set meeting at most `w p` residue classes modulo every
prime `p ≤ Q` satisfies `|A| ∑_{p ≤ Q} (p − w p)/(w p) ≤ Q² + π N`. -/
example {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ Finset.range N) (w : ℕ → ℕ)
    (hwpos : ∀ p ∈ RiemannHypothesis.LargeSieveSifted.primesUpTo Q, 0 < w p)
    (hw : ∀ p ∈ RiemannHypothesis.LargeSieveSifted.primesUpTo Q,
      (A.image (fun n => n % p)).card ≤ w p) :
    (A.card : ℝ) * ∑ p ∈ RiemannHypothesis.LargeSieveSifted.primesUpTo Q,
        (((p : ℝ) - w p) / w p) ≤ (Q : ℝ) ^ 2 + Real.pi * N :=
  RiemannHypothesis.LargeSieveSifted.card_le_sifted hQ hA w hwpos hw

/-- **A set meeting at most half the classes modulo every prime `p ≤ Q` is small.** -/
example {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ Finset.range N)
    (hhalf : ∀ p ∈ RiemannHypothesis.LargeSieveSifted.primesUpTo Q,
      2 * (A.image (fun n => n % p)).card ≤ p) :
    (A.card : ℝ) * ((RiemannHypothesis.LargeSieveSifted.primesUpTo Q).card : ℝ)
      ≤ (Q : ℝ) ^ 2 + Real.pi * N :=
  RiemannHypothesis.LargeSieveSifted.card_le_sifted_half hQ hA hhalf

/-- **The worked example**: the squares below `N`, with no hypothesis left to the caller. -/
example {N Q : ℕ} (hQ : 2 ≤ Q) :
    ((((Finset.range N).filter (fun n => IsSquare n)).card : ℝ))
        * (((RiemannHypothesis.LargeSieveSifted.primesUpTo Q).erase 2).card : ℝ)
      ≤ 3 * ((Q : ℝ) ^ 2 + Real.pi * N) :=
  RiemannHypothesis.LargeSieveSifted.card_squares_lt_le hQ

/-! ## M2-LARGE-SIEVE-SQUAREFREE — Montgomery's sieve over squarefree moduli -/

/-- **Parseval's identity** for the discrete Fourier transform of an arbitrary complex-valued
function on the residues mod `q`. -/
example {q : ℕ} (hq : 0 < q) (g : ℕ → ℂ) :
    ∑ c ∈ Finset.range q,
        ‖∑ r ∈ Finset.range q, g r * RiemannHypothesis.KusminLandau.e2pi ((r : ℝ) * c / q)‖ ^ 2
      = (q : ℝ) * ∑ r ∈ Finset.range q, ‖g r‖ ^ 2 :=
  RiemannHypothesis.LargeSieveSquarefree.sum_normSq_dft hq g

/-- **The prime step**, now at an arbitrary real shift `x` of the argument. -/
example (A : Finset ℕ) {p w : ℕ} (hp : p.Prime) (hw : 0 < w)
    (hAw : (A.image (fun n => n % p)).card ≤ w) (x : ℝ) :
    ‖RiemannHypothesis.LargeSieveSquarefree.expSum A x‖ ^ 2 * (((p : ℝ) - w) / w)
      ≤ ∑ c ∈ Finset.Ico 1 p,
          ‖RiemannHypothesis.LargeSieveSquarefree.expSum A ((c : ℝ) / p + x)‖ ^ 2 :=
  RiemannHypothesis.LargeSieveSquarefree.sq_norm_expSum_mul_le_sum_prime A hp hw hAw x

/-- **Multiplicativity of the lower bound**: `F(p m) ≥ ((p − w)/w) F(m)` for `p ∤ m`. -/
example (A : Finset ℕ) {p m w : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m) (hw : 0 < w)
    (hAw : (A.image (fun n => n % p)).card ≤ w) :
    (((p : ℝ) - w) / w) * RiemannHypothesis.LargeSieveSquarefree.redSq A m
      ≤ RiemannHypothesis.LargeSieveSquarefree.redSq A (p * m) :=
  RiemannHypothesis.LargeSieveSquarefree.redSq_prime_mul_le A hp hm hpm hw hAw

/-- **The multiplicative lower bound at a squarefree modulus.** -/
example (A : Finset ℕ) (w : ℕ → ℕ) {q : ℕ} (hq : Squarefree q)
    (hwpos : ∀ p ∈ q.primeFactors, 0 < w p) (hwle : ∀ p ∈ q.primeFactors, w p ≤ p)
    (hAw : ∀ p ∈ q.primeFactors, (A.image (fun n => n % p)).card ≤ w p) :
    (A.card : ℝ) ^ 2 * ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p)
      ≤ RiemannHypothesis.LargeSieveSquarefree.redSq A q :=
  RiemannHypothesis.LargeSieveSquarefree.sq_card_mul_prod_le_redSq A w hq hwpos hwle hAw

/-- **Montgomery's sieve**: the sifting sum now runs over all squarefree `q ≤ Q`, with the
multiplicative density `∏_{p ∣ q} (p − w p)/(w p)`. -/
example {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ Finset.range N) (w : ℕ → ℕ)
    (hwpos : ∀ p, p.Prime → p ≤ Q → 0 < w p) (hwle : ∀ p, p.Prime → p ≤ Q → w p ≤ p)
    (hAw : ∀ p, p.Prime → p ≤ Q → (A.image (fun n => n % p)).card ≤ w p) :
    (A.card : ℝ) * ∑ q ∈ RiemannHypothesis.LargeSieveSquarefree.squarefreeUpTo Q,
        ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p)
      ≤ (Q : ℝ) ^ 2 + Real.pi * N :=
  RiemannHypothesis.LargeSieveSquarefree.card_le_sifted_squarefree hQ hA w hwpos hwle hAw

/-- **The half-classes consequence**, now with the count of all squarefree moduli up to `Q`. -/
example {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ Finset.range N)
    (hhalf : ∀ p, p.Prime → p ≤ Q → 2 * (A.image (fun n => n % p)).card ≤ p) :
    (A.card : ℝ) * ((RiemannHypothesis.LargeSieveSquarefree.squarefreeUpTo Q).card : ℝ)
      ≤ (Q : ℝ) ^ 2 + Real.pi * N :=
  RiemannHypothesis.LargeSieveSquarefree.card_le_sifted_squarefree_half hQ hA hhalf

/-- **At least a quarter of the moduli up to `Q` are squarefree.** -/
example (Q : ℕ) :
    (Q : ℝ) / 4 ≤ ((RiemannHypothesis.LargeSieveSquarefree.squarefreeUpTo Q).card : ℝ) :=
  RiemannHypothesis.LargeSieveSquarefree.card_squarefreeUpTo_ge Q

/-- **A set below `N` meeting at most half the residue classes modulo every prime `p ≤ √N` has at
most `34 √N` elements.** -/
example {N : ℕ} (hN : 4 ≤ N) {A : Finset ℕ} (hA : A ⊆ Finset.range N)
    (hhalf : ∀ p, p.Prime → p ≤ Nat.sqrt N → 2 * (A.image (fun n => n % p)).card ≤ p) :
    (A.card : ℝ) ≤ 34 * Real.sqrt N :=
  RiemannHypothesis.LargeSieveSquarefree.card_le_of_sifted_half_sqrt hN hA hhalf

/-! ## M2-BRUN-TITCHMARSH — a Brun–Titchmarsh inequality from the squarefree large sieve -/

/-- **The sifting sum dominates the squarefree harmonic sum.** -/
example (Q : ℕ) :
    ∑ q ∈ RiemannHypothesis.LargeSieveSquarefree.squarefreeUpTo Q, (1 : ℝ) / q
      ≤ RiemannHypothesis.BrunTitchmarsh.siftSum Q :=
  RiemannHypothesis.BrunTitchmarsh.sum_inv_squarefree_le_siftSum Q

/-- **The reciprocals of the non-squarefree `n ≤ Q` sum to at most `(3/4)(log Q + 1)`.** -/
example (Q : ℕ) :
    ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => ¬ Squarefree n), (1 : ℝ) / n
      ≤ 3 / 4 * (Real.log Q + 1) :=
  RiemannHypothesis.BrunTitchmarsh.sum_inv_not_squarefree_le Q

/-- **The sifting sum is at least `(log Q)/4 − 3/4`.** -/
example (Q : ℕ) :
    Real.log Q / 4 - 3 / 4 ≤ RiemannHypothesis.BrunTitchmarsh.siftSum Q :=
  RiemannHypothesis.BrunTitchmarsh.quarter_log_le_siftSum Q

/-- **The large sieve for a set avoiding one residue class modulo every prime `p ≤ Q`.** -/
example {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ Finset.range N)
    (havoid : ∀ p, p.Prime → p ≤ Q → ∃ c < p, ∀ n ∈ A, n % p ≠ c) :
    (A.card : ℝ) * RiemannHypothesis.BrunTitchmarsh.siftSum Q ≤ (Q : ℝ) ^ 2 + Real.pi * N :=
  RiemannHypothesis.BrunTitchmarsh.card_mul_siftSum_le hQ hA havoid

/-- **The harmonic sum splits along `n = d² q` with `q` squarefree.** -/
example (Q : ℕ) :
    ∑ n ∈ Finset.Icc 1 Q, (1 : ℝ) / n
      ≤ (∑ d ∈ Finset.Icc 1 Q, (1 : ℝ) / (d : ℝ) ^ 2)
          * ∑ q ∈ RiemannHypothesis.LargeSieveSquarefree.squarefreeUpTo Q, (1 : ℝ) / q :=
  RiemannHypothesis.BrunTitchmarsh.sum_inv_le_sum_inv_sq_mul_sum_inv_squarefree Q

/-- **The squarefree harmonic sum is at least `(4/7) log Q`.** -/
example (Q : ℕ) :
    4 / 7 * Real.log Q
      ≤ ∑ q ∈ RiemannHypothesis.LargeSieveSquarefree.squarefreeUpTo Q, (1 : ℝ) / q :=
  RiemannHypothesis.BrunTitchmarsh.four_sevenths_log_le_sum_inv_squarefree Q

/-- **The sifting sum is at least `(4/7) log Q`.** -/
example (Q : ℕ) :
    4 / 7 * Real.log Q ≤ RiemannHypothesis.BrunTitchmarsh.siftSum Q :=
  RiemannHypothesis.BrunTitchmarsh.four_sevenths_log_le_siftSum Q

/-- **The reciprocals of the `m ≤ Q` with a prescribed set `P` of prime factors sum to at most
`∏_{p ∈ P} 1/(p − 1)`.** -/
example (Q : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ m ∈ (Finset.Icc 1 Q).filter (fun m => m.primeFactors = P), (1 : ℝ) / m
      ≤ ∏ p ∈ P, 1 / ((p : ℝ) - 1) :=
  RiemannHypothesis.BrunTitchmarsh.sum_inv_primeFactors_eq_le Q P hP

/-- **The sifting sum is at least `log Q`**, the classical bound with the constant `1`. -/
example (Q : ℕ) : Real.log Q ≤ RiemannHypothesis.BrunTitchmarsh.siftSum Q :=
  RiemannHypothesis.BrunTitchmarsh.log_le_siftSum Q

/-- **Brun–Titchmarsh with a non-optimal constant**: uniformly in `x`, the number of primes in
`[x, x + y)` is at most `13 y / log y + √y + 1` once `log y ≥ 4`. -/
example (x : ℕ) {y : ℕ} (hy : 4 ≤ Real.log y) :
    (((Finset.Ico x (x + y)).filter Nat.Prime).card : ℝ)
      ≤ 13 * y / Real.log y + Real.sqrt y + 1 :=
  RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_le x hy

/-- **The same with the constant `9`, once `log y ≥ 24`.** -/
example (x : ℕ) {y : ℕ} (hy : 24 ≤ Real.log y) :
    (((Finset.Ico x (x + y)).filter Nat.Prime).card : ℝ)
      ≤ 9 * y / Real.log y + Real.sqrt y + 1 :=
  RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_le_of_log_ge_24 x hy

/-- **The sieve at a free level `Q ≥ 2`**: the bound `(Q² + π y)/log Q + Q + 1`, uniformly in the
starting point. -/
example (x y : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) :
    (((Finset.Ico x (x + y)).filter Nat.Prime).card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + Real.pi * y) / Real.log Q + Q + 1 :=
  RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_le_of_level x y hQ

/-- **Brun–Titchmarsh with the constant `2π + ε`**, at the sieve level `Q = ⌊√y / log y⌋`. -/
example {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∀ x : ℕ,
      (((Finset.Ico x (x + y)).filter Nat.Prime).card : ℝ)
        ≤ (2 * Real.pi + eps) * y / Real.log y :=
  RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_le_two_pi heps

/-- **A Chebyshev-type upper bound with the constant `2π`**: `π(N) ≤ (2π + ε) N / log N` for all
large `N`. -/
example {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℕ, ∀ N : ℕ, Y ≤ N →
      (((Finset.range N).filter Nat.Prime).card : ℝ)
        ≤ (2 * Real.pi + eps) * N / Real.log N :=
  RiemannHypothesis.BrunTitchmarsh.card_primes_range_le_two_pi heps

/-- **The progression form at a free level `Q ≥ 2`.** -/
example {q a : ℕ} (hq : 1 ≤ q) (ha : a < q) (x y : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) :
    (((Finset.Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + Real.pi * ((y / q + 1 : ℕ) : ℝ)) * q
            / ((q.totient : ℝ) * Real.log Q)
          + Q + 1 :=
  RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_mod_le_of_level hq ha x y hQ

/-- **Brun–Titchmarsh in arithmetic progressions with the constant `2π + ε`**, uniformly in the
starting point, the modulus and the residue. -/
example {eps : ℝ} (heps : 0 < eps) :
    ∃ Y₀ : ℕ, ∀ q a : ℕ, 1 ≤ q → a < q → ∀ x y : ℕ, Y₀ ≤ y / q + 1 →
      (((Finset.Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
        ≤ (2 * Real.pi + eps) * ((q : ℝ) / (q.totient : ℝ)) * ((y / q + 1 : ℕ) : ℝ)
            / Real.log ((y / q + 1 : ℕ) : ℝ) :=
  RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_mod_le_two_pi heps

/-- **A Chebyshev-type upper bound for the prime counting function**: `π(N) ≤ 13 N / log N + √N + 1`
once `log N ≥ 4`. -/
example {N : ℕ} (hN : 4 ≤ Real.log N) :
    (((Finset.range N).filter Nat.Prime).card : ℝ)
      ≤ 13 * N / Real.log N + Real.sqrt N + 1 :=
  RiemannHypothesis.BrunTitchmarsh.card_primes_range_le hN

/-- **The reciprocals of the `n ≤ Q` coprime to `q` are dominated by the coprime sifting sum.** -/
example (q Q : ℕ) :
    ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n q), (1 : ℝ) / n
      ≤ RiemannHypothesis.BrunTitchmarsh.siftSumCoprime q Q :=
  RiemannHypothesis.BrunTitchmarsh.coprime_harmonic_le_siftSumCoprime q Q

/-- **The block bound for the coprime harmonic sum.** -/
example {q : ℕ} (hq : 1 ≤ q) (J : ℕ) :
    ((q.totient : ℝ) / q) * ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / j
      ≤ ∑ n ∈ (Finset.Icc 1 (J * q)).filter (fun n => Nat.Coprime n q), (1 : ℝ) / n :=
  RiemannHypothesis.BrunTitchmarsh.totient_mul_harmonic_le_coprime_harmonic hq J

/-- **The reciprocals of the `n ≤ Q` coprime to `q` sum to at least `(φ(q)/q) log Q`.** -/
example {q : ℕ} (hq : 1 ≤ q) (Q : ℕ) :
    ((q.totient : ℝ) / q) * Real.log Q
      ≤ ∑ m ∈ (Finset.Icc 1 Q).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m :=
  RiemannHypothesis.BrunTitchmarsh.totient_log_le_coprime_harmonic hq Q

/-- **The coprime sifting sum is at least `(φ(q)/q) log Q`.** -/
example {q : ℕ} (hq : 1 ≤ q) (Q : ℕ) :
    ((q.totient : ℝ) / q) * Real.log Q
      ≤ RiemannHypothesis.BrunTitchmarsh.siftSumCoprime q Q :=
  RiemannHypothesis.BrunTitchmarsh.totient_log_le_siftSumCoprime hq Q

/-- **The large sieve for a set avoiding one residue class modulo every prime `p ≤ Q` that does
not divide `q`.** -/
example {N Q q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ Finset.range N)
    (havoid : ∀ p, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c < p, ∀ n ∈ A, n % p ≠ c) :
    (A.card : ℝ) * RiemannHypothesis.BrunTitchmarsh.siftSumCoprime q Q
      ≤ (Q : ℝ) ^ 2 + Real.pi * N :=
  RiemannHypothesis.BrunTitchmarsh.card_mul_siftSumCoprime_le hQ hA havoid

/-- **Brun–Titchmarsh in arithmetic progressions, with a non-optimal constant**: with
`Y = ⌊y/q⌋ + 1` and `Q = ⌊√Y⌋`, the number of primes of `[x, x + y)` congruent to `a` modulo `q`
is at most `4.15 q Y / (φ(q) log Q) + √Y + 1`, uniformly in `x` and `a`. -/
example {q a : ℕ} (hq : 1 ≤ q) (ha : a < q) (x y : ℕ)
    (hQsqrt : 2 ≤ Nat.sqrt (y / q + 1)) :
    (((Finset.Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
      ≤ 4.15 * q * ((y / q + 1 : ℕ) : ℝ)
            / ((q.totient : ℝ) * Real.log (Nat.sqrt (y / q + 1)))
          + Real.sqrt ((y / q + 1 : ℕ) : ℝ) + 1 :=
  RiemannHypothesis.BrunTitchmarsh.card_primes_Ico_mod_le hq ha x y hQsqrt

/-! ## M2-BRUN-TWIN — Brun's twin-prime bound from the squarefree large sieve -/

/-- **The odd squarefree weights dominate the odd harmonic sum**, so their total is at least
`(log X)/2 − 1/2`. -/
example (X : ℕ) :
    Real.log X / 2 - 1 / 2 ≤ RiemannHypothesis.BrunTwinPrimes.oddSieveTotal X :=
  RiemannHypothesis.BrunTwinPrimes.half_log_sub_half_le_oddSieveTotal X

/-- **The coprime pairs carry at least `9/16` of the total weight of the pairs.** -/
example (X : ℕ) :
    9 / 16 * RiemannHypothesis.BrunTwinPrimes.oddSieveTotal X ^ 2
      ≤ ∑ ab ∈ RiemannHypothesis.BrunTwinPrimes.coprimeOddPairs X,
          RiemannHypothesis.BrunTwinPrimes.sieveWeight ab.1 *
            RiemannHypothesis.BrunTwinPrimes.sieveWeight ab.2 :=
  RiemannHypothesis.BrunTwinPrimes.nine_sixteenths_le_sum_coprime_pairs X

/-- **The coprime pairs of odd squarefree numbers up to `X` are dominated by the twin sifting
sum at any `Q ≥ X²`.** -/
example {X Q : ℕ} (hXQ : X * X ≤ Q) :
    ∑ ab ∈ RiemannHypothesis.BrunTwinPrimes.coprimeOddPairs X,
        RiemannHypothesis.BrunTwinPrimes.sieveWeight ab.1 *
          RiemannHypothesis.BrunTwinPrimes.sieveWeight ab.2
      ≤ RiemannHypothesis.BrunTwinPrimes.twinSiftSum Q :=
  RiemannHypothesis.BrunTwinPrimes.sum_coprime_pairs_le_twinSiftSum hXQ

/-- **The twin sifting sum is of order `(log Q)²`.** -/
example {Q : ℕ} (hQ : 1 ≤ Real.log (Nat.sqrt Q)) :
    9 / 16 * (Real.log (Nat.sqrt Q) / 2 - 1 / 2) ^ 2
      ≤ RiemannHypothesis.BrunTwinPrimes.twinSiftSum Q :=
  RiemannHypothesis.BrunTwinPrimes.twinSiftSum_ge hQ

/-- **The large sieve at the twin-prime weights.** -/
example {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ Finset.range N)
    (havoid : ∀ p, p.Prime → p ≤ Q →
      (A.image (fun n => n % p)).card ≤ RiemannHypothesis.BrunTwinPrimes.twinWeight p) :
    (A.card : ℝ) * RiemannHypothesis.BrunTwinPrimes.twinSiftSum Q
      ≤ (Q : ℝ) ^ 2 + Real.pi * N :=
  RiemannHypothesis.BrunTwinPrimes.card_mul_twinSiftSum_le hQ hA havoid

/-- **Brun's twin-prime bound, with a non-optimal constant**: the number of `n < N` with `n` and
`n + 2` both prime is at most `900 N/(log N)² + √N + 1`, once `log N ≥ 32`.  No lower bound for
the number of twin primes is claimed — that is the twin-prime conjecture, and it is open. -/
example {N : ℕ} (hN : 32 ≤ Real.log N) :
    (((Finset.range N).filter (fun n => n.Prime ∧ (n + 2).Prime)).card : ℝ)
      ≤ 900 * N / Real.log N ^ 2 + Real.sqrt N + 1 :=
  RiemannHypothesis.BrunTwinPrimes.card_twinPrimes_le hN

/-! ## M2-BRUN-CONSTANT — Brun's theorem: the reciprocals of the twin primes converge -/

/-- **Every dyadic block of the twin-prime reciprocal sum is `O(1/k²)`.** -/
example (k : ℕ) :
    RiemannHypothesis.BrunConstant.blockSum k ≤ 3753 / ((k : ℝ) + 1) ^ 2 :=
  RiemannHypothesis.BrunConstant.blockSum_le k

/-- **Brun's bound**: the reciprocals of the twin primes below `N` sum to at most `6600`,
uniformly in `N`.  The constant is not sharp: the Brun constant is `1.902…`. -/
example (N : ℕ) :
    ∑ n ∈ (Finset.range N).filter (fun n => n.Prime ∧ (n + 2).Prime), (1 : ℝ) / (n : ℝ) ≤ 6600 :=
  RiemannHypothesis.BrunConstant.sum_inv_twinPrimes_le N

/-- **Brun's theorem**: the series `∑ 1/n` over the `n` with `n` and `n + 2` both prime
converges.  Nothing follows about the number of twin primes from below: the twin-prime
conjecture is open. -/
example : Summable (fun n : ℕ => if n.Prime ∧ (n + 2).Prime then (1 : ℝ) / (n : ℝ) else 0) :=
  RiemannHypothesis.BrunConstant.summable_twinInv

/-- **The sum of the reciprocals of the twin primes is at most `6600`.** -/
example :
    ∑' n : ℕ, (if n.Prime ∧ (n + 2).Prime then (1 : ℝ) / (n : ℝ) else 0) ≤ 6600 :=
  RiemannHypothesis.BrunConstant.tsum_twinInv_le

/-- **There are infinitely many primes `p` with `p + 2` composite.**  A consequence of Brun's
theorem: the sum of the prime reciprocals diverges while its twin part converges.  Nothing
follows about the twin primes themselves. -/
example : {p : ℕ | p.Prime ∧ ¬ (p + 2).Prime}.Infinite :=
  RiemannHypothesis.BrunConstant.infinite_setOf_prime_not_prime_add_two

/-! ## M1-ALMOST-ALL-STRIP — Carlson's density theorem in its `o(T)` form -/

/-- **`N(σ, T) ≤ ε T` for every fixed `σ > 1/2` and every `ε > 0`, for `T` large.**  Zeroes are
counted without multiplicity.  This is strictly stronger than the Bohr–Landau `O(T)` of
`M2-BOHR-LANDAU`. -/
example {σ ε : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T} : ℝ)) ≤ ε * T :=
  RiemannHypothesis.exists_ncard_zerosRightOf_le_eps h0 h1 hε

/-- The limit form: `N(σ, T) / T → 0`. -/
example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    Tendsto (fun T : ℝ =>
        (Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T} : ℝ) / T)
      atTop (𝓝 0) :=
  RiemannHypothesis.tendsto_ncard_zerosRightOf_div_atTop h0 h1

/-- **The Prop of `RiemannHypothesis/Partial.lean` that the row is measured against.** -/
example : ∀ δ : ℝ, 0 < δ →
    Tendsto (fun T : ℝ => (Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T ∧
        δ ≤ |s.re - 1 / 2|} : ℝ) / T) atTop (𝓝 0) :=
  RiemannHypothesis.almostAllZerosNearCriticalLine

/-- The analytic input: the mean square of `ζ M_y − 1` on a vertical segment *inside* the
critical strip, for every mollifier length `y ≥ y₀`. -/
example {σ₀ ε : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) (hε : 0 < ε) :
    ∃ y₀ : ℕ, 4 ≤ y₀ ∧ ∀ y : ℕ, y₀ ≤ y → ∃ b₀ : ℝ, 6 ≤ b₀ ∧
      ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 6 → ∀ a b : ℝ, 1 ≤ a → a ≤ b → b₀ ≤ b →
        (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
            RiemannHypothesis.Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) ≤ ε * b :=
  RiemannHypothesis.exists_integral_normSq_zeta_mul_mollifier_sub_one_le h0 h1 hε

/-! ## M2-DENSITY-POWER-SAVING — Carlson's density theorem with a power saving -/

/-- **`N(σ, T) ≤ C T^(1−c)` with `c > 0`, for every fixed `1/2 < σ < 1` and every `T ≥ 1`.**
Zeroes are counted without multiplicity.  This is strictly stronger than the `o(T)` of
`M1-ALMOST-ALL-STRIP`; the saving `c` is at least `(σ − 1/2)²/64`. -/
example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ (σ - 1 / 2) ^ 2 / 64 ≤ c ∧ ∀ T : ℝ, 1 ≤ T →
      ((Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T} : ℝ))
        ≤ C * T ^ (1 - c) :=
  RiemannHypothesis.exists_ncard_zerosRightOf_le_rpow h0 h1

/-- **The same with the exponent named: `N(σ, T) ≤ C(σ) T^(1 − (σ−1/2)²/64)`.**  Only the
constant is left implicit; the saving is an explicit function of `σ` which degrades to `0` as
`σ ↓ 1/2`. -/
example {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T} : ℝ))
        ≤ C * T ^ (1 - (σ - 1 / 2) ^ 2 / 64) :=
  RiemannHypothesis.ncard_zerosRightOf_le_rpow_explicit h0 h1

/-- The two-sided form with the explicit exponent. -/
example {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ δ ≤ |ρ.re - 1 / 2| ∧ 0 < ρ.im ∧ ρ.im ≤ T} : ℝ))
        ≤ C * T ^ (1 - δ ^ 2 / 64) :=
  RiemannHypothesis.ncard_zerosOffCriticalLine_le_rpow_explicit hδ0 hδ1

/-- The two-sided form: the zeroes at distance at least `δ` from the critical line. -/
example {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ δ ≤ |ρ.re - 1 / 2| ∧ 0 < ρ.im ∧ ρ.im ≤ T} : ℝ))
        ≤ C * T ^ (1 - c) :=
  RiemannHypothesis.exists_ncard_zerosOffCriticalLine_le_rpow hδ0 hδ1

/-- The analytic input: the mean square of `ζ M_y − 1` for a mollifier length that is allowed
to grow with the height, with an explicit rate in both parameters.  Both exponents are
explicit in `θ = σ₀ − 1/2`: length up to `4 b^{θ/8}`, saving at least `3θ/8`. -/
example {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C c γ : ℝ, 0 < C ∧ 0 < c ∧ c < 1 ∧ 0 < γ ∧ 3 * (σ₀ - 1 / 2) / 8 ≤ c ∧
      γ = (σ₀ - 1 / 2) / 8 ∧ ∃ b₀ : ℝ, 6 ≤ b₀ ∧
      ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 6 → ∀ y : ℕ, 1 ≤ y → ∀ a b : ℝ, 1 ≤ a → a ≤ b → b₀ ≤ b →
        (y : ℝ) ≤ 4 * b ^ γ →
        (∫ t in a..b, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
            RiemannHypothesis.Mollifier.mollifier y ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
          ≤ C * (b * (y : ℝ) ^ (-(σ₀ - 1 / 2)) + b ^ (1 - c)) :=
  RiemannHypothesis.exists_integral_normSq_zeta_mul_mollifier_sub_one_le_rpow h0 h1


/-! ## The two-thirds theorem in absolute form (RiemannHypothesis/Zeta23Verification.lean)

The vendored two-thirds theorem is a ratio; these pins are the statements that give it an
absolute size, so that the denominator cannot be empty. -/

/-- Riemann–von Mangoldt for the dyadic window, in this repository's counting functions. -/
example : ∃ C T₀ : ℝ, ∀ T ≥ T₀,
    |(RiemannHypothesis.windowCount T (2 * T) : ℝ) -
        T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) + 2 * Real.log 2 - 1)|
      ≤ C * Real.log T :=
  RiemannHypothesis.windowCount_sub_mainTerm_le

/-- Theorem A in absolute form: at least `(T/8π)·log T` distinct zeroes of `ζ` on the critical
line have ordinate in `(T, 2T]`, for all large `T`. -/
example : ∀ᶠ T in Filter.atTop,
    T / (8 * Real.pi) * Real.log T ≤ (RiemannHypothesis.windowCountOnLine T (2 * T) : ℝ) :=
  RiemannHypothesis.eventually_windowCountOnLine_ge

/-- Theorem B in absolute form: the same count of *simple* zeroes on the line. -/
example : ∀ᶠ T in Filter.atTop,
    T / (8 * Real.pi) * Real.log T ≤ (RiemannHypothesis.windowCountSimpleOnLine T (2 * T) : ℝ) :=
  RiemannHypothesis.eventually_windowCountSimpleOnLine_ge


/-! ## The Riemann hypothesis as an eventual counting statement
(RiemannHypothesis/EventualCountingCriterion.lean) -/

/-- The conjecture holds iff the on-line and the total distinct counts agree for all large `T`. -/
example : RiemannHypothesis.ZetaStripForm ↔ ∀ᶠ T in Filter.atTop,
    RiemannHypothesis.windowCountOnLine 0 T = RiemannHypothesis.windowCountDistinct 0 T :=
  RiemannHypothesis.zetaStripForm_iff_eventually_windowCountOnLine_eq

/-- The same with both sides counted with multiplicity: the denominator of the two-thirds
theorem. -/
example : RiemannHypothesis.ZetaStripForm ↔ ∀ᶠ T in Filter.atTop,
    ∑ᶠ ρ ∈ RiemannHypothesis.windowZeros 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2},
      RiemannHypothesis.zeroMultiplicity ρ = RiemannHypothesis.windowCount 0 T :=
  RiemannHypothesis.zetaStripForm_iff_eventually_windowCountOnLine_eq_windowCount

/-! ## M1-WEYL-DISCREPANCY — a rate of convergence for equidistribution modulo one -/

/-- **The quantitative Weyl criterion**: the average of a periodic Lipschitz test function along
the first `N` terms differs from its mean by at most `L δ + 1/(2Mδ)` plus twice the normalized
exponential sums below `M`. -/
example {g : ℝ → ℝ} {L δ : ℝ} {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t, g t ≤ 1) (hper : ∀ t, g (t + 1) = g t)
    (hlip : ∀ u v, |g u - g v| ≤ L * |u - v|) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (x : ℕ → ℝ) :
    |(∑ n ∈ Finset.range N, g (x n)) / N - ∫ t in (0 : ℝ)..1, g t|
      ≤ L * δ + 1 / (2 * M * δ)
        + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (M - 1),
            ‖∑ n ∈ Finset.range N,
                Complex.exp ((2 * Real.pi * ((((m : ℤ) : ℝ)) * x n) : ℝ) * Complex.I)‖ / N :=
  RiemannHypothesis.WeylDiscrepancy.abs_avg_sub_integral_le hM hN hg0 hg1 hper hlip hδ0 hδ x

/-- **The discrepancy bound**: with all parameters tied to a single `K`, the proportion of the
first `N` fractional parts in `[a, b)` differs from `b − a` by at most `4/K` plus twice the
normalized exponential sums below `K⁴`. -/
example (x : ℕ → ℝ) {a b : ℝ} {K N : ℕ} (hK : 2 ≤ K) (hN : 0 < N)
    (ha : 1 / (K : ℝ) < a) (hb : b + 1 / (K : ℝ) < 1) (hab : a + 2 / (K : ℝ) ≤ b) :
    |((((Finset.range N).filter fun n : ℕ =>
          a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card : ℝ)) / N - (b - a)|
      ≤ 4 / K + 2 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
          ‖∑ n ∈ Finset.range N,
              Complex.exp ((2 * Real.pi * ((((m : ℤ) : ℝ)) * x n) : ℝ) * Complex.I)‖ / N :=
  RiemannHypothesis.WeylDiscrepancy.abs_countIn_div_sub_le_pow x hK hN ha hb hab

/-- **An explicit rate**: for a badly approximable `α` the discrepancy of `α n` on an interval is
at most `(4 + 1/c)/K` as soon as `K⁹ ≤ N`. -/
example {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ |(m : ℝ) * α - round ((m : ℝ) * α)|)
    {a b : ℝ} {K N : ℕ} (hK : 2 ≤ K) (hNK : K ^ 9 ≤ N) (ha : 1 / (K : ℝ) < a)
    (hb : b + 1 / (K : ℝ) < 1) (hab : a + 2 / (K : ℝ) ≤ b) :
    |((((Finset.range N).filter fun n : ℕ =>
          a ≤ Int.fract (α * n) ∧ Int.fract (α * n) < b).card : ℝ)) / N - (b - a)|
      ≤ (4 + 1 / c) / K :=
  RiemannHypothesis.WeylDiscrepancy.abs_countIn_div_sub_le_linear hc hbad hK hNK ha hb hab

/-! ## M1-WEYL-DISCREPANCY-GENERAL -/

/-- **The discrepancy bound for every subinterval**: no restriction on the position or the
length of `[a, b) ⊆ [0, 1]`, at the cost of the constant `20` in place of `4`. -/
example (x : ℕ → ℝ) {a b : ℝ} {K N : ℕ} (hK : 8 ≤ K) (hN : 0 < N) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    |((((Finset.range N).filter fun n : ℕ =>
          a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card : ℝ)) / N - (b - a)|
      ≤ 20 / K + 4 * ∑ m ∈ Finset.Icc (1 : ℕ) (K ^ 4 - 1),
          ‖∑ n ∈ Finset.range N,
              Complex.exp ((2 * Real.pi * ((((m : ℤ) : ℝ)) * x n) : ℝ) * Complex.I)‖ / N :=
  RiemannHypothesis.WeylDiscrepancy.abs_countIn_div_sub_le_pow_of_le x hK hN ha hab hb

/-- **An explicit rate for every interval**: for a badly approximable `α` the discrepancy of
`α n`, over all subintervals of `[0, 1]`, is at most `(20 + 2/c)/K` as soon as `K⁹ ≤ N`. -/
example {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ |(m : ℝ) * α - round ((m : ℝ) * α)|)
    {a b : ℝ} {K N : ℕ} (hK : 8 ≤ K) (hNK : K ^ 9 ≤ N) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((((Finset.range N).filter fun n : ℕ =>
          a ≤ Int.fract (α * n) ∧ Int.fract (α * n) < b).card : ℝ)) / N - (b - a)|
      ≤ (20 + 2 / c) / K :=
  RiemannHypothesis.WeylDiscrepancy.abs_countIn_div_sub_le_linear_of_le hc hbad hK hNK ha hab hb

/-- The concrete quadratic instance `α = √2/2`, for every subinterval of `[0, 1]`. -/
example {a b : ℝ} {K N : ℕ} (hK : 8 ≤ K) (hN : 0 < N) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((((Finset.range N).filter fun n : ℕ =>
          a ≤ Int.fract (Real.sqrt 2 / 2 * (n : ℝ) ^ 2) ∧
            Int.fract (Real.sqrt 2 / 2 * (n : ℝ) ^ 2) < b).card : ℝ)) / N - (b - a)|
      ≤ 20 / K
        + 4 * (K : ℝ) ^ 4 * Real.sqrt ((64 * (K : ℝ) ^ 4 + 26) * N * (1 + Real.log N)) / N :=
  RiemannHypothesis.WeylDiscrepancy.abs_countIn_div_sub_le_sqrt_two_of_le hK hN ha hab hb

/-! ## M1-DISCREPANCY -/

/-- **The discrepancy** is the supremum of the interval deviations over all subintervals of
`[0, 1]`, and it dominates each of them. -/
example (x : ℕ → ℝ) (N : ℕ) :
    RiemannHypothesis.WeylDiscrepancy.discrepancy x N =
      sSup {d : ℝ | ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
        d = |((((Finset.range N).filter fun n : ℕ =>
              a ≤ Int.fract (x n) ∧ Int.fract (x n) < b).card : ℝ)) / N - (b - a)|} := rfl

/-- The discrepancy is not vacuous: the constant sequence `0` has discrepancy at least `1/2`. -/
example (N : ℕ) :
    (1 : ℝ) / 2 ≤ RiemannHypothesis.WeylDiscrepancy.discrepancy (fun _ : ℕ => (0 : ℝ)) N :=
  RiemannHypothesis.WeylDiscrepancy.half_le_discrepancy_const_zero N

/-- **A power saving for the discrepancy of `α n`**: for a badly approximable `α` and `N ≥ 8⁹`,
`D_N ≤ 2 (20 + 2/c) N^(−1/9)`. -/
example {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ m : ℕ, 1 ≤ m → c / m ≤ |(m : ℝ) * α - round ((m : ℝ) * α)|)
    {N : ℕ} (hN : 8 ^ 9 ≤ N) :
    RiemannHypothesis.WeylDiscrepancy.discrepancy (fun n : ℕ => α * n) N
      ≤ 2 * (20 + 2 / c) * (N : ℝ) ^ (-(1 : ℝ) / 9) :=
  RiemannHypothesis.WeylDiscrepancy.discrepancy_linear_le_rpow hc hbad hN

/-! ## M1-DISCREPANCY-CRITERION -/

/-- **Weyl's criterion in discrepancy form**: a sequence is equidistributed modulo one if and
only if its discrepancy tends to `0`. -/
example (x : ℕ → ℝ) :
    RiemannHypothesis.WeylCriterion.EquidistributedMod1 x ↔
      Tendsto (fun N : ℕ => RiemannHypothesis.WeylDiscrepancy.discrepancy x N) atTop (𝓝 0) :=
  RiemannHypothesis.WeylDiscrepancy.equidistributedMod1_iff_tendsto_discrepancy x

/-- For every irrational `α` the discrepancy of `α n²` tends to `0`. -/
example {α : ℝ} (hα : Irrational α) :
    Tendsto (fun N : ℕ =>
      RiemannHypothesis.WeylDiscrepancy.discrepancy (fun n : ℕ => α * (n : ℝ) ^ 2) N) atTop
      (𝓝 0) :=
  RiemannHypothesis.WeylDiscrepancy.tendsto_discrepancy_quadratic hα

/-- The criterion is not vacuous: the discrepancy of the constant sequence `0` does not tend to
`0`. -/
example : ¬ Tendsto
    (fun N : ℕ => RiemannHypothesis.WeylDiscrepancy.discrepancy (fun _ : ℕ => (0 : ℝ)) N) atTop
    (𝓝 0) :=
  RiemannHypothesis.WeylDiscrepancy.not_tendsto_discrepancy_const_zero


/-! ## M1-KOKSMA -/

/-- **Koksma's inequality**: for a nondecreasing integrand the error of the average along the
first `N` terms is at most `(f 1 - f 0)` times the discrepancy.  No continuity is assumed. -/
example {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1)) (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ (f 1 - f 0) * RiemannHypothesis.WeylDiscrepancy.discrepancy x N :=
  RiemannHypothesis.WeylDiscrepancy.koksma_monotone hmono x hN

/-- Koksma's inequality for a difference of two nondecreasing functions. -/
example {f g h : ℝ → ℝ} (hfgh : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = g t - h t)
    (hgmono : MonotoneOn g (Set.Icc 0 1)) (hhmono : MonotoneOn h (Set.Icc 0 1))
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ ((g 1 - g 0) + (h 1 - h 0)) * RiemannHypothesis.WeylDiscrepancy.discrepancy x N :=
  RiemannHypothesis.WeylDiscrepancy.koksma_sub_monotone hfgh hgmono hhmono x hN

/-- Koksma's inequality for a Lipschitz integrand, with the constant `3 L`. -/
example {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ 3 * L * RiemannHypothesis.WeylDiscrepancy.discrepancy x N :=
  RiemannHypothesis.WeylDiscrepancy.koksma_lipschitz hL hlip x hN

/-- A sequence of vanishing discrepancy integrates every monotone function correctly; the
concrete instance is `α n²` for an irrational `α`. -/
example {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1)) {α : ℝ} (hα : Irrational α) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (α * (n : ℝ) ^ 2))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) :=
  RiemannHypothesis.WeylDiscrepancy.tendsto_average_quadratic hmono hα


/-! ## M1-KOKSMA-VARIATION -/

/-- For a nondecreasing integrand the total variation on `[0,1]` is the rise. -/
example {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Icc 0 1)) :
    RiemannHypothesis.WeylDiscrepancy.unitVariation f = f 1 - f 0 :=
  RiemannHypothesis.WeylDiscrepancy.unitVariation_of_monotoneOn hmono

/-- **Koksma's inequality with the total variation**: for every integrand of bounded variation on
`[0,1]` the error of the average along the first `N` terms is at most
`(2 V(f) - |f 1 - f 0|)` times the discrepancy.  No continuity is assumed. -/
example {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) (x : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ (2 * RiemannHypothesis.WeylDiscrepancy.unitVariation f - |f 1 - f 0|)
          * RiemannHypothesis.WeylDiscrepancy.discrepancy x N :=
  RiemannHypothesis.WeylDiscrepancy.koksma_variation hf x hN

/-- The same, in the readable form `2 V(f) D_N(x)`. -/
example {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) (x : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ 2 * RiemannHypothesis.WeylDiscrepancy.unitVariation f
          * RiemannHypothesis.WeylDiscrepancy.discrepancy x N :=
  RiemannHypothesis.WeylDiscrepancy.koksma_variation_le hf x hN

/-- Koksma's inequality for a Lipschitz integrand, with the constant `2 L`. -/
example {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ 2 * L * RiemannHypothesis.WeylDiscrepancy.discrepancy x N :=
  RiemannHypothesis.WeylDiscrepancy.koksma_lipschitz_two hL hlip x hN

/-- A sequence of vanishing discrepancy integrates every function of bounded variation correctly;
the concrete instance is `α n²` for an irrational `α`. -/
example {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) {α : ℝ} (hα : Irrational α) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (α * (n : ℝ) ^ 2))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) :=
  RiemannHypothesis.WeylDiscrepancy.tendsto_average_quadratic_variation hf hα


/-! ## M1-KOKSMA-LIPSCHITZ-SHARP -/

/-- The cell deviation sum for an arbitrary weight sequence: summation by parts against the
deviations of the tail intervals. -/
example (x : ℕ → ℝ) (a : ℕ → ℝ) {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    |∑ j ∈ Finset.range K,
        a j * ((RiemannHypothesis.WeylCount.countIn x ((j : ℝ) / K) (((j : ℝ) + 1) / K) N : ℝ) / N
          - 1 / K)|
      ≤ (∑ j ∈ Finset.range K, |a (j + 1) - a j|)
          * RiemannHypothesis.WeylDiscrepancy.discrepancy x N :=
  RiemannHypothesis.WeylDiscrepancy.abs_sum_weight_cellDev_le x a hK hN

/-- **Koksma's inequality for a Lipschitz integrand, with the sharp constant `L`.** -/
example {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (x n))) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ L * RiemannHypothesis.WeylDiscrepancy.discrepancy x N :=
  RiemannHypothesis.WeylDiscrepancy.koksma_lipschitz_sharp hL hlip x hN


/-! ## M2-MEANVALUE-WELLSPACED — the mean value theorem for well-spaced frequencies -/

/-- The row sums of the Gaussian kernel over `δ`-separated frequencies. -/
example {ι : Type} [DecidableEq ι] {S : Finset ι} {lam : ι → ℝ} {δ b : ℝ} (hδ : 0 < δ)
    (hb : 0 < b) (hsep : RiemannHypothesis.WellSpaced.Separated S lam δ) {r : ι} (hr : r ∈ S) :
    ∑ s ∈ S, Real.exp (-(lam r - lam s) ^ 2 / (4 * b))
      ≤ 1 + 2 * Real.sqrt (Real.pi * b) / δ :=
  RiemannHypothesis.WellSpaced.rowSum_le hδ hb hsep hr

/-- **The mean value theorem for well-spaced frequencies**, with the explicit constant. -/
example {ι : Type} {S : Finset ι} {lam : ι → ℝ} (x : ι → ℂ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    (hsep : RiemannHypothesis.WellSpaced.Separated S lam δ) :
    (∫ t in (-T)..T, ‖RiemannHypothesis.WellSpaced.expSum S lam x t‖ ^ 2)
      ≤ Real.exp 1 * (Real.sqrt Real.pi * T + 2 * Real.pi / δ) * ∑ r ∈ S, ‖x r‖ ^ 2 :=
  RiemannHypothesis.WellSpaced.integral_normSq_expSum_le x hδ hT hsep

/-- The same with the round constant `18 (T + 1/δ)`. -/
example {ι : Type} {S : Finset ι} {lam : ι → ℝ} (x : ι → ℂ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    (hsep : RiemannHypothesis.WellSpaced.Separated S lam δ) :
    (∫ t in (-T)..T, ‖RiemannHypothesis.WellSpaced.expSum S lam x t‖ ^ 2)
      ≤ 18 * (T + 1 / δ) * ∑ r ∈ S, ‖x r‖ ^ 2 :=
  RiemannHypothesis.WellSpaced.integral_normSq_expSum_le_mv x hδ hT hsep

/-! ## M2-VAUGHAN — Vaughan's identity -/

/-- **Vaughan's identity** as an identity of arithmetic functions. -/
example (U V : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)
      = RiemannHypothesis.Vaughan.truncLE ArithmeticFunction.vonMangoldt U
        + ArithmeticFunction.log *
            RiemannHypothesis.Vaughan.truncLE
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V
        - RiemannHypothesis.Vaughan.truncLE ArithmeticFunction.vonMangoldt U *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            RiemannHypothesis.Vaughan.truncLE
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V
        + RiemannHypothesis.Vaughan.truncGT ArithmeticFunction.vonMangoldt U *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            RiemannHypothesis.Vaughan.truncGT
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V :=
  RiemannHypothesis.Vaughan.vaughan_identity U V

/-! ## M2-CORPUS-INSTANCE — the counting system of `CorpusCeiling` holds of the zeroes of `ζ` -/

/-- The instance exists: the zeroes of `ζ` are a model of `ZeroCorpus 0.33`. -/
noncomputable example : RiemannHypothesis.ZeroCorpus 0.33 := RiemannHypothesis.zetaCorpus

/-- Its five counting functions are the repository's counting functions of `ζ`. -/
example : RiemannHypothesis.zetaCorpus.total
    = fun T : ℝ => (RiemannHypothesis.windowCount 0 T : ℝ) := rfl

example : RiemannHypothesis.zetaCorpus.distinct
    = fun T : ℝ => (RiemannHypothesis.windowCountDistinct 0 T : ℝ) := rfl

example : RiemannHypothesis.zetaCorpus.onLine
    = fun T : ℝ => (RiemannHypothesis.windowCountOnLine 0 T : ℝ) := rfl

example : RiemannHypothesis.zetaCorpus.off
    = fun T : ℝ => (RiemannHypothesis.windowCountOffLine 0 T : ℝ) := rfl

/-- The `offAt` field counts what the density theorems bound. -/
example {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    (RiemannHypothesis.offAtSet δ T).ncard
      = (RiemannHypothesis.zerosOffCriticalLine δ T).ncard :=
  RiemannHypothesis.ncard_offAtSet_eq hδ T

/-- Soundness for `ζ`: at most `33 %` of the zeroes of a dyadic window are off the line. -/
example : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (RiemannHypothesis.windowCountOffLine T (2 * T) : ℝ)
      ≤ 0.33 * (RiemannHypothesis.windowCount T (2 * T) : ℝ) :=
  RiemannHypothesis.zeta_windowOff_le

/-- The Riemann hypothesis is exactly the vanishing of the off-line count of the corpus. -/
example : RiemannHypothesis.ZetaStripForm
    ↔ RiemannHypothesis.RHCounts RiemannHypothesis.zetaCorpus :=
  RiemannHypothesis.zetaStripForm_iff_rhCounts_zetaCorpus

/-- **Relative independence**: the corpus that `ζ` provably satisfies has a model violating the
Riemann hypothesis. -/
example : (∃ Z : RiemannHypothesis.ZeroCorpus 0.33, ¬ RiemannHypothesis.RHCounts Z)
    ∧ (RiemannHypothesis.ZetaStripForm
      ↔ RiemannHypothesis.RHCounts RiemannHypothesis.zetaCorpus) :=
  RiemannHypothesis.rh_not_derivable_from_zeta_corpus

/-! ## M3-VINOGRADOV-SYSTEM — the Vinogradov system and its invariances -/

/-- Translation invariance of the Vinogradov system. -/
example {k s : ℕ} {x y : Fin s → ℕ}
    (h : RiemannHypothesis.Vinogradov.VinogradovEq k x y) (a : ℕ) :
    RiemannHypothesis.Vinogradov.VinogradovEq k (fun i => x i + a) (fun i => y i + a) :=
  RiemannHypothesis.Vinogradov.vinogradovEq_translate h a

/-- The diagonal lower bound `X^s ≤ J_{s,k}(X)`. -/
example (k s X : ℕ) : X ^ s ≤ RiemannHypothesis.Vinogradov.vinogradovCount k s X :=
  RiemannHypothesis.Vinogradov.pow_card_le_vinogradovCount k s X

/-- The count is not vacuous: `J_{1,1}(X) = X`. -/
example (X : ℕ) : RiemannHypothesis.Vinogradov.vinogradovCount 1 1 X = X :=
  RiemannHypothesis.Vinogradov.vinogradovCount_one_one X

/-! ## The conjecture itself is *not* claimed

There is deliberately no term of type `RiemannHypothesis.ZetaForm` anywhere in this
repository, and no `example` above produces one.  Every statement pinned here is either an
equivalence between formulations, a symmetry, or a classical estimate.  The audit script
checks separately that no proof in the library is left open. -/

end RiemannHypothesisRevalidation
