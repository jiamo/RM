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

/-! ## The conjecture itself is *not* claimed

There is deliberately no term of type `RiemannHypothesis.ZetaForm` anywhere in this
repository, and no `example` above produces one.  Every statement pinned here is either an
equivalence between formulations, a symmetry, or a classical estimate.  The audit script
checks separately that no proof in the library is left open. -/

end RiemannHypothesisRevalidation
