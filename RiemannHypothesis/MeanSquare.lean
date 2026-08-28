/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The mean square of a Dirichlet series, and of `ζ`, on a line of absolute convergence

If the Dirichlet series `D(s) = ∑ aₙ (n+1)^(-s)` converges absolutely on the line `re s = σ`,
then squaring it against its own conjugate and integrating gives the classical mean value
theorem

`(1/T) ∫₀ᵀ |D(σ + i t)|² dt → ∑ |aₙ|² (n+1)^(-2σ)`  as  `T → ∞`,

the diagonal terms `m = n` of the resulting double series surviving the average while every
off-diagonal term oscillates, its average `(1/T) ∫₀ᵀ e^{i t log((n+1)/(m+1))} dt` tending
to `0`.  For `aₙ = 1` and `σ > 1` this is the first moment computation for the zeta function,

`(1/T) ∫₀ᵀ |ζ(σ + i t)|² dt → ζ(2σ)`.

## Main results

* `meanSquareAvg_tendsto_tsum_of_summable` : the mean value theorem for a Dirichlet series
  with absolutely convergent coefficients.
* `meanSquareAvg_tendsto_tsum` : the specialization `(1/T) ∫₀ᵀ ‖ζ(σ + i t)‖² dt →
  ∑' n, (n+1)^(-2σ)` for `σ > 1`.
* `meanSquareAvg_tendsto_riemannZeta` : the same limit written as `ζ(2σ)`.

Along the way:

* `oscAvg_tendsto_zero` : `(1/T) ∫₀ᵀ e^{i θ t} dt → 0` for `θ ≠ 0`.
* `normSq_dirichletLineSum_eq_tsum`, `normSq_riemannZeta_line_eq_tsum` : the expansion of
  `|D(σ + i t)|²` (resp. of `|ζ(σ + i t)|²`) as an absolutely convergent double series.
* `integral_normSq_dirichletLineSum`, `integral_normSq_riemannZeta_line` : the termwise
  integration of that expansion over `[0, T]`.
-/

noncomputable section

open Complex MeasureTheory Filter Topology

namespace RiemannHypothesis

/-- The point `σ + i t` of the vertical line with real part `σ`. -/
def linePoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

@[simp] lemma linePoint_re (σ t : ℝ) : (linePoint σ t).re = σ := by
  simp [linePoint]

/-- The modulus `((m+1)(n+1))^(-σ)` of the term `(m, n)` of the double Dirichlet series
of `|D(σ + i t)|²`. -/
def msCoeff (σ : ℝ) (p : ℕ × ℕ) : ℝ := (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) ^ (-σ)

/-- The frequency `log((n+1)/(m+1))` of the term `(m, n)` of the double Dirichlet series
of `|D(σ + i t)|²`. -/
def msFreq (p : ℕ × ℕ) : ℝ := Real.log ((p.2 : ℝ) + 1) - Real.log ((p.1 : ℝ) + 1)

lemma msCoeff_nonneg (σ : ℝ) (p : ℕ × ℕ) : 0 ≤ msCoeff σ p :=
  Real.rpow_nonneg (by positivity) _

lemma msCoeff_eq_mul (σ : ℝ) (p : ℕ × ℕ) :
    msCoeff σ p = ((p.1 : ℝ) + 1) ^ (-σ) * ((p.2 : ℝ) + 1) ^ (-σ) := by
  rw [msCoeff, Real.mul_rpow (by positivity) (by positivity)]

lemma msFreq_eq_zero_iff (p : ℕ × ℕ) : msFreq p = 0 ↔ p.1 = p.2 := by
  constructor
  · intro h
    have h1 : Real.log ((p.2 : ℝ) + 1) = Real.log ((p.1 : ℝ) + 1) := by
      simpa [msFreq, sub_eq_zero] using h
    have h2 : ((p.2 : ℝ) + 1) = ((p.1 : ℝ) + 1) :=
      Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
        (by simp only [Set.mem_Ioi]; positivity) h1
    have h3 : (p.2 : ℝ) = (p.1 : ℝ) := by linarith
    exact_mod_cast h3.symm
  · intro h; simp [msFreq, h]

/-- The series `∑ (n+1)^(-σ)` converges for `σ > 1`. -/
lemma summable_natAddOne_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := Real.summable_nat_rpow.mpr (by linarith)
  refine (h.comp_injective (add_left_injective 1)).congr fun n => ?_
  simp only [Function.comp_apply]
  push_cast
  ring_nf

/-! ## The oscillatory integral -/

/-- The oscillatory integral `∫₀ᵀ e^{i θ t} dt`. -/
def oscIntegral (θ T : ℝ) : ℂ := ∫ t in (0 : ℝ)..T, Complex.exp ((θ * t : ℝ) * I)

lemma oscIntegral_zero_freq (T : ℝ) : oscIntegral 0 T = (T : ℂ) := by
  simp [oscIntegral]

lemma oscIntegral_eq {θ : ℝ} (hθ : θ ≠ 0) (T : ℝ) :
    oscIntegral θ T = (Complex.exp ((θ * T : ℝ) * I) - 1) / ((θ : ℂ) * I) := by
  have hc : ((θ : ℂ) * I) ≠ 0 := by
    simp [hθ, Complex.I_ne_zero, Complex.ofReal_eq_zero]
  have key := integral_exp_mul_complex (a := (0 : ℝ)) (b := T) (c := (θ : ℂ) * I) hc
  rw [oscIntegral]
  have h1 : ∀ t : ℝ, Complex.exp ((θ * t : ℝ) * I) = Complex.exp (((θ : ℂ) * I) * (t : ℂ)) := by
    intro t; push_cast; ring_nf
  simp_rw [h1]
  rw [key]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- The trivial bound `‖∫₀ᵀ e^{i θ t} dt‖ ≤ T`. -/
lemma norm_oscIntegral_le {θ T : ℝ} (hT : 0 ≤ T) : ‖oscIntegral θ T‖ ≤ T := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := T) (C := 1) (f := fun t : ℝ => Complex.exp ((θ * t : ℝ) * I))
    (fun x _ => by simp [Complex.norm_exp])
  simpa [oscIntegral, abs_of_nonneg hT] using h

/-- The oscillation bound `‖∫₀ᵀ e^{i θ t} dt‖ ≤ 2/|θ|`, uniform in `T`. -/
lemma norm_oscIntegral_le_two_div {θ : ℝ} (hθ : θ ≠ 0) (T : ℝ) :
    ‖oscIntegral θ T‖ ≤ 2 / |θ| := by
  rw [oscIntegral_eq hθ, norm_div]
  have h1 : ‖Complex.exp ((θ * T : ℝ) * I) - 1‖ ≤ 2 := by
    have h := norm_sub_le (Complex.exp ((θ * T : ℝ) * I)) 1
    simp only [Complex.norm_exp, norm_one] at h
    simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero] at h
    linarith
  have h2 : ‖(θ : ℂ) * I‖ = |θ| := by simp
  rw [h2]
  have hpos : 0 < |θ| := abs_pos.mpr hθ
  gcongr

/-- The average of a nonzero frequency tends to zero: `(1/T) ∫₀ᵀ e^{i θ t} dt → 0`. -/
lemma oscAvg_tendsto_zero {θ : ℝ} (hθ : θ ≠ 0) :
    Tendsto (fun T : ℝ => oscIntegral θ T / (T : ℂ)) atTop (𝓝 0) := by
  have hbound : Tendsto (fun T : ℝ => (2 / |θ|) / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  gcongr
  exact norm_oscIntegral_le_two_div hθ T

/-! ## Dirichlet series on a vertical line -/

/-- The value at `σ + i t` of the Dirichlet series with coefficients `A`, written with the
shifted index `n ↦ n + 1` so that the series is indexed by `ℕ`. -/
def dirichletLineSum (A : ℕ → ℂ) (σ t : ℝ) : ℂ :=
  ∑' n : ℕ, A n * (1 / ((n : ℂ) + 1) ^ (linePoint σ t))

/-- The modulus `‖aₙ‖ (n+1)^(-σ)` of the `n`-th term of the Dirichlet series on the line
of real part `σ`. -/
def dirichletWeight (A : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℝ := ‖A n‖ * ((n : ℝ) + 1) ^ (-σ)

/-- The coefficient `aₘ conj(aₙ) ((m+1)(n+1))^(-σ)` of the term `(m, n)` of the double
Dirichlet series of `|D(σ + i t)|²`. -/
def dirichletMsCoeff (A : ℕ → ℂ) (σ : ℝ) (p : ℕ × ℕ) : ℂ :=
  A p.1 * (starRingEnd ℂ) (A p.2) * (msCoeff σ p : ℂ)

lemma dirichletWeight_nonneg (A : ℕ → ℂ) (σ : ℝ) (n : ℕ) : 0 ≤ dirichletWeight A σ n := by
  unfold dirichletWeight
  positivity

lemma dirichletWeight_sq (A : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    dirichletWeight A σ n ^ 2 = ‖A n‖ ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h : (((n : ℝ) + 1) ^ (-σ)) ^ 2 = ((n : ℝ) + 1) ^ (-(2 * σ)) := by
    rw [sq, ← Real.rpow_add hn]
    ring_nf
  rw [dirichletWeight, mul_pow, h]

lemma one_div_cpow_linePoint {x : ℝ} (hx : 0 < x) (σ t : ℝ) :
    1 / (x : ℂ) ^ (linePoint σ t) =
      ((x ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-(t * Real.log x) : ℝ)) * I) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le,
    Real.rpow_neg hx.le, Real.rpow_def_of_pos hx, one_div, ← Complex.exp_neg,
    Complex.ofReal_inv, Complex.ofReal_exp, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  simp only [linePoint]
  push_cast
  ring

lemma norm_one_div_cpow_linePoint (σ t : ℝ) (n : ℕ) :
    ‖1 / ((n : ℂ) + 1) ^ (linePoint σ t)‖ = ((n : ℝ) + 1) ^ (-σ) := by
  rw [norm_div, norm_one, show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)),
    linePoint_re, Real.rpow_neg (by positivity)]
  push_cast
  rw [one_div]

lemma norm_dirichletTerm (A : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖A n * (1 / ((n : ℂ) + 1) ^ (linePoint σ t))‖ = dirichletWeight A σ n := by
  rw [norm_mul, norm_one_div_cpow_linePoint, dirichletWeight]

/-- The product of the `m`-th term of the Dirichlet series with the conjugate of its `n`-th
term is `aₘ conj(aₙ) ((m+1)(n+1))^(-σ) e^{i t log((n+1)/(m+1))}`. -/
lemma term_mul_conj (σ t : ℝ) (m n : ℕ) :
    (1 / ((m : ℂ) + 1) ^ (linePoint σ t)) *
        (starRingEnd ℂ) (1 / ((n : ℂ) + 1) ^ (linePoint σ t))
      = (msCoeff σ (m, n) : ℂ) * Complex.exp ((msFreq (m, n) * t : ℝ) * I) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have em : ((m : ℂ) + 1) = ((((m : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
  have en : ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [em, en, one_div_cpow_linePoint hm, one_div_cpow_linePoint hn, map_mul, ← Complex.exp_conj]
  simp only [Complex.conj_ofReal, map_mul, Complex.conj_I]
  rw [mul_mul_mul_comm, ← Complex.exp_add, ← Complex.ofReal_mul]
  congr 1
  · rw [msCoeff, Real.mul_rpow hm.le hn.le]
  · push_cast [msFreq]
    ring_nf

lemma dirichletTerm_mul_conj (A : ℕ → ℂ) (σ t : ℝ) (m n : ℕ) :
    (A m * (1 / ((m : ℂ) + 1) ^ (linePoint σ t))) *
        (starRingEnd ℂ) (A n * (1 / ((n : ℂ) + 1) ^ (linePoint σ t)))
      = dirichletMsCoeff A σ (m, n) * Complex.exp ((msFreq (m, n) * t : ℝ) * I) := by
  rw [map_mul, dirichletMsCoeff]
  calc (A m * (1 / ((m : ℂ) + 1) ^ (linePoint σ t))) *
        ((starRingEnd ℂ) (A n) * (starRingEnd ℂ) (1 / ((n : ℂ) + 1) ^ (linePoint σ t)))
      = (A m * (starRingEnd ℂ) (A n)) *
        ((1 / ((m : ℂ) + 1) ^ (linePoint σ t)) *
          (starRingEnd ℂ) (1 / ((n : ℂ) + 1) ^ (linePoint σ t))) := by ring
    _ = (A m * (starRingEnd ℂ) (A n)) *
        ((msCoeff σ (m, n) : ℂ) * Complex.exp ((msFreq (m, n) * t : ℝ) * I)) := by
        rw [term_mul_conj]
    _ = A m * (starRingEnd ℂ) (A n) * (msCoeff σ (m, n) : ℂ) *
        Complex.exp ((msFreq (m, n) * t : ℝ) * I) := by ring

lemma norm_dirichletMsCoeff (A : ℕ → ℂ) (σ : ℝ) (p : ℕ × ℕ) :
    ‖dirichletMsCoeff A σ p‖ = dirichletWeight A σ p.1 * dirichletWeight A σ p.2 := by
  rw [dirichletMsCoeff, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (msCoeff_nonneg σ p), msCoeff_eq_mul, dirichletWeight,
    dirichletWeight]
  ring

lemma summable_norm_dirichletMsCoeff {A : ℕ → ℂ} {σ : ℝ} (hA : Summable (dirichletWeight A σ)) :
    Summable (fun p : ℕ × ℕ => ‖dirichletMsCoeff A σ p‖) :=
  (hA.mul_of_nonneg hA (fun _ => dirichletWeight_nonneg A σ _)
    (fun _ => dirichletWeight_nonneg A σ _)).congr fun p => (norm_dirichletMsCoeff A σ p).symm

/-- The expansion of `|D(σ + i t)|²` as an absolutely convergent double Dirichlet series. -/
lemma normSq_dirichletLineSum_eq_tsum {A : ℕ → ℂ} {σ : ℝ}
    (hA : Summable (dirichletWeight A σ)) (t : ℝ) :
    ((‖dirichletLineSum A σ t‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : ℕ × ℕ, dirichletMsCoeff A σ p * Complex.exp ((msFreq p * t : ℝ) * I) := by
  have hsum1 : Summable (fun n : ℕ => ‖A n * (1 / ((n : ℂ) + 1) ^ (linePoint σ t))‖) :=
    hA.congr fun n => (norm_dirichletTerm A σ t n).symm
  have hsum2 : Summable
      (fun n : ℕ => ‖(starRingEnd ℂ) (A n * (1 / ((n : ℂ) + 1) ^ (linePoint σ t)))‖) := by
    simpa using hsum1
  have hnormSq : ((‖dirichletLineSum A σ t‖ ^ 2 : ℝ) : ℂ) =
      dirichletLineSum A σ t * (starRingEnd ℂ) (dirichletLineSum A σ t) := by
    rw [Complex.mul_conj]
    norm_cast
    exact (Complex.normSq_eq_norm_sq _).symm
  rw [hnormSq, dirichletLineSum, Complex.conj_tsum,
    tsum_mul_tsum_of_summable_norm hsum1 hsum2]
  exact tsum_congr fun p => dirichletTerm_mul_conj A σ t p.1 p.2

/-- Termwise integration of the double Dirichlet series of `|D(σ + i t)|²` over `[0, T]`. -/
lemma integral_normSq_dirichletLineSum {A : ℕ → ℂ} {σ : ℝ}
    (hA : Summable (dirichletWeight A σ)) {T : ℝ} (hT : 0 ≤ T) :
    ((∫ t in (0 : ℝ)..T, ‖dirichletLineSum A σ t‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : ℕ × ℕ, dirichletMsCoeff A σ p * oscIntegral (msFreq p) T := by
  set F : ℕ × ℕ → ℝ → ℂ :=
    fun p t => dirichletMsCoeff A σ p * Complex.exp ((msFreq p * t : ℝ) * I) with hF
  have hint : ∀ p : ℕ × ℕ, Integrable (F p) (volume.restrict (Set.Ioc 0 T)) := by
    intro p
    apply Continuous.integrableOn_Ioc
    fun_prop
  have hnormF : ∀ (p : ℕ × ℕ) (t : ℝ), ‖F p t‖ = ‖dirichletMsCoeff A σ p‖ := by
    intro p t
    rw [hF]
    simp only
    rw [norm_mul, Complex.norm_exp]
    simp
  have hintnorm : ∀ p : ℕ × ℕ,
      ∫ t in Set.Ioc (0 : ℝ) T, ‖F p t‖ = ‖dirichletMsCoeff A σ p‖ * T := by
    intro p
    simp_rw [hnormF p]
    simp [hT, mul_comm]
  have hsummable : Summable (fun p : ℕ × ℕ => ∫ t in Set.Ioc (0 : ℝ) T, ‖F p t‖) :=
    ((summable_norm_dirichletMsCoeff hA).mul_right T).congr fun p => (hintnorm p).symm
  have hterm : ∀ p : ℕ × ℕ,
      (∫ t in Set.Ioc (0 : ℝ) T, F p t) = dirichletMsCoeff A σ p * oscIntegral (msFreq p) T := by
    intro p
    rw [hF]
    simp only
    rw [integral_const_mul, oscIntegral, intervalIntegral.integral_of_le hT]
  rw [← intervalIntegral.integral_ofReal]
  have hcongr : ∀ t : ℝ, ((‖dirichletLineSum A σ t‖ ^ 2 : ℝ) : ℂ) = ∑' p : ℕ × ℕ, F p t :=
    fun t => normSq_dirichletLineSum_eq_tsum hA t
  simp_rw [hcongr]
  rw [intervalIntegral.integral_of_le hT,
    ← integral_tsum_of_summable_integral_norm hint hsummable]
  exact tsum_congr hterm

/-! ## The mean value theorem -/

/-- A double series supported on the diagonal sums to the sum of its diagonal. -/
lemma tsum_diagonal_eq {c : ℕ × ℕ → ℂ} (hc : Summable (fun p : ℕ × ℕ => ‖c p‖)) :
    (∑' p : ℕ × ℕ, (if p.1 = p.2 then c p else 0)) = ∑' n : ℕ, c (n, n) := by
  have hsummable : Summable (fun p : ℕ × ℕ => (if p.1 = p.2 then c p else 0)) := by
    refine Summable.of_norm (hc.of_nonneg_of_le (fun _ => norm_nonneg _) ?_)
    intro p
    by_cases h : p.1 = p.2 <;> simp [h]
  have hrow : ∀ m : ℕ, Summable (fun n : ℕ => (if m = n then c (m, n) else 0)) :=
    fun m => summable_of_ne_finset_zero (s := {m})
      (by intro n hn; simp only [Finset.mem_singleton] at hn; simp [Ne.symm hn])
  rw [hsummable.tsum_prod' hrow]
  refine tsum_congr fun m => ?_
  have hswap : (fun n : ℕ => (if m = n then c (m, n) else 0))
      = fun n : ℕ => (if n = m then c (m, n) else 0) := by
    funext n
    by_cases h : n = m
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hswap, tsum_ite_eq]

lemma dirichletMsCoeff_diag (A : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    dirichletMsCoeff A σ (n, n) = ((dirichletWeight A σ n ^ 2 : ℝ) : ℂ) := by
  have hconj : A n * (starRingEnd ℂ) (A n) = ((‖A n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  rw [dirichletMsCoeff, hconj, msCoeff_eq_mul, dirichletWeight]
  push_cast
  ring

/-- **The mean value theorem for an absolutely convergent Dirichlet series**: if
`∑ ‖aₙ‖ (n+1)^(-σ)` converges, then `(1/T) ∫₀ᵀ |D(σ + i t)|² dt → ∑ (‖aₙ‖ (n+1)^(-σ))²`. -/
theorem meanSquareAvg_tendsto_tsum_of_summable {A : ℕ → ℂ} {σ : ℝ}
    (hA : Summable (dirichletWeight A σ)) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖dirichletLineSum A σ t‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, dirichletWeight A σ n ^ 2)) := by
  set f : ℝ → ℕ × ℕ → ℂ :=
    fun T p => dirichletMsCoeff A σ p * (oscIntegral (msFreq p) T / (T : ℂ)) with hf
  set g : ℕ × ℕ → ℂ := fun p => (if p.1 = p.2 then dirichletMsCoeff A σ p else 0) with hg
  have hpoint : ∀ p : ℕ × ℕ, Tendsto (fun T : ℝ => f T p) atTop (𝓝 (g p)) := by
    intro p
    by_cases h : p.1 = p.2
    · have hfreq : msFreq p = 0 := (msFreq_eq_zero_iff p).mpr h
      have heventually :
          (fun _ : ℝ => dirichletMsCoeff A σ p) =ᶠ[atTop] fun T : ℝ => f T p := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
        have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
        rw [hf]
        simp only
        rw [hfreq, oscIntegral_zero_freq, div_self hT0, mul_one]
      refine Tendsto.congr' heventually ?_
      simp [hg, h]
    · have hfreq : msFreq p ≠ 0 := fun hc => h ((msFreq_eq_zero_iff p).mp hc)
      have := (oscAvg_tendsto_zero hfreq).const_mul (dirichletMsCoeff A σ p)
      simpa [hf, hg, h] using this
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ p : ℕ × ℕ, ‖f T p‖ ≤ ‖dirichletMsCoeff A σ p‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT p
    rw [hf]
    simp only
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    have h1 : ‖oscIntegral (msFreq p) T‖ / T ≤ 1 := by
      rw [div_le_one hT]
      exact norm_oscIntegral_le hT.le
    calc ‖dirichletMsCoeff A σ p‖ * (‖oscIntegral (msFreq p) T‖ / T)
        ≤ ‖dirichletMsCoeff A σ p‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖dirichletMsCoeff A σ p‖ := mul_one _
  have hlim : Tendsto (fun T : ℝ => ∑' p : ℕ × ℕ, f T p) atTop (𝓝 (∑' p : ℕ × ℕ, g p)) :=
    tendsto_tsum_of_dominated_convergence (summable_norm_dirichletMsCoeff hA) hpoint hbound
  have hdiag : (∑' p : ℕ × ℕ, g p) = ((∑' n : ℕ, dirichletWeight A σ n ^ 2 : ℝ) : ℂ) := by
    rw [hg, tsum_diagonal_eq (summable_norm_dirichletMsCoeff hA), Complex.ofReal_tsum]
    exact tsum_congr fun n => dirichletMsCoeff_diag A σ n
  rw [hdiag] at hlim
  have heq : (fun T : ℝ => ∑' p : ℕ × ℕ, f T p) =ᶠ[atTop]
      fun T : ℝ => (((∫ t in (0 : ℝ)..T, ‖dirichletLineSum A σ t‖ ^ 2) / T : ℝ) : ℂ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Complex.ofReal_div, integral_normSq_dirichletLineSum hA hT.le, hf]
    simp only
    rw [← tsum_div_const]
    exact (tsum_congr fun p => by rw [mul_div_assoc]).symm
  exact tendsto_ofReal_iff.mp (Tendsto.congr' heq hlim)

/-! ## The zeta function -/

lemma dirichletWeight_one (σ : ℝ) (n : ℕ) :
    dirichletWeight (fun _ => 1) σ n = ((n : ℝ) + 1) ^ (-σ) := by
  simp [dirichletWeight]

lemma summable_dirichletWeight_one {σ : ℝ} (hσ : 1 < σ) :
    Summable (dirichletWeight (fun _ => 1) σ) :=
  (summable_natAddOne_rpow hσ).congr fun n => (dirichletWeight_one σ n).symm

lemma dirichletLineSum_one {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    dirichletLineSum (fun _ => 1) σ t = riemannZeta (linePoint σ t) := by
  have hre : 1 < (linePoint σ t).re := by simpa using hσ
  rw [dirichletLineSum, zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  exact tsum_congr fun n => one_mul _

lemma dirichletMsCoeff_one (σ : ℝ) (p : ℕ × ℕ) :
    dirichletMsCoeff (fun _ => 1) σ p = (msCoeff σ p : ℂ) := by
  simp [dirichletMsCoeff]

/-- The expansion of `|ζ(σ + i t)|²` as an absolutely convergent double Dirichlet series,
valid for `σ > 1`. -/
lemma normSq_riemannZeta_line_eq_tsum {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ((‖riemannZeta (linePoint σ t)‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : ℕ × ℕ, (msCoeff σ p : ℂ) * Complex.exp ((msFreq p * t : ℝ) * I) := by
  have h := normSq_dirichletLineSum_eq_tsum (summable_dirichletWeight_one hσ) t
  rw [dirichletLineSum_one hσ t] at h
  simpa only [dirichletMsCoeff_one] using h

/-- Termwise integration of the double Dirichlet series of `|ζ(σ + i t)|²` over `[0, T]`. -/
lemma integral_normSq_riemannZeta_line {σ : ℝ} (hσ : 1 < σ) {T : ℝ} (hT : 0 ≤ T) :
    ((∫ t in (0 : ℝ)..T, ‖riemannZeta (linePoint σ t)‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : ℕ × ℕ, (msCoeff σ p : ℂ) * oscIntegral (msFreq p) T := by
  have h := integral_normSq_dirichletLineSum (summable_dirichletWeight_one hσ) hT
  simp_rw [dirichletLineSum_one hσ] at h
  simpa only [dirichletMsCoeff_one] using h

/-- **The mean value theorem for `ζ` on a line of absolute convergence**, in series form:
for `σ > 1`, `(1/T) ∫₀ᵀ |ζ(σ + i t)|² dt → ∑' n, (n+1)^(-2σ)`. -/
theorem meanSquareAvg_tendsto_tsum {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (linePoint σ t)‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)))) := by
  have h := meanSquareAvg_tendsto_tsum_of_summable (summable_dirichletWeight_one hσ)
  simp_rw [dirichletLineSum_one hσ] at h
  have hsq : ∀ n : ℕ,
      dirichletWeight (fun _ => 1) σ n ^ 2 = ((n : ℝ) + 1) ^ (-(2 * σ)) := by
    intro n
    rw [dirichletWeight_sq]
    simp
  simpa only [hsq] using h

/-- On the real axis to the right of `1`, `ζ` is the (real) sum of its Dirichlet series. -/
theorem riemannZeta_ofReal_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    riemannZeta ((σ : ℝ) : ℂ) = ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
  have hre : 1 < ((σ : ℝ) : ℂ).re := by simpa using hσ
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, ← Complex.ofReal_cpow hn.le, Complex.ofReal_cpow hn.le, ← Complex.ofReal_cpow hn.le]
  rw [Real.rpow_neg hn.le, Complex.ofReal_inv, one_div]

/-- **The mean value theorem for `ζ` on a line of absolute convergence**: for `σ > 1`,
`(1/T) ∫₀ᵀ |ζ(σ + i t)|² dt → ζ(2σ)`. -/
theorem meanSquareAvg_tendsto_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (linePoint σ t)‖ ^ 2) / T) atTop
      (𝓝 (riemannZeta ((2 * σ : ℝ) : ℂ)).re) := by
  have h2 : (1 : ℝ) < 2 * σ := by linarith
  have := meanSquareAvg_tendsto_tsum hσ
  rwa [show (riemannZeta ((2 * σ : ℝ) : ℂ)).re = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ)) by
    rw [riemannZeta_ofReal_eq_tsum h2, Complex.ofReal_re]]

/-! ## The reciprocal of `ζ`, through the Möbius series -/

/-- An `LSeries` is the Dirichlet line sum of its shifted coefficients. -/
theorem lseries_eq_dirichletLineSum (f : ℕ → ℂ) (σ t : ℝ)
    (h : LSeriesSummable f (linePoint σ t)) :
    LSeries f (linePoint σ t) = dirichletLineSum (fun n => f (n + 1)) σ t := by
  rw [LSeries, Summable.tsum_eq_zero_add h, dirichletLineSum]
  simp only [LSeries.term_def]
  norm_num
  exact tsum_congr fun n => by rw [div_eq_mul_inv]

/-- For `σ > 1` the Möbius Dirichlet series on the line of real part `σ` is `1/ζ`. -/
lemma dirichletLineSum_moebius {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    dirichletLineSum (fun n => ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)) σ t
      = (riemannZeta (linePoint σ t))⁻¹ := by
  have hre : 1 < (linePoint σ t).re := by simpa using hσ
  have hsummable : LSeriesSummable (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
      (linePoint σ t) := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hre
  have h1 : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (linePoint σ t) *
      riemannZeta (linePoint σ t) = 1 := by
    have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := linePoint σ t) hre
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hre] at h
    linear_combination h
  rw [← lseries_eq_dirichletLineSum _ _ _ hsummable]
  exact eq_inv_of_mul_eq_one_left h1

lemma summable_dirichletWeight_moebius {σ : ℝ} (hσ : 1 < σ) :
    Summable (dirichletWeight (fun n => ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)) σ) := by
  refine (summable_natAddOne_rpow hσ).of_nonneg_of_le
    (fun n => dirichletWeight_nonneg _ _ _) fun n => ?_
  have h1 : ‖((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)‖ ≤ 1 := by
    rw [show ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)
        = ((((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
  calc dirichletWeight (fun n => ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)) σ n
      = ‖((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)‖ * ((n : ℝ) + 1) ^ (-σ) := rfl
    _ ≤ 1 * ((n : ℝ) + 1) ^ (-σ) := by gcongr
    _ = ((n : ℝ) + 1) ^ (-σ) := one_mul _

/-- **The mean value theorem for `1/ζ`**: for `σ > 1`,
`(1/T) ∫₀ᵀ |1/ζ(σ + i t)|² dt → ∑ μ(n)² n^(-2σ)`. -/
theorem meanSquareAvg_tendsto_tsum_moebius {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖(riemannZeta (linePoint σ t))⁻¹‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) ^ 2 *
        ((n : ℝ) + 1) ^ (-(2 * σ)))) := by
  have h := meanSquareAvg_tendsto_tsum_of_summable (summable_dirichletWeight_moebius hσ)
  simp_rw [dirichletLineSum_moebius hσ] at h
  have hsq : ∀ n : ℕ,
      dirichletWeight (fun n => ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)) σ n ^ 2
        = ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ)) := by
    intro n
    rw [dirichletWeight_sq]
    congr 1
    rw [show ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)
        = ((((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [hsq] using h

end RiemannHypothesis
