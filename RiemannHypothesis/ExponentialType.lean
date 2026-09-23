/-
Copyright (c) 2026 Aristotle. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Functions of exponential type

The Beurling–Selberg extremal machinery — the majorants and minorants of the sign function and of
interval indicators that give the sharp constants in the large sieve, in Erdős–Turán, and in
Montgomery's explicit formula — is organised around the class of entire functions of exponential
type `τ`.  This module supplies the bottom layer of that theory: the growth predicate itself and
its closure API, which is what every later statement (Paley–Wiener, Beurling's `B`, the Selberg
majorants, the Vaaler functions) is phrased in terms of.

## Main definitions

* `RiemannHypothesis.HasExponentialTypeAtMost f τ` — for every `ε > 0` there is `C > 0` with
  `‖f z‖ ≤ C exp ((τ + ε) ‖z‖)` for all `z`.  This is the usual definition of "of exponential type
  at most `τ`" as a growth condition; entirety, where it is needed, is carried separately.

## Main results

The class is closed under the operations one needs to build extremal functions:

* `hasExponentialTypeAtMost_const`, `.add`, `.sub`, `.neg`, `.mul`, `.const_mul`, `.sum`,
  `.mono`;
* `hasExponentialTypeAtMost_pow`, `hasExponentialTypeAtMost_polynomial_aux` — polynomials have
  exponential type `0`;
* `hasExponentialTypeAtMost_exp_mul` — `z ↦ exp (a z)` has exponential type `‖a‖`;
* `hasExponentialTypeAtMost_sin`, `hasExponentialTypeAtMost_cos` — type `1`;
  `hasExponentialTypeAtMost_sin_mul`, `hasExponentialTypeAtMost_cos_mul` — `z ↦ sin (c z)` has type
  `|c|`, which is the normalisation the Beurling–Selberg constructions use (`sin (π z)` has type
  `π`);
* `HasExponentialTypeAtMost.comp_mul` — rescaling `z ↦ f (c z)` multiplies the type by `|c|`.
-/

namespace RiemannHypothesis

open Complex

/-- `f` has exponential type at most `τ`: for every `ε > 0` there is a constant `C > 0` with
`‖f z‖ ≤ C exp ((τ + ε) ‖z‖)` for all `z`. -/
def HasExponentialTypeAtMost (f : ℂ → ℂ) (τ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖)

namespace HasExponentialTypeAtMost

variable {f g : ℂ → ℂ} {τ σ : ℝ}

/-- The type may always be increased. -/
theorem mono (hf : HasExponentialTypeAtMost f τ) (hle : τ ≤ σ) :
    HasExponentialTypeAtMost f σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hf ε hε
  refine ⟨C, hC, fun z => le_trans (hbound z) ?_⟩
  have : (τ + ε) * ‖z‖ ≤ (σ + ε) * ‖z‖ := by
    apply mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) hC.le

/-- Sums. -/
theorem add (hf : HasExponentialTypeAtMost f τ) (hg : HasExponentialTypeAtMost g τ) :
    HasExponentialTypeAtMost (fun z => f z + g z) τ := by
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hf ε hε
  obtain ⟨C₂, hC₂, h₂⟩ := hg ε hε
  refine ⟨C₁ + C₂, by linarith, fun z => ?_⟩
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C₁ * Real.exp ((τ + ε) * ‖z‖) + C₂ * Real.exp ((τ + ε) * ‖z‖) :=
        add_le_add (h₁ z) (h₂ z)
    _ = (C₁ + C₂) * Real.exp ((τ + ε) * ‖z‖) := by ring

/-- Negation. -/
theorem neg (hf : HasExponentialTypeAtMost f τ) :
    HasExponentialTypeAtMost (fun z => -f z) τ := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := hf ε hε
  exact ⟨C, hC, fun z => by simpa using h z⟩

/-- Differences. -/
theorem sub (hf : HasExponentialTypeAtMost f τ) (hg : HasExponentialTypeAtMost g τ) :
    HasExponentialTypeAtMost (fun z => f z - g z) τ := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Products: the types add. -/
theorem mul (hf : HasExponentialTypeAtMost f τ) (hg : HasExponentialTypeAtMost g σ) :
    HasExponentialTypeAtMost (fun z => f z * g z) (τ + σ) := by
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hf (ε / 2) (by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := hg (ε / 2) (by linarith)
  refine ⟨C₁ * C₂, by positivity, fun z => ?_⟩
  calc ‖f z * g z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C₁ * Real.exp ((τ + ε / 2) * ‖z‖)) * (C₂ * Real.exp ((σ + ε / 2) * ‖z‖)) := by
        exact mul_le_mul (h₁ z) (h₂ z) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * Real.exp ((τ + ε / 2) * ‖z‖ + (σ + ε / 2) * ‖z‖) := by
        rw [Real.exp_add]; ring
    _ = C₁ * C₂ * Real.exp ((τ + σ + ε) * ‖z‖) := by ring_nf

/-- Scalar multiples. -/
theorem const_mul (hf : HasExponentialTypeAtMost f τ) (a : ℂ) :
    HasExponentialTypeAtMost (fun z => a * f z) τ := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := hf ε hε
  refine ⟨(‖a‖ + 1) * C, by positivity, fun z => ?_⟩
  calc ‖a * f z‖ = ‖a‖ * ‖f z‖ := norm_mul _ _
    _ ≤ (‖a‖ + 1) * (C * Real.exp ((τ + ε) * ‖z‖)) := by
        refine mul_le_mul (by linarith) (h z) (norm_nonneg _) (by positivity)
    _ = (‖a‖ + 1) * C * Real.exp ((τ + ε) * ‖z‖) := by ring

/-- Rescaling the variable multiplies the type by `|c|`. -/
theorem comp_mul (hf : HasExponentialTypeAtMost f τ) (hτ : 0 ≤ τ) (c : ℝ) :
    HasExponentialTypeAtMost (fun z => f ((c : ℂ) * z)) (|c| * τ) := by
  intro ε hε
  rcases eq_or_lt_of_le (abs_nonneg c) with hc | hc
  · -- `c = 0`: the function is constant
    have hc0 : c = 0 := abs_eq_zero.mp hc.symm
    obtain ⟨C, hC, h⟩ := hf ε hε
    refine ⟨C, hC, fun z => ?_⟩
    have hz : ((c : ℂ) * z) = 0 := by rw [hc0]; simp
    change ‖f ((c : ℂ) * z)‖ ≤ C * Real.exp ((|c| * τ + ε) * ‖z‖)
    rw [hz]
    have h0 := h 0
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one] at h0
    have hexp : (1 : ℝ) ≤ Real.exp ((|c| * τ + ε) * ‖z‖) := by
      refine Real.one_le_exp ?_
      have h1 : 0 ≤ |c| * τ + ε := by positivity
      positivity
    nlinarith [hC.le]
  · obtain ⟨C, hC, h⟩ := hf (ε / |c|) (by positivity)
    refine ⟨C, hC, fun z => ?_⟩
    have hnorm : ‖(c : ℂ) * z‖ = |c| * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := h ((c : ℂ) * z)
    rw [hnorm] at hb
    refine le_trans hb ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
    have hrw : (τ + ε / |c|) * (|c| * ‖z‖) = (|c| * τ + ε) * ‖z‖ := by
      field_simp
    exact le_of_eq hrw

/-- Finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ s, HasExponentialTypeAtMost (F i) τ) :
    HasExponentialTypeAtMost (fun z => ∑ i ∈ s, F i z) τ := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro ε hε
    refine ⟨1, one_pos, fun z => ?_⟩
    simp only [Finset.sum_empty, norm_zero]
    positivity
  | insert i s hi ih =>
    have hmem : ∀ j ∈ s, HasExponentialTypeAtMost (F j) τ :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hhead : HasExponentialTypeAtMost (F i) τ := hF i (Finset.mem_insert_self i s)
    have := hhead.add (ih hmem)
    simpa [Finset.sum_insert hi] using this

end HasExponentialTypeAtMost

/-- Constants have exponential type `0`. -/
theorem hasExponentialTypeAtMost_const (a : ℂ) :
    HasExponentialTypeAtMost (fun _ => a) 0 := by
  intro ε hε
  refine ⟨‖a‖ + 1, by positivity, fun z => ?_⟩
  have hexp : (1 : ℝ) ≤ Real.exp ((0 + ε) * ‖z‖) := by
    refine Real.one_le_exp ?_
    have : 0 ≤ ε := hε.le
    positivity
  nlinarith [norm_nonneg a]

/-- A single Taylor term bounds a power: `r ^ n ≤ n ! ε⁻ⁿ exp (ε r)` for `r ≥ 0`. -/
theorem pow_le_factorial_mul_exp {ε : ℝ} (hε : 0 < ε) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ n ≤ (Nat.factorial n : ℝ) / ε ^ n * Real.exp (ε * r) := by
  have hterm : (ε * r) ^ n / (Nat.factorial n : ℝ) ≤ Real.exp (ε * r) := by
    have hx : 0 ≤ ε * r := by positivity
    have := Real.sum_le_exp_of_nonneg hx (n + 1)
    have hsub : (ε * r) ^ n / (Nat.factorial n : ℝ)
        ≤ ∑ i ∈ Finset.range (n + 1), (ε * r) ^ i / (Nat.factorial i : ℝ) := by
      refine Finset.single_le_sum (f := fun i => (ε * r) ^ i / (Nat.factorial i : ℝ))
        (fun i _ => ?_) (Finset.self_mem_range_succ n)
      positivity
    linarith
  have hεn : (0 : ℝ) < ε ^ n := by positivity
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hfac] at hterm
  have hexp : ε ^ n * r ^ n ≤ Real.exp (ε * r) * (Nat.factorial n : ℝ) := by
    calc ε ^ n * r ^ n = (ε * r) ^ n := by rw [mul_pow]
      _ ≤ Real.exp (ε * r) * (Nat.factorial n : ℝ) := hterm
  rw [div_mul_eq_mul_div, le_div_iff₀ hεn]
  nlinarith [hexp]

/-- Powers of `z` have exponential type `0`. -/
theorem hasExponentialTypeAtMost_pow (n : ℕ) :
    HasExponentialTypeAtMost (fun z => z ^ n) 0 := by
  intro ε hε
  refine ⟨(Nat.factorial n : ℝ) / ε ^ n, by positivity, fun z => ?_⟩
  have h := pow_le_factorial_mul_exp hε n (norm_nonneg z)
  simpa [norm_pow, zero_add, mul_comm] using h

/-- Monomials, hence (with `HasExponentialTypeAtMost.sum` and `.const_mul`) polynomials, have
exponential type `0`. -/
theorem hasExponentialTypeAtMost_polynomial_aux {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (d : ι → ℕ) : HasExponentialTypeAtMost (fun z => ∑ i ∈ s, a i * z ^ d i) 0 :=
  HasExponentialTypeAtMost.sum s fun i _ =>
    (hasExponentialTypeAtMost_pow (d i)).const_mul (a i)

/-- `z ↦ exp (a z)` has exponential type `‖a‖`. -/
theorem hasExponentialTypeAtMost_exp_mul (a : ℂ) :
    HasExponentialTypeAtMost (fun z => Complex.exp (a * z)) ‖a‖ := by
  intro ε hε
  refine ⟨1, one_pos, fun z => ?_⟩
  rw [one_mul, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  calc (a * z).re ≤ ‖a * z‖ := Complex.re_le_norm _
    _ = ‖a‖ * ‖z‖ := norm_mul _ _
    _ ≤ (‖a‖ + ε) * ‖z‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)

/-- `sin` has exponential type `1`. -/
theorem hasExponentialTypeAtMost_sin : HasExponentialTypeAtMost Complex.sin 1 := by
  have h1 : HasExponentialTypeAtMost (fun z => Complex.exp (-Complex.I * z)) 1 := by
    simpa using hasExponentialTypeAtMost_exp_mul (-Complex.I)
  have h2 : HasExponentialTypeAtMost (fun z => Complex.exp (Complex.I * z)) 1 := by
    simpa using hasExponentialTypeAtMost_exp_mul Complex.I
  have hdiff := (h1.sub h2).const_mul (Complex.I / 2)
  have hEq : (fun z => Complex.I / 2 *
      (Complex.exp (-Complex.I * z) - Complex.exp (Complex.I * z))) = Complex.sin := by
    funext z
    rw [Complex.sin]
    ring_nf
  rwa [hEq] at hdiff

/-- `cos` has exponential type `1`. -/
theorem hasExponentialTypeAtMost_cos : HasExponentialTypeAtMost Complex.cos 1 := by
  have h1 : HasExponentialTypeAtMost (fun z => Complex.exp (Complex.I * z)) 1 := by
    simpa using hasExponentialTypeAtMost_exp_mul Complex.I
  have h2 : HasExponentialTypeAtMost (fun z => Complex.exp (-Complex.I * z)) 1 := by
    simpa using hasExponentialTypeAtMost_exp_mul (-Complex.I)
  have hsum := (h1.add h2).const_mul (1 / 2)
  have hEq : (fun z => (1 : ℂ) / 2 *
      (Complex.exp (Complex.I * z) + Complex.exp (-Complex.I * z))) = Complex.cos := by
    funext z
    rw [Complex.cos]
    ring_nf
  rwa [hEq] at hsum

/-- `z ↦ sin (c z)` has exponential type `|c|`; with `c = π` this is the normalisation of the
Beurling–Selberg constructions. -/
theorem hasExponentialTypeAtMost_sin_mul (c : ℝ) :
    HasExponentialTypeAtMost (fun z => Complex.sin ((c : ℂ) * z)) |c| := by
  have h := hasExponentialTypeAtMost_sin.comp_mul zero_le_one c
  simpa using h

/-- `z ↦ cos (c z)` has exponential type `|c|`. -/
theorem hasExponentialTypeAtMost_cos_mul (c : ℝ) :
    HasExponentialTypeAtMost (fun z => Complex.cos ((c : ℂ) * z)) |c| := by
  have h := hasExponentialTypeAtMost_cos.comp_mul zero_le_one c
  simpa using h

end RiemannHypothesis
