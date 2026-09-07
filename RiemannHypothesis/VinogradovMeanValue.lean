/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.Enumerative.Bell

/-!
# The Vinogradov system and its solution count

Vinogradov's mean value theorem bounds the number `J_{s,k}(X)` of solutions of the system

`x₁^j + ⋯ + x_s^j = y₁^j + ⋯ + y_s^j`  for `j = 1, …, k`,  `1 ≤ xᵢ, yᵢ ≤ X`.

It is the engine behind the Vinogradov–Korobov zero-free region.  This file fixes the
combinatorial object and proves the elementary facts about it that any route to the theorem —
in particular Wooley's efficient congruencing, which is a purely counting argument — takes as
its starting point.

## Main results

* `RiemannHypothesis.Vinogradov.vinBox`, `vinogradovCount` — the box `[1, X]^s` and the solution
  count `J_{s,k}(X)`.
* `RiemannHypothesis.Vinogradov.vinogradovEq_translate` — **translation invariance**: the system
  is unchanged by a common shift `xᵢ ↦ xᵢ + a`, `yᵢ ↦ yᵢ + a`.  This is the invariance that
  efficient congruencing exploits; it is what distinguishes the Vinogradov system from an
  arbitrary system of equations.
* `RiemannHypothesis.Vinogradov.vinogradovEq_dilate` — dilation invariance, `xᵢ ↦ c xᵢ`.
* `RiemannHypothesis.Vinogradov.pow_card_le_vinogradovCount` — the diagonal lower bound
  `X^s ≤ J_{s,k}(X)`.
* `RiemannHypothesis.Vinogradov.vinogradovCount_le_pow` — the trivial upper bound
  `J_{s,k}(X) ≤ X^{2s}`.
* `RiemannHypothesis.Vinogradov.vinogradovCount_one_one` — `J_{1,1}(X) = X`, a non-vacuity check.
* `RiemannHypothesis.Vinogradov.VinogradovMeanValueBound` — the **statement** of the theorem
  (Wooley; Bourgain–Demeter–Guth), recorded as a `Prop` and *not* proved here.

## Scope

Only the elementary facts are proved.  The mean value theorem itself is not; nor is any
consequence for exponential sums or for the zero-free region.  The lower bound
`X^{2s − k(k+1)/2} ≪ J_{s,k}(X)`, which shows the second term of the conjectured bound is also
necessary, needs a major-arc argument and is not proved here either.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace Vinogradov

/-- The box of `s`-tuples of integers in `[1, X]`. -/
def vinBox (s X : ℕ) : Finset (Fin s → ℕ) := Fintype.piFinset (fun _ => Finset.Icc 1 X)

theorem card_vinBox (s X : ℕ) : (vinBox s X).card = X ^ s := by
  rw [vinBox, Fintype.card_piFinset]
  simp [Nat.card_Icc]

/-- Two tuples solve the Vinogradov system of degree `k` when their power sums agree up to
degree `k`. -/
def VinogradovEq (k : ℕ) {s : ℕ} (x y : Fin s → ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 k, ∑ i, x i ^ j = ∑ i, y i ^ j

instance (k : ℕ) {s : ℕ} (x y : Fin s → ℕ) : Decidable (VinogradovEq k x y) := by
  unfold VinogradovEq; infer_instance

/-- `J_{s,k}(X)`: the number of solutions of the Vinogradov system of degree `k` in `s` pairs of
variables from `[1, X]`. -/
def vinogradovCount (k s X : ℕ) : ℕ :=
  (((vinBox s X) ×ˢ (vinBox s X)).filter (fun p => VinogradovEq k p.1 p.2)).card

/-! ## The invariances of the system -/

/-- The power sums of a shifted tuple, by the binomial theorem. -/
theorem sum_add_pow_eq {s : ℕ} (x : Fin s → ℕ) (a j : ℕ) :
    ∑ i, (x i + a) ^ j = ∑ m ∈ Finset.range (j + 1), (j.choose m * a ^ (j - m)) * ∑ i, x i ^ m := by
  have hbin : ∀ i, (x i + a) ^ j
      = ∑ m ∈ Finset.range (j + 1), x i ^ m * a ^ (j - m) * j.choose m := by
    intro i
    exact add_pow (x i) a j
  rw [Finset.sum_congr rfl fun i _ => hbin i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Translation invariance of the Vinogradov system.**  If `x` and `y` solve the system, so do
`x + a` and `y + a` for every shift `a`.  This is the structural feature that efficient
congruencing uses. -/
theorem vinogradovEq_translate {k s : ℕ} {x y : Fin s → ℕ} (h : VinogradovEq k x y) (a : ℕ) :
    VinogradovEq k (fun i => x i + a) (fun i => y i + a) := by
  intro j hj
  have hj' : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hsum : ∀ m ≤ j, ∑ i, x i ^ m = ∑ i, y i ^ m := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · exact h m (Finset.mem_Icc.mpr ⟨hm0, le_trans hm hj'⟩)
  simp only []
  rw [sum_add_pow_eq x a j, sum_add_pow_eq y a j]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hsum m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]

/-- **Dilation invariance of the Vinogradov system.** -/
theorem vinogradovEq_dilate {k s : ℕ} {x y : Fin s → ℕ} (h : VinogradovEq k x y) (c : ℕ) :
    VinogradovEq k (fun i => c * x i) (fun i => c * y i) := by
  intro j hj
  simp only [mul_pow, ← Finset.mul_sum]
  rw [h j hj]

/-! ## The elementary bounds -/

/-- **The diagonal lower bound** `X^s ≤ J_{s,k}(X)`: every tuple gives the solution `(x, x)`. -/
theorem pow_card_le_vinogradovCount (k s X : ℕ) : X ^ s ≤ vinogradovCount k s X := by
  classical
  have hsub : (vinBox s X).image (fun x => (x, x))
      ⊆ ((vinBox s X) ×ˢ (vinBox s X)).filter (fun p => VinogradovEq k p.1 p.2) := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, fun j _ => rfl⟩
  have hinj : Function.Injective (fun x : Fin s → ℕ => (x, x)) := fun a b hab => by
    simpa using congrArg Prod.fst hab
  calc X ^ s = ((vinBox s X).image (fun x => (x, x))).card := by
        rw [Finset.card_image_of_injective _ hinj, card_vinBox]
    _ ≤ _ := Finset.card_le_card hsub

/-- **The trivial upper bound** `J_{s,k}(X) ≤ X^{2s}`. -/
theorem vinogradovCount_le_pow (k s X : ℕ) : vinogradovCount k s X ≤ X ^ (2 * s) := by
  classical
  calc vinogradovCount k s X ≤ ((vinBox s X) ×ˢ (vinBox s X)).card :=
        Finset.card_filter_le _ _
    _ = X ^ s * X ^ s := by rw [Finset.card_product, card_vinBox]
    _ = X ^ (2 * s) := by rw [← pow_add]; ring_nf

/-- A non-vacuity check: with one variable and one equation the only solutions are the diagonal
ones, so `J_{1,1}(X) = X`. -/
theorem vinogradovCount_one_one (X : ℕ) : vinogradovCount 1 1 X = X := by
  classical
  have hfilter : ((vinBox 1 X) ×ˢ (vinBox 1 X)).filter (fun p => VinogradovEq 1 p.1 p.2)
      = (vinBox 1 X).image (fun x => (x, x)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
      have h := heq 1 (by simp)
      simp only [pow_one, Fin.sum_univ_one] at h
      have hfun : p.1 = p.2 := by
        funext i
        fin_cases i
        exact h
      refine Finset.mem_image.mpr ⟨p.1, h1, ?_⟩
      have hpair : (p.1, p.1) = (p.1, p.2) := by rw [hfun]
      simpa using hpair
    · intro hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, fun j _ => rfl⟩
  have hinj : Function.Injective (fun x : Fin 1 → ℕ => (x, x)) := fun a b hab => by
    simpa using congrArg Prod.fst hab
  rw [vinogradovCount, hfilter, Finset.card_image_of_injective _ hinj, card_vinBox, pow_one]

/-! ## The theorem itself, as a statement -/

/-- **Vinogradov's mean value theorem** (Wooley 2016 for `k = 3` and by efficient congruencing in
general; Bourgain–Demeter–Guth 2016 by decoupling), recorded as a statement and *not* proved
here: for every `ε > 0`,

`J_{s,k}(X) ≪ X^{s+ε} + X^{2s − k(k+1)/2 + ε}`.

Both terms are needed: the first is the diagonal contribution, bounded below in
`pow_card_le_vinogradovCount`. -/
def VinogradovMeanValueBound : Prop :=
  ∀ k s : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
    (vinogradovCount k s X : ℝ)
      ≤ C * ((X : ℝ) ^ ((s : ℝ) + ε)
        + (X : ℝ) ^ ((2 * s : ℝ) - (k * (k + 1) : ℝ) / 2 + ε))

end Vinogradov

end RiemannHypothesis
