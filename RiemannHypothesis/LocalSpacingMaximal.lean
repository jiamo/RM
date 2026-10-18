/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib

/-!
# A maximal inequality for points with local spacings

Let `λ_1, …, λ_n` be real numbers and `δ_r > 0` with `|λ_r - λ_s| ≥ δ_r` for `s ≠ r`.  Then the
intervals of length `δ_r` centred at the `λ_r` are pairwise disjoint.  This file proves the
estimates for such configurations that the weighted Montgomery–Vaughan inequality
(`RiemannHypothesis/MontgomeryVaughanWeighted.lean`) needs:

* `sum_delta_ball_le` — `∑_{t ≠ s, |λ_s - λ_t| ≤ R} δ_t ≤ 3 R` (disjoint intervals);
* `sum_div_sq_le_of_ballSum_le` — summation by parts: if every ball `|λ_s - λ_t| ≤ R` carries
  mass at most `A R`, then `∑_{t ≠ s} m_t / (λ_s - λ_t)² ≤ 2 A / δ_s`;
* `sum_delta_le_of_ballSum_gt` — the Vitali covering argument: the weak-type bound
  `∑_{s ∈ E} δ_s ≤ (5 / τ) ∑_t m_t` when each ball of radius `R_s ≥ δ_s` about `s ∈ E` carries
  mass more than `τ R_s`;
* `sum_delta_mul_maxAvg_sq_le` — the strong `L²` maximal inequality
  `∑_s δ_s M_s² ≤ 120 ∑_t a_t²` for the maximal averages `M_s` of the masses `a_t √δ_t`, by the
  layer-cake formula;
* `sum_sum_mul_div_sq_le` — the consequence used for the weighted inequality:
  `∑_{s ≠ t} a_s a_t δ_s^{3/2} δ_t^{1/2} / (λ_s - λ_t)² ≤ 2 √120 ∑ a_t²` for `a ≥ 0`;
* `delta_mul_sum_delta_div_sq_le` — `δ_s ∑_{t ≠ s} δ_t / (λ_s - λ_t)² ≤ 6`.

The positive kernel `δ_s^{3/2} δ_t^{1/2} / (λ_s - λ_t)²` is not bounded by Schur's test with any
power weight `δ^β` (an isolated point next to a dense cluster and a geometric progression need
incompatible exponents), which is why a maximal-function argument is used.
-/

open Finset MeasureTheory

namespace RiemannHypothesis

namespace LocalSpacing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mass `∑ m_t` over the points `t ≠ s` with `|λ_s - λ_t| ≤ R`. -/
noncomputable def ballSum (lam m : ι → ℝ) (s : ι) (R : ℝ) : ℝ :=
  ∑ t ∈ (univ.erase s).filter (fun t => |lam s - lam t| ≤ R), m t

/-- The maximal average `sup_{t ≠ s} ballSum(|λ_s - λ_t|) / |λ_s - λ_t|` (`0` if no `t ≠ s`). -/
noncomputable def maxAvg (lam m : ι → ℝ) (s : ι) : ℝ :=
  ⨆ t : {t : ι // t ≠ s}, ballSum lam m s |lam s - lam t| / |lam s - lam t|

/-- Disjoint intervals in a bounded interval: if the intervals `(c_i - ρ_i, c_i + ρ_i)`,
`i ∈ S`, are pairwise disjoint and lie in `[α, β]`, then `∑ 2 ρ_i ≤ β - α`. -/
lemma sum_two_mul_le_of_disjoint {ι : Type*} (S : Finset ι) (c ρ : ι → ℝ) (α β : ℝ)
    (hρ : ∀ i ∈ S, 0 ≤ ρ i)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ρ i + ρ j ≤ |c i - c j|)
    (hsub : ∀ i ∈ S, α ≤ c i - ρ i ∧ c i + ρ i ≤ β) (hαβ : α ≤ β) :
    ∑ i ∈ S, 2 * ρ i ≤ β - α := by
  have hpd : (S : Set ι).PairwiseDisjoint (fun i => Set.Ioo (c i - ρ i) (c i + ρ i)) := by
    intro i hi j hj hij
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have h := hdisj i hi j hj hij
    have h1 : |c i - c j| ≤ |x - c i| + |x - c j| := by
      rw [abs_sub_comm x (c i)]; exact abs_sub_le _ _ _
    have h2 : |x - c i| < ρ i := abs_sub_lt_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h3 : |x - c j| < ρ j := abs_sub_lt_iff.mpr ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
    linarith
  have hU := measure_biUnion_finset (μ := volume) hpd (fun i _ => measurableSet_Ioo)
  have hle : volume (⋃ i ∈ S, Set.Ioo (c i - ρ i) (c i + ρ i)) ≤ volume (Set.Icc α β) := by
    refine measure_mono (Set.iUnion₂_subset fun i hi => ?_)
    exact Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc (hsub i hi).1 (hsub i hi).2)
  rw [hU, Real.volume_Icc] at hle
  simp only [Real.volume_Ioo] at hle
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => by linarith [hρ i hi])] at hle
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at hle
  refine le_trans (le_of_eq ?_) hle
  refine Finset.sum_congr rfl fun i _ => by ring

section Spacing

variable {lam δ : ι → ℝ}
omit [Fintype ι] [DecidableEq ι] in
lemma sep_symm (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) {r s : ι}
    (h : r ≠ s) : δ s ≤ |lam r - lam s| := by
  rw [abs_sub_comm]; exact hsep s r h.symm

/-- The points `t ≠ s` within distance `R` of `λ_s` have total spacing at most `3 R`. -/
lemma sum_delta_ball_le (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) (s : ι) {R : ℝ} (hR : 0 ≤ R) :
    ballSum lam δ s R ≤ 3 * R := by
  unfold ballSum
  set F := (univ.erase s).filter (fun t => |lam s - lam t| ≤ R)
  have hF : ∀ t ∈ F, t ≠ s ∧ |lam s - lam t| ≤ R := fun t ht => by
    rw [Finset.mem_filter, Finset.mem_erase] at ht; exact ⟨ht.1.1, ht.2⟩
  have h := sum_two_mul_le_of_disjoint F lam (fun t => δ t / 2) (lam s - 3 * R / 2)
    (lam s + 3 * R / 2) (fun t _ => by linarith [hδ t])
    (fun i hi j hj hij => by
      have h1 := hsep i j hij
      have h2 := sep_symm hsep hij
      linarith)
    (fun t ht => by
      obtain ⟨hts, hd⟩ := hF t ht
      have h1 : δ t ≤ |lam s - lam t| := by rw [abs_sub_comm]; exact hsep t s hts
      rw [abs_le] at hd
      have h2 : δ t ≤ R := le_trans h1 (abs_le.mpr hd)
      constructor <;> linarith [hd.1, hd.2])
    (by linarith)
  calc ∑ t ∈ F, δ t = ∑ t ∈ F, 2 * (δ t / 2) := Finset.sum_congr rfl fun t _ => by ring
    _ ≤ _ := h
    _ = 3 * R := by ring

lemma maxAvg_nonneg {m : ι → ℝ} (hm : ∀ t, 0 ≤ m t) (s : ι) :
    0 ≤ maxAvg lam m s :=
  Real.iSup_nonneg fun _ => div_nonneg (Finset.sum_nonneg fun u _ => hm u) (abs_nonneg _)

/-- Every ball of radius `R` carries mass at most `maxAvg · R`. -/
lemma ballSum_le_maxAvg_mul (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) {m : ι → ℝ}
    (hm : ∀ t, 0 ≤ m t) (s : ι) {R : ℝ}
    (hR : 0 ≤ R) : ballSum lam m s R ≤ maxAvg lam m s * R := by
  set F := (univ.erase s).filter (fun t => |lam s - lam t| ≤ R) with hFdef
  rcases F.eq_empty_or_nonempty with hF | hF
  · rw [ballSum, ← hFdef, hF, Finset.sum_empty]
    exact mul_nonneg (maxAvg_nonneg hm s) hR
  obtain ⟨t₀, ht₀, hmax⟩ := F.exists_max_image (fun t => |lam s - lam t|) hF
  rw [hFdef, Finset.mem_filter, Finset.mem_erase] at ht₀
  have hpos : 0 < |lam s - lam t₀| := lt_of_lt_of_le (hδ s) (hsep s t₀ ht₀.1.1.symm)
  have heq : ballSum lam m s R = ballSum lam m s |lam s - lam t₀| := by
    unfold ballSum
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hmax t (by
        rw [hFdef, Finset.mem_filter, Finset.mem_erase]; exact ⟨⟨h1, Finset.mem_univ _⟩, h2⟩)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.trans ht₀.2⟩
  have hle : ballSum lam m s |lam s - lam t₀| / |lam s - lam t₀| ≤ maxAvg lam m s :=
    le_ciSup (f := fun t : {t : ι // t ≠ s} =>
      ballSum lam m s |lam s - lam t| / |lam s - lam t|) (Set.finite_range _).bddAbove
      ⟨t₀, ht₀.1.1⟩
  rw [div_le_iff₀ hpos] at hle
  rw [heq]
  exact hle.trans (mul_le_mul_of_nonneg_left ht₀.2 (maxAvg_nonneg hm s))

lemma exists_lt_ballSum_of_lt_maxAvg (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) {m : ι → ℝ} (s : ι) {τ : ℝ}
    (h : τ < maxAvg lam m s) (hτ : 0 ≤ τ) :
    ∃ t, t ≠ s ∧ τ * |lam s - lam t| < ballSum lam m s |lam s - lam t| := by
  unfold maxAvg at h
  cases isEmpty_or_nonempty {t : ι // t ≠ s} with
  | inl he => rw [Real.iSup_of_isEmpty] at h; linarith
  | inr hne =>
    obtain ⟨⟨t, ht⟩, hlt⟩ := exists_lt_of_lt_ciSup h
    have hpos : 0 < |lam s - lam t| := lt_of_lt_of_le (hδ s) (hsep s t ht.symm)
    exact ⟨t, ht, by rwa [lt_div_iff₀ hpos] at hlt⟩

/-- **The Vitali covering argument** (weak type): if each ball of radius `R_s ≥ δ_s` about
`λ_s`, `s ∈ E`, carries mass more than `τ R_s`, then `∑_{s ∈ E} δ_s ≤ (5 / τ) ∑_t m_t`. -/
theorem sum_delta_le_of_ballSum_gt (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) {τ : ℝ} (hτ : 0 < τ)
    (R : ι → ℝ) (E : Finset (ι)) (m : ι → ℝ) (hm : ∀ t, 0 ≤ m t)
    (hE : ∀ s ∈ E, δ s ≤ R s ∧ τ * R s < ballSum lam m s (R s)) :
    ∑ s ∈ E, δ s ≤ 5 / τ * ∑ t, m t := by
  induction E using Finset.strongInduction generalizing m with
  | H E ih =>
  rcases E.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => hm t)
  obtain ⟨s₀, hs₀, hmax⟩ := E.exists_max_image R hne
  have hR₀ : 0 < R s₀ := lt_of_lt_of_le (hδ s₀) (hE s₀ hs₀).1
  set E' := E.filter (fun s => R s + R s₀ < |lam s - lam s₀|) with hE'
  set m' : ι → ℝ := fun t => if |lam t - lam s₀| ≤ R s₀ then 0 else m t with hm'
  have hm'nn : ∀ t, 0 ≤ m' t := fun t => by
    simp only [hm']; split_ifs; exacts [le_rfl, hm t]
  have hsub : E' ⊂ E := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have : s₀ ∈ E' := h ▸ hs₀
    rw [hE', Finset.mem_filter, sub_self, abs_zero] at this
    linarith [this.2]
  have hball : ∀ s ∈ E', ballSum lam m' s (R s) = ballSum lam m s (R s) := by
    intro s hs
    rw [hE', Finset.mem_filter] at hs
    unfold ballSum
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_filter] at ht
    have h1 : |lam s - lam s₀| ≤ |lam s - lam t| + |lam t - lam s₀| := abs_sub_le _ _ _
    have h2 : ¬ |lam t - lam s₀| ≤ R s₀ := by
      intro h3; linarith [hs.2, ht.2]
    simp only [hm', h2, if_false]
  have hIH := ih E' hsub m' hm'nn fun s hs => by
    rw [hball s hs]; exact hE s (Finset.filter_subset _ _ hs)
  -- the points of `E` near `s₀`
  have hnear : ∑ s ∈ E.filter (fun s => ¬ (R s + R s₀ < |lam s - lam s₀|)), δ s ≤ 5 * R s₀ := by
    set F := E.filter (fun s => ¬ (R s + R s₀ < |lam s - lam s₀|))
    have h := sum_two_mul_le_of_disjoint F lam (fun t => δ t / 2) (lam s₀ - 5 * R s₀ / 2)
      (lam s₀ + 5 * R s₀ / 2) (fun t _ => by linarith [hδ t])
      (fun i _ j _ hij => by
        have h1 := hsep i j hij
        have h2 := sep_symm hsep hij
        linarith)
      (fun t ht => by
        rw [Finset.mem_filter, not_lt] at ht
        have h1 := (hE t ht.1).1
        have h2 := hmax t ht.1
        have h3 := abs_le.mp ht.2
        constructor <;> linarith [h3.1, h3.2])
      (by linarith)
    calc ∑ t ∈ F, δ t = ∑ t ∈ F, 2 * (δ t / 2) := Finset.sum_congr rfl fun t _ => by ring
      _ ≤ _ := h
      _ = 5 * R s₀ := by ring
  have hmass : ballSum lam m s₀ (R s₀) ≤ ∑ t, (m t - m' t) := by
    unfold ballSum
    have hdiff : ∀ t, m t - m' t = if |lam t - lam s₀| ≤ R s₀ then m t else 0 := fun t => by
      simp only [hm']; split_ifs <;> ring
    simp_rw [hdiff]
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t _ _ => hm t)
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_univ _, by rw [abs_sub_comm]; exact ht.2⟩
  have hs₀b := (hE s₀ hs₀).2
  rw [← Finset.sum_filter_add_sum_filter_not E (fun s => R s + R s₀ < |lam s - lam s₀|)]
  have h5 : 5 * R s₀ ≤ 5 / τ * ∑ t, (m t - m' t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hτ]; nlinarith
  calc ∑ s ∈ E', δ s + ∑ s ∈ E.filter (fun s => ¬ (R s + R s₀ < |lam s - lam s₀|)), δ s
      ≤ 5 / τ * ∑ t, m' t + 5 / τ * ∑ t, (m t - m' t) := add_le_add hIH (hnear.trans h5)
    _ = 5 / τ * ∑ t, m t := by rw [← mul_add, ← Finset.sum_add_distrib]; congr 1; simp

/-- The weak-type bound for the maximal averages of the masses `a_t √δ_t`, with the large
values of `a_t / √δ_t` separated off. -/
theorem sum_delta_maxAvg_gt_le (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) {a : ι → ℝ}
    (ha : ∀ t, 0 ≤ a t) {τ : ℝ} (hτ : 0 < τ) :
    ∑ s ∈ univ.filter (fun s => τ < maxAvg lam (fun t => a t * Real.sqrt (δ t)) s), δ s
      ≤ 10 / τ * ∑ t ∈ univ.filter (fun t => τ < 6 * a t / Real.sqrt (δ t)),
          a t * Real.sqrt (δ t) := by
  set m : ι → ℝ := fun t => a t * Real.sqrt (δ t) with hmdef
  set mb : ι → ℝ := fun t => if τ < 6 * a t / Real.sqrt (δ t) then m t else 0 with hmb
  have hmnn : ∀ t, 0 ≤ m t := fun t => mul_nonneg (ha t) (Real.sqrt_nonneg _)
  have hmbnn : ∀ t, 0 ≤ mb t := fun t => by
    simp only [hmb]; split_ifs; exacts [hmnn t, le_rfl]
  -- the small masses are at most `(τ / 6) δ_t`
  have hsmall : ∀ t, m t - mb t ≤ τ / 6 * δ t := fun t => by
    simp only [hmb]
    split_ifs with h
    · rw [sub_self]; exact mul_nonneg (by positivity) (hδ t).le
    · rw [sub_zero]
      have hs : 0 < Real.sqrt (δ t) := Real.sqrt_pos.mpr (hδ t)
      rw [not_lt, div_le_iff₀ hs] at h
      have hsq : Real.sqrt (δ t) * Real.sqrt (δ t) = δ t := Real.mul_self_sqrt (hδ t).le
      simp only [hmdef]
      nlinarith
  set E := univ.filter (fun s => τ < maxAvg lam m s)
  have hex : ∀ s ∈ E, ∃ t, t ≠ s ∧ τ * |lam s - lam t| < ballSum lam m s |lam s - lam t| :=
    fun s hs => exists_lt_ballSum_of_lt_maxAvg hδ hsep s (Finset.mem_filter.mp hs).2 hτ.le
  choose! T hT using hex
  set R : ι → ℝ := fun s => |lam s - lam (T s)|
  have hE : ∀ s ∈ E, δ s ≤ R s ∧ τ / 2 * R s < ballSum lam mb s (R s) := by
    intro s hs
    obtain ⟨hts, hlt⟩ := hT s hs
    refine ⟨hsep s (T s) hts.symm, ?_⟩
    have hR : 0 ≤ R s := abs_nonneg _
    have hsplit : ballSum lam m s (R s)
        = ballSum lam mb s (R s) + ballSum lam (fun t => m t - mb t) s (R s) := by
      unfold ballSum; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun t _ => by ring
    have hsm : ballSum lam (fun t => m t - mb t) s (R s) ≤ τ / 6 * (3 * R s) := by
      calc ballSum lam (fun t => m t - mb t) s (R s) ≤ ballSum lam (fun t => τ / 6 * δ t) s (R s) :=
            Finset.sum_le_sum fun t _ => hsmall t
        _ = τ / 6 * ballSum lam δ s (R s) := by unfold ballSum; rw [Finset.mul_sum]
        _ ≤ τ / 6 * (3 * R s) :=
            mul_le_mul_of_nonneg_left (sum_delta_ball_le hδ hsep s hR) (by positivity)
    have : τ * R s < ballSum lam mb s (R s) + τ / 6 * (3 * R s) := by
      change τ * R s < ballSum lam m s (R s) at hlt
      rw [hsplit] at hlt; linarith
    nlinarith
  have h := sum_delta_le_of_ballSum_gt hδ hsep (half_pos hτ) R E mb hmbnn hE
  have hmb_sum : ∑ t, mb t = ∑ t ∈ univ.filter (fun t => τ < 6 * a t / Real.sqrt (δ t)), m t := by
    rw [Finset.sum_filter]
  rw [hmb_sum, show 5 / (τ / 2) = 10 / τ by field_simp; ring] at h
  exact h

lemma intervalIntegrable_indicator_Iio (A X : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    IntervalIntegrable ((Set.Iio A).indicator f) volume 0 X := by
  rw [intervalIntegrable_iff]
  exact (hf.integrableOn_Icc.mono_set Set.uIoc_subset_uIcc).indicator measurableSet_Iio

lemma integral_indicator_Iio {A X : ℝ} (hA : 0 ≤ A) (hAX : A ≤ X) (f : ℝ → ℝ) :
    ∫ τ in (0 : ℝ)..X, (Set.Iio A).indicator f τ = ∫ τ in (0 : ℝ)..A, f τ := by
  rw [intervalIntegral.integral_of_le (hA.trans hAX), setIntegral_indicator measurableSet_Iio,
    intervalIntegral.integral_of_le hA, integral_Ioc_eq_integral_Ioo]
  rw [show Set.Ioc 0 X ∩ Set.Iio A = Set.Ioo 0 A from ?_]
  ext τ
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩

/-- **The maximal inequality**: `∑_s δ_s M_s² ≤ 120 ∑_t a_t²`, `M_s` the maximal average of
the masses `a_t √δ_t` about `λ_s` (layer-cake formula and the weak-type bound). -/
theorem sum_delta_mul_maxAvg_sq_le (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) {a : ι → ℝ}
    (ha : ∀ t, 0 ≤ a t) :
    ∑ s, δ s * maxAvg lam (fun t => a t * Real.sqrt (δ t)) s ^ 2 ≤ 120 * ∑ t, a t ^ 2 := by
  set m : ι → ℝ := fun t => a t * Real.sqrt (δ t) with hmdef
  have hmnn : ∀ t, 0 ≤ m t := fun t => mul_nonneg (ha t) (Real.sqrt_nonneg _)
  set M : ι → ℝ := fun s => maxAvg lam m s with hM
  set c : ι → ℝ := fun t => 6 * a t / Real.sqrt (δ t) with hc
  have hMnn : ∀ s, 0 ≤ M s := fun s => maxAvg_nonneg hmnn s
  have hcnn : ∀ t, 0 ≤ c t := fun t => div_nonneg (by linarith [ha t]) (Real.sqrt_nonneg _)
  set X : ℝ := ∑ s, M s + ∑ t, c t with hX
  have hMX : ∀ s, M s ≤ X := fun s => by
    have h1 := Finset.single_le_sum (fun i _ => hMnn i) (Finset.mem_univ s)
    have h2 := Finset.sum_nonneg (fun i (_ : i ∈ univ) => hcnn i)
    linarith
  have hcX : ∀ t, c t ≤ X := fun t => by
    have h1 := Finset.single_le_sum (fun i _ => hcnn i) (Finset.mem_univ t)
    have h2 := Finset.sum_nonneg (fun i (_ : i ∈ univ) => hMnn i)
    linarith
  have hX0 : 0 ≤ X :=
    add_nonneg (Finset.sum_nonneg fun s _ => hMnn s) (Finset.sum_nonneg fun t _ => hcnn t)
  -- the left side as an integral over the levels
  have hL : ∑ s, δ s * M s ^ 2
      = ∫ τ in (0 : ℝ)..X, ∑ s, δ s * (Set.Iio (M s)).indicator (fun τ => 2 * τ) τ := by
    rw [intervalIntegral.integral_finsetSum fun s _ =>
      (intervalIntegrable_indicator_Iio _ _ _ (by fun_prop)).const_mul _]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_indicator_Iio (hMnn s) (hMX s)]
    congr 1
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hR : 120 * ∑ t, a t ^ 2
      = ∫ τ in (0 : ℝ)..X, 20 * ∑ t, m t * (Set.Iio (c t)).indicator (fun _ => (1 : ℝ)) τ := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun t _ =>
      (intervalIntegrable_indicator_Iio _ _ _ (by fun_prop)).const_mul _, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_indicator_Iio (hcnn t) (hcX t)]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero, hc, hmdef]
    have hs : 0 < Real.sqrt (δ t) := Real.sqrt_pos.mpr (hδ t)
    field_simp
    ring
  rw [hL, hR]
  have hI1 : IntervalIntegrable
      (fun τ => ∑ s, δ s * (Set.Iio (M s)).indicator (fun τ => 2 * τ) τ) volume 0 X := by
    have := IntervalIntegrable.sum univ (fun s _ =>
      (intervalIntegrable_indicator_Iio (M s) X (fun τ => 2 * τ) (by fun_prop)).const_mul (δ s))
    rw [Finset.sum_fn] at this; exact this
  have hI2 : IntervalIntegrable
      (fun τ => ∑ t, m t * (Set.Iio (c t)).indicator (fun _ => (1 : ℝ)) τ) volume 0 X := by
    have := IntervalIntegrable.sum univ (fun t _ =>
      (intervalIntegrable_indicator_Iio (c t) X (fun _ => (1 : ℝ)) (by fun_prop)).const_mul
        (m t))
    rw [Finset.sum_fn] at this; exact this
  refine intervalIntegral.integral_mono_on hX0 hI1 (hI2.const_mul _) fun τ hτ => ?_
  have hlhs : ∑ s, δ s * (Set.Iio (M s)).indicator (fun τ => 2 * τ) τ
      = 2 * τ * ∑ s ∈ univ.filter (fun s => τ < M s), δ s := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : τ < M s
    · rw [Set.indicator_of_mem (Set.mem_Iio.mpr h), if_pos h]; ring
    · rw [Set.indicator_of_notMem (by simpa using h), if_neg h]; ring
  have hrhs : ∑ t, m t * (Set.Iio (c t)).indicator (fun _ => (1 : ℝ)) τ
      = ∑ t ∈ univ.filter (fun t => τ < c t), m t := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : τ < c t
    · rw [Set.indicator_of_mem (Set.mem_Iio.mpr h), if_pos h, mul_one]
    · rw [Set.indicator_of_notMem (by simpa using h), if_neg h, mul_zero]
  rw [hlhs, hrhs]
  rcases eq_or_lt_of_le hτ.1 with h0 | hpos
  · rw [← h0]; simp only [mul_zero, zero_mul]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun t _ => hmnn t)
  have hw := sum_delta_maxAvg_gt_le hδ hsep ha hpos
  calc 2 * τ * ∑ s ∈ univ.filter (fun s => τ < M s), δ s
      ≤ 2 * τ * (10 / τ * ∑ t ∈ univ.filter (fun t => τ < c t), m t) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = 20 * ∑ t ∈ univ.filter (fun t => τ < c t), m t := by field_simp; ring

lemma integral_Ioi_two_mul_rpow_neg_three {c : ℝ} (hc : 0 < c) :
    ∫ R in Set.Ioi c, 2 * R ^ (-3 : ℝ) = 1 / c ^ 2 := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hc]
  rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hc.le]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- Summation by parts: `∑_{t ≠ s} m_t / (λ_s - λ_t)² ≤ 2 A / δ_s` if every ball of radius `R`
about `λ_s` carries mass at most `A R`. -/
lemma sum_div_sq_le_of_ballSum_le (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) {m : ι → ℝ}
    (hm : ∀ t, 0 ≤ m t) (s : ι) {A : ℝ}
    (hball : ∀ R, 0 ≤ R → ballSum lam m s R ≤ A * R) :
    ∑ t ∈ univ.erase s, m t / (lam s - lam t) ^ 2 ≤ 2 * A / δ s := by
  have hδs := hδ s
  set f : ℝ → ℝ := fun R => 2 * R ^ (-3 : ℝ) with hf
  have hfint : IntegrableOn f (Set.Ioi (δ s)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hδs).const_mul 2
  have hd : ∀ t ∈ univ.erase s, δ s ≤ |lam s - lam t| := fun t ht =>
    hsep s t (Finset.ne_of_mem_erase ht).symm
  have hterm : ∀ t ∈ univ.erase s, m t / (lam s - lam t) ^ 2
      = ∫ R in Set.Ioi (δ s), m t * (Set.Ioi |lam s - lam t|).indicator f R := by
    intro t ht
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
      sup_eq_right.mpr (hd t ht), integral_Ioi_two_mul_rpow_neg_three
        (lt_of_lt_of_le hδs (hd t ht)), sq_abs]
    ring
  rw [Finset.sum_congr rfl hterm, ← integral_finsetSum _ fun t _ =>
    (hfint.indicator measurableSet_Ioi).const_mul _]
  have hg : IntegrableOn (fun R => 2 * A * R ^ (-2 : ℝ)) (Set.Ioi (δ s)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hδs).const_mul _
  have hrhs : ∫ R in Set.Ioi (δ s), 2 * A * R ^ (-2 : ℝ) = 2 * A / δ s := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hδs]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  rw [← hrhs]
  have hint : IntegrableOn (fun R => ∑ t ∈ univ.erase s,
      m t * (Set.Ioi |lam s - lam t|).indicator f R) (Set.Ioi (δ s)) := by
    have := integrable_finsetSum (univ.erase s) fun t _ =>
      ((hfint.indicator (measurableSet_Ioi (a := |lam s - lam t|))).const_mul (m t))
    exact this
  refine setIntegral_mono_on hint hg measurableSet_Ioi fun R hR => ?_
  have hR0 : 0 < R := lt_trans hδs hR
  have hsum : ∑ t ∈ univ.erase s, m t * (Set.Ioi |lam s - lam t|).indicator f R
      ≤ f R * ballSum lam m s R := by
    unfold ballSum
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases h : |lam s - lam t| < R
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h), if_pos h.le, mul_comm]
    · rw [Set.indicator_of_notMem (by simpa using h), mul_zero]
      split_ifs
      · exact mul_nonneg (by positivity) (hm t)
      · exact le_rfl
  have hfR : 0 ≤ f R := by positivity
  calc ∑ t ∈ univ.erase s, m t * (Set.Ioi |lam s - lam t|).indicator f R
      ≤ f R * ballSum lam m s R := hsum
    _ ≤ f R * (A * R) := mul_le_mul_of_nonneg_left (hball R hR0.le) hfR
    _ = 2 * A * R ^ (-2 : ℝ) := by
        simp only [hf]
        rw [show 2 * R ^ (-3 : ℝ) * (A * R) = 2 * A * (R ^ (-3 : ℝ) * R) by ring,
          ← Real.rpow_add_one hR0.ne']
        norm_num

/-- `δ_s ∑_{t ≠ s} δ_t / (λ_s - λ_t)² ≤ 6`. -/
lemma delta_mul_sum_delta_div_sq_le (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) (s : ι) :
    δ s * ∑ t ∈ univ.erase s, δ t / (lam s - lam t) ^ 2 ≤ 6 := by
  have h := sum_div_sq_le_of_ballSum_le hδ hsep (fun t => (hδ t).le) s (A := 3)
    (fun R hR => sum_delta_ball_le hδ hsep s hR)
  have hδs := hδ s
  calc δ s * ∑ t ∈ univ.erase s, δ t / (lam s - lam t) ^ 2 ≤ δ s * (2 * 3 / δ s) :=
        mul_le_mul_of_nonneg_left h hδs.le
    _ = 6 := by field_simp; norm_num

/-- The positive kernel `δ_s^{3/2} δ_t^{1/2} / (λ_s - λ_t)²` is bounded on `ℓ²`:
`∑_{s ≠ t} a_s a_t δ_s √δ_s √δ_t / (λ_s - λ_t)² ≤ 2 √120 ∑ a_t²` for `a ≥ 0`. -/
theorem sum_sum_mul_div_sq_le (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : ι, r ≠ s → δ r ≤ |lam r - lam s|) {a : ι → ℝ}
    (ha : ∀ t, 0 ≤ a t) :
    ∑ s, ∑ t ∈ univ.erase s,
        a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t)) / (lam s - lam t) ^ 2
      ≤ 2 * Real.sqrt 120 * ∑ t, a t ^ 2 := by
  set m : ι → ℝ := fun t => a t * Real.sqrt (δ t) with hmdef
  have hmnn : ∀ t, 0 ≤ m t := fun t => mul_nonneg (ha t) (Real.sqrt_nonneg _)
  set M : ι → ℝ := fun s => maxAvg lam m s with hM
  have hMnn : ∀ s, 0 ≤ M s := fun s => maxAvg_nonneg hmnn s
  have hrow : ∀ s, ∑ t ∈ univ.erase s,
      a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t)) / (lam s - lam t) ^ 2
      ≤ 2 * (a s * (Real.sqrt (δ s) * M s)) := by
    intro s
    have hδs := hδ s
    have h := sum_div_sq_le_of_ballSum_le hδ hsep hmnn s
      (fun R hR => ballSum_le_maxAvg_mul hδ hsep hmnn s hR)
    have heq : ∑ t ∈ univ.erase s,
        a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t)) / (lam s - lam t) ^ 2
        = a s * δ s * Real.sqrt (δ s) * ∑ t ∈ univ.erase s, m t / (lam s - lam t) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [hmdef]; ring
    rw [heq]
    have hc : 0 ≤ a s * δ s * Real.sqrt (δ s) :=
      mul_nonneg (mul_nonneg (ha s) hδs.le) (Real.sqrt_nonneg _)
    calc a s * δ s * Real.sqrt (δ s) * ∑ t ∈ univ.erase s, m t / (lam s - lam t) ^ 2
        ≤ a s * δ s * Real.sqrt (δ s) * (2 * M s / δ s) := mul_le_mul_of_nonneg_left h hc
      _ = 2 * (a s * (Real.sqrt (δ s) * M s)) := by field_simp
  have hmax := sum_delta_mul_maxAvg_sq_le hδ hsep ha
  have hcs : ∑ s, a s * (Real.sqrt (δ s) * M s)
      ≤ Real.sqrt (∑ s, a s ^ 2) * Real.sqrt (∑ s, (Real.sqrt (δ s) * M s) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hsq : ∑ s, (Real.sqrt (δ s) * M s) ^ 2 = ∑ s, δ s * M s ^ 2 :=
    Finset.sum_congr rfl fun s _ => by rw [mul_pow, Real.sq_sqrt (hδ s).le]
  have hA : 0 ≤ ∑ s, a s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have h2 : Real.sqrt (∑ s, δ s * M s ^ 2) ≤ Real.sqrt 120 * Real.sqrt (∑ s, a s ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hmax
  calc ∑ s, ∑ t ∈ univ.erase s,
        a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t)) / (lam s - lam t) ^ 2
      ≤ ∑ s, 2 * (a s * (Real.sqrt (δ s) * M s)) := Finset.sum_le_sum fun s _ => hrow s
    _ = 2 * ∑ s, a s * (Real.sqrt (δ s) * M s) := by rw [Finset.mul_sum]
    _ ≤ 2 * (Real.sqrt (∑ s, a s ^ 2) * (Real.sqrt 120 * Real.sqrt (∑ s, a s ^ 2))) := by
        rw [hsq] at hcs
        refine mul_le_mul_of_nonneg_left (hcs.trans ?_) (by norm_num)
        exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt 120 * ∑ t, a t ^ 2 := by
        rw [show Real.sqrt (∑ s, a s ^ 2) * (Real.sqrt 120 * Real.sqrt (∑ s, a s ^ 2))
          = Real.sqrt 120 * (Real.sqrt (∑ s, a s ^ 2) * Real.sqrt (∑ s, a s ^ 2)) by ring,
          Real.mul_self_sqrt hA]
        ring

end Spacing

end LocalSpacing

end RiemannHypothesis
