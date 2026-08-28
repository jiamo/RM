/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroExists
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# `ζ` has infinitely many nontrivial zeroes

`RiemannHypothesis/ZeroExists.lean` produces one zero of `ζ` in the open critical strip. Here the
same growth argument is pushed to its conclusion: the strip contains **infinitely many** zeroes.

If there were only finitely many, `ξ` would be a *polynomial times* a nowhere-vanishing entire
function (`exists_rootMultiset_factorization`, an induction on the total order of vanishing that
divides out one root at a time through `dslope`). The nonvanishing factor is `exp G` with `G`
entire, its real part is `O(‖z‖ log ‖z‖)` — the polynomial factor is `≥ 1` far out, and `G` is
bounded on the remaining compact disc — so `G` is linear by `linear_of_re_le`, and `‖ξ‖` would
grow at most exponentially along the real axis, which `xiFn_growth_contradiction` forbids.
-/

noncomputable section

open Complex Metric Filter

namespace RiemannHypothesis

/-! ## Dividing out the zeroes of an entire function -/

/-- The difference quotient of an entire function is entire. -/
lemma differentiable_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (dslope f a) := by
  rw [← differentiableOn_univ]
  exact (differentiableOn_dslope (f := f) (s := Set.univ) (c := a) Filter.univ_mem).mpr
    hf.differentiableOn

/-- An entire function that is nonzero somewhere vanishes to finite order everywhere. -/
lemma analyticOrderAt_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) {w : ℂ} (hw : f w ≠ 0)
    (σ : ℂ) : analyticOrderAt f σ ≠ ⊤ := by
  rw [Ne, analyticOrderAt_eq_top]
  intro h
  have hA : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  exact hw (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ σ) h (Set.mem_univ w))

/-- The product `∏_{ρ ∈ m} (z − ρ)` over a multiset of roots. -/
def rootProd (m : Multiset ℂ) (z : ℂ) : ℂ := (m.map (fun ρ => z - ρ)).prod

@[simp] lemma rootProd_zero (z : ℂ) : rootProd 0 z = 1 := by simp [rootProd]

@[simp] lemma rootProd_cons (a : ℂ) (m : Multiset ℂ) (z : ℂ) :
    rootProd (a ::ₘ m) z = (z - a) * rootProd m z := by
  simp [rootProd]

/-- `‖∏_{ρ ∈ m} (z − ρ)‖ ≤ (‖z‖ + M)^{card m}` when every root has `‖ρ‖ ≤ M`. -/
lemma norm_rootProd_le {m : Multiset ℂ} {M : ℝ} (hM : ∀ ρ ∈ m, ‖ρ‖ ≤ M) (z : ℂ) :
    ‖rootProd m z‖ ≤ (‖z‖ + M) ^ (Multiset.card m) := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih =>
    have ha : ‖a‖ ≤ M := hM a (Multiset.mem_cons_self a m)
    have hrest : ∀ ρ ∈ m, ‖ρ‖ ≤ M := fun ρ hρ => hM ρ (Multiset.mem_cons_of_mem hρ)
    have h0 : (0 : ℝ) ≤ ‖z‖ + M := le_trans (norm_nonneg a) (by linarith [norm_nonneg z])
    have h1 : ‖z - a‖ ≤ ‖z‖ + M := le_trans (norm_sub_le z a) (by linarith)
    calc ‖rootProd (a ::ₘ m) z‖ = ‖z - a‖ * ‖rootProd m z‖ := by
          rw [rootProd_cons, norm_mul]
      _ ≤ (‖z‖ + M) * (‖z‖ + M) ^ (Multiset.card m) :=
          mul_le_mul h1 (ih hrest) (norm_nonneg _) h0
      _ = (‖z‖ + M) ^ (Multiset.card (a ::ₘ m)) := by
          rw [Multiset.card_cons, pow_succ]; ring

/-- Far from all its roots the product `∏_{ρ ∈ m}(z − ρ)` has norm at least one. -/
lemma one_le_norm_rootProd {m : Multiset ℂ} {M : ℝ} (hM : ∀ ρ ∈ m, ‖ρ‖ ≤ M) {z : ℂ}
    (hz : M + 1 ≤ ‖z‖) : 1 ≤ ‖rootProd m z‖ := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih =>
    have ha : ‖a‖ ≤ M := hM a (Multiset.mem_cons_self a m)
    have hrest : ∀ ρ ∈ m, ‖ρ‖ ≤ M := fun ρ hρ => hM ρ (Multiset.mem_cons_of_mem hρ)
    have h1 : 1 ≤ ‖z - a‖ := by
      have := norm_sub_norm_le z a
      linarith
    have h2 : 1 ≤ ‖rootProd m z‖ := ih hrest
    rw [rootProd_cons, norm_mul]
    nlinarith

/-- The inductive step of `exists_rootMultiset_factorization`: an induction on (a bound for) the
total order of vanishing of `f` on `S`, dividing out one root at a time. -/
theorem exists_rootMultiset_factorization_aux : ∀ (N : ℕ) (f : ℂ → ℂ), Differentiable ℂ f →
    ∀ (w : ℂ), f w ≠ 0 → ∀ (S : Finset ℂ), (∀ z, f z = 0 → z ∈ S) →
    (∑ ρ ∈ S, analyticOrderNatAt f ρ) ≤ N →
    ∃ (m : Multiset ℂ) (g : ℂ → ℂ), (∀ ρ ∈ m, ρ ∈ S) ∧ Differentiable ℂ g ∧ (∀ z, g z ≠ 0) ∧
      ∀ z, f z = rootProd m z * g z := by
  intro N
  induction N with
  | zero =>
    intro f hf w hw S hS hsum
    refine ⟨0, f, by simp, hf, ?_, by simp⟩
    intro z hz
    have hle := Finset.single_le_sum (f := fun ρ => analyticOrderNatAt f ρ)
      (fun i _ => Nat.zero_le _) (hS z hz)
    have h1 : analyticOrderNatAt f z = 0 := by omega
    have h2 : analyticOrderAt f z = 0 := by
      rcases ENat.toNat_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (analyticOrderAt_ne_top hf hw z)
    rcases analyticOrderAt_eq_zero.mp h2 with h | h
    · exact h (hf.analyticAt z)
    · exact h hz
  | succ N ih =>
    intro f hf w hw S hS hsum
    by_cases hzero : ∀ z, f z ≠ 0
    · exact ⟨0, f, by simp, hf, hzero, by simp⟩
    push Not at hzero
    obtain ⟨a, ha⟩ := hzero
    have haS : a ∈ S := hS a ha
    have hf₁ : Differentiable ℂ (dslope f a) := differentiable_dslope hf a
    have hprod : ∀ z, f z = (z - a) * dslope f a z := by
      intro z
      have h := sub_smul_dslope f a z
      rw [ha, sub_zero, smul_eq_mul] at h
      exact h.symm
    have hfe : f = (fun z => z - a) * dslope f a := funext (by intro z; simpa using hprod z)
    have hw₁ : dslope f a w ≠ 0 := fun h => hw (by rw [hprod w, h, mul_zero])
    have hS₁ : ∀ z, dslope f a z = 0 → z ∈ S := fun z hz => hS z (by rw [hprod z, hz, mul_zero])
    have hAlin : ∀ σ : ℂ, AnalyticAt ℂ (fun z : ℂ => z - a) σ := by intro σ; fun_prop
    have hordmul : ∀ σ : ℂ, analyticOrderAt f σ
        = analyticOrderAt (fun z : ℂ => z - a) σ + analyticOrderAt (dslope f a) σ := by
      intro σ
      conv_lhs => rw [hfe]
      exact analyticOrderAt_mul (hAlin σ) (hf₁.analyticAt σ)
    have hlin1 : analyticOrderAt (fun z : ℂ => z - a) a = 1 := by
      rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) by rfl, (hAlin a).analyticOrderAt_eq_natCast]
      exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, by filter_upwards with z; simp⟩
    have hne₁ : ∀ σ, analyticOrderAt (dslope f a) σ ≠ ⊤ := analyticOrderAt_ne_top hf₁ hw₁
    have hother : ∀ σ ∈ S, σ ≠ a →
        analyticOrderNatAt (dslope f a) σ = analyticOrderNatAt f σ := by
      intro σ _ h
      have hlin0 : analyticOrderAt (fun z : ℂ => z - a) σ = 0 := by
        rw [analyticOrderAt_eq_zero]
        exact Or.inr (by simpa [sub_eq_zero] using h)
      unfold analyticOrderNatAt
      rw [hordmul σ, hlin0, zero_add]
    have hata : analyticOrderNatAt f a = analyticOrderNatAt (dslope f a) a + 1 := by
      obtain ⟨x, hx⟩ : ∃ x : ℕ, analyticOrderAt (dslope f a) a = (x : ℕ∞) :=
        ⟨_, (ENat.coe_toNat (hne₁ a)).symm⟩
      unfold analyticOrderNatAt
      rw [hordmul a, hlin1, hx, show (1 : ℕ∞) + (x : ℕ∞) = ((1 + x : ℕ) : ℕ∞) by push_cast; ring]
      simp only [ENat.toNat_coe]
      omega
    have hsum₁ : (∑ ρ ∈ S, analyticOrderNatAt (dslope f a) ρ) ≤ N := by
      have h1 : ∑ ρ ∈ S, analyticOrderNatAt f ρ
          = analyticOrderNatAt f a + ∑ ρ ∈ S.erase a, analyticOrderNatAt f ρ :=
        (Finset.add_sum_erase S _ haS).symm
      have h2 : ∑ ρ ∈ S, analyticOrderNatAt (dslope f a) ρ
          = analyticOrderNatAt (dslope f a) a
            + ∑ ρ ∈ S.erase a, analyticOrderNatAt (dslope f a) ρ :=
        (Finset.add_sum_erase S _ haS).symm
      have h3 : ∑ ρ ∈ S.erase a, analyticOrderNatAt (dslope f a) ρ
          = ∑ ρ ∈ S.erase a, analyticOrderNatAt f ρ :=
        Finset.sum_congr rfl fun σ hσ =>
          hother σ (Finset.mem_of_mem_erase hσ) (Finset.ne_of_mem_erase hσ)
      rw [h2, h3]
      omega
    obtain ⟨m, g, hm, hg, hg0, hfac⟩ := ih (dslope f a) hf₁ w hw₁ S hS₁ hsum₁
    refine ⟨a ::ₘ m, g, ?_, hg, hg0, fun z => by rw [hprod z, hfac z, rootProd_cons, mul_assoc]⟩
    intro ρ hρ
    rcases Multiset.mem_cons.mp hρ with h | h
    · exact h ▸ haS
    · exact hm ρ h

/-- **Factoring out finitely many zeroes.**  An entire function with finitely many zeroes, not
identically zero, is a finite product `∏(z − ρ)` times an entire function without zeroes. -/
theorem exists_rootMultiset_factorization {f : ℂ → ℂ} (hf : Differentiable ℂ f) {w : ℂ}
    (hw : f w ≠ 0) (S : Finset ℂ) (hS : ∀ z, f z = 0 → z ∈ S) :
    ∃ (m : Multiset ℂ) (g : ℂ → ℂ), (∀ ρ ∈ m, ρ ∈ S) ∧ Differentiable ℂ g ∧ (∀ z, g z ≠ 0) ∧
      ∀ z, f z = rootProd m z * g z :=
  exists_rootMultiset_factorization_aux (∑ ρ ∈ S, analyticOrderNatAt f ρ) f hf w hw S hS le_rfl

/-! ## Infinitely many zeroes -/

/-- The zeroes of `ξ` are exactly the nontrivial zeroes of `ζ`. -/
lemma xiFn_eq_zero_iff_mem_nontrivialZeroSet {s : ℂ} :
    xiFn s = 0 ↔ s ∈ nontrivialZeroSet := by
  constructor
  · intro hs
    have hxi : riemannXi (-I * (s - 1 / 2)) = 0 := by
      rw [riemannXi_eq_xiFn, xiPoint_neg_I_mul_sub]
      exact hs
    obtain ⟨h0, h1, hz⟩ := riemannXi_eq_zero_iff.mp hxi
    rw [xiPoint_neg_I_mul_sub] at h0 h1 hz
    exact ⟨hz, h0, h1⟩
  · rintro ⟨hz, h0, h1⟩
    exact xiFn_eq_zero_of_zeta h0 h1 hz

/-- **`ζ` has infinitely many zeroes in the open critical strip.**  Were there only finitely
many, `ξ` would be a polynomial times `exp` of a linear function, and so of at most exponential
growth along the real axis. -/
theorem infinite_nontrivialZeroSet : nontrivialZeroSet.Infinite := by
  intro hfin
  -- factor the finitely many zeroes out of `ξ`
  have hS : ∀ z, xiFn z = 0 → z ∈ hfin.toFinset := fun z hz =>
    hfin.mem_toFinset.mpr (xiFn_eq_zero_iff_mem_nontrivialZeroSet.mp hz)
  obtain ⟨m, g, hm, hg, hg0, hfac⟩ :=
    exists_rootMultiset_factorization differentiable_xiFn xiFn_two_ne_zero hfin.toFinset hS
  set M : ℝ := ∑ ρ ∈ hfin.toFinset, ‖ρ‖ with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hMbound : ∀ ρ ∈ m, ‖ρ‖ ≤ M :=
    fun ρ hρ => Finset.single_le_sum (f := fun σ : ℂ => ‖σ‖) (fun _ _ => norm_nonneg _) (hm ρ hρ)
  set d : ℕ := Multiset.card m with hd
  -- the nonvanishing factor is an exponential
  obtain ⟨G, hGdiff, hG⟩ := exists_exp_of_ne_zero hg hg0
  obtain ⟨C, hC0, hC⟩ := norm_xiFn_le
  -- `re G` is `O(‖z‖ log ‖z‖)`: far out because the product factor is at least one in modulus,
  -- and near the origin because `G` is continuous on a compact disc
  have hfar : ∀ z : ℂ, M + 1 ≤ ‖z‖ → (G z).re ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
    intro z hz
    have hP : 1 ≤ ‖rootProd m z‖ := one_le_norm_rootProd hMbound hz
    have h1 : Real.exp ((G z).re) = ‖g z‖ := by rw [hG z, Complex.norm_exp]
    have h2 : ‖g z‖ ≤ ‖xiFn z‖ := by
      rw [hfac z, norm_mul]
      nlinarith [norm_nonneg (g z)]
    have h3 : Real.exp ((G z).re) ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :=
      le_trans (by rw [h1]; exact h2) (hC z)
    exact Real.exp_le_exp.mp h3
  obtain ⟨D, hD0, hnear⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℂ, ‖z‖ ≤ M + 1 → (G z).re ≤ D := by
    have hcont : Continuous fun z : ℂ => (G z).re := Complex.continuous_re.comp hGdiff.continuous
    obtain ⟨z₀, _, hz₀⟩ := (isCompact_closedBall (0 : ℂ) (M + 1)).exists_isMaxOn
      (Metric.nonempty_closedBall.mpr (by linarith)) hcont.continuousOn
    refine ⟨max ((G z₀).re) 0, le_max_right _ _, fun z hz => ?_⟩
    refine le_trans (hz₀ ?_) (le_max_left _ _)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre : ∀ z : ℂ, (G z).re ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) + D := by
    intro z
    have hlog : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    have hpos : 0 ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
      mul_nonneg (mul_nonneg hC0.le (by positivity)) hlog
    rcases le_or_gt (M + 1) ‖z‖ with h | h
    · linarith [hfar z h]
    · linarith [hnear z h.le]
  obtain ⟨a, b, hab⟩ := linear_of_re_le hGdiff hC0.le hD0 hre
  -- hence `‖ξ‖` grows at most exponentially along the real axis
  refine xiFn_growth_contradiction
    (B := ((2 + M) ^ d * Real.exp ‖a‖) * Real.exp ((d : ℝ) + 2 * ‖b‖))
    (L := Real.exp ((d : ℝ) + 2 * ‖b‖)) (by positivity) fun n _ => ?_
  set z : ℂ := 2 * ((n : ℂ) + 1) with hzdef
  set t : ℝ := (n : ℝ) + 1 with htdef
  have ht1 : 1 ≤ t := by simp [htdef]
  have hzn : ‖z‖ = 2 * t := by
    rw [hzdef, htdef, ← Complex.ofReal_natCast,
      show (2 : ℂ) * ((n : ℝ) + 1) = ((2 * ((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- the product factor
  have hprod : ‖rootProd m z‖ ≤ (2 + M) ^ d * Real.exp ((d : ℝ) * t) := by
    have h1 : ‖rootProd m z‖ ≤ (‖z‖ + M) ^ d := norm_rootProd_le hMbound z
    have h2 : ‖z‖ + M ≤ (2 + M) * Real.exp t := by
      have hte : t ≤ Real.exp t := le_trans (by linarith) (Real.add_one_le_exp t)
      nlinarith [Real.exp_pos t]
    have h3 : (‖z‖ + M) ^ d ≤ ((2 + M) * Real.exp t) ^ d :=
      pow_le_pow_left₀ (by positivity) h2 d
    have h4 : ((2 + M) * Real.exp t) ^ d = (2 + M) ^ d * Real.exp ((d : ℝ) * t) := by
      rw [mul_pow, ← Real.exp_nat_mul]
    linarith [h1, h3, h4.le, h4.ge]
  -- the exponential factor
  have hexpfac : ‖g z‖ ≤ Real.exp ‖a‖ * Real.exp (2 * ‖b‖ * t) := by
    rw [hG z, Complex.norm_exp, hab z]
    have h1 : (a + b * z).re ≤ ‖a‖ + 2 * ‖b‖ * t := by
      have h2 : (a + b * z).re ≤ ‖a + b * z‖ := Complex.re_le_norm _
      have h3 : ‖a + b * z‖ ≤ ‖a‖ + ‖b‖ * ‖z‖ :=
        le_trans (norm_add_le _ _) (by rw [norm_mul])
      rw [hzn] at h3
      linarith
    calc Real.exp ((a + b * z).re) ≤ Real.exp (‖a‖ + 2 * ‖b‖ * t) := Real.exp_le_exp.mpr h1
      _ = Real.exp ‖a‖ * Real.exp (2 * ‖b‖ * t) := Real.exp_add _ _
  -- put the two together
  have hfinal : ‖xiFn z‖ ≤ ((2 + M) ^ d * Real.exp ‖a‖) * Real.exp (((d : ℝ) + 2 * ‖b‖) * t) := by
    rw [hfac z, norm_mul]
    calc ‖rootProd m z‖ * ‖g z‖
        ≤ ((2 + M) ^ d * Real.exp ((d : ℝ) * t)) * (Real.exp ‖a‖ * Real.exp (2 * ‖b‖ * t)) :=
          mul_le_mul hprod hexpfac (norm_nonneg _) (by positivity)
      _ = ((2 + M) ^ d * Real.exp ‖a‖) * Real.exp (((d : ℝ) + 2 * ‖b‖) * t) := by
          rw [show ((d : ℝ) + 2 * ‖b‖) * t = (d : ℝ) * t + 2 * ‖b‖ * t by ring, Real.exp_add]
          ring
  refine le_trans hfinal (le_of_eq ?_)
  have hsplit : Real.exp (((d : ℝ) + 2 * ‖b‖) * t)
      = Real.exp ((d : ℝ) + 2 * ‖b‖) * (Real.exp ((d : ℝ) + 2 * ‖b‖)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, htdef]
    congr 1
    ring
  rw [hsplit]
  ring

/-- **`ξ` has infinitely many zeroes.** -/
theorem infinite_setOf_xiFn_eq_zero : {s : ℂ | xiFn s = 0}.Infinite := by
  have h : {s : ℂ | xiFn s = 0} = nontrivialZeroSet :=
    Set.ext fun s => xiFn_eq_zero_iff_mem_nontrivialZeroSet
  rw [h]
  exact infinite_nontrivialZeroSet

end RiemannHypothesis
