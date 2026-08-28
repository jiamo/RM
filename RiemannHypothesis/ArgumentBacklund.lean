/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.LittlewoodZetaBound

/-!
# Backlund's counting bound for the variation of a continuous argument

`RiemannHypothesis.LittlewoodZetaBound` shows that a continuous real function whose cosine never
vanishes on an interval moves by less than `π`.  Backlund's observation is that the *number of
zeroes of the cosine* controls the total variation: if the cosine vanishes at `n` points of the
interval, the function moves by at most `(n + 1) π`.

Applied to a continuous branch `θ` of the argument of a holomorphic function `f` along a segment,
`cos θ = 0` exactly where `re f = 0`, so the variation of the argument of `f` along the segment is
at most `(n + 1) π` where `n` counts the zeroes of `re f` on it.  This is the elementary half of
the classical estimate `S(t) = O(log t)`; the other half is a Jensen-type count of the zeroes of
`re f`.

## Main results

* `abs_sub_le_pi_of_forall_cos_ne_zero_Ioo` — the open-interval form of the `π` bound: only the
  interior of the interval has to be free of zeroes of the cosine.
* `abs_sub_le_of_ncard_cos_eq_zero` — **Backlund's bound**: if the cosine of a continuous function
  `θ` vanishes at no more than `n` points of `(a, b]`, then `|θ b − θ a| ≤ (n + 1) π`.
-/

noncomputable section

open Real Set

open scoped Interval

namespace RiemannHypothesis

/-- **The `π` bound with the endpoints excluded.**  If the cosine of a continuous function does
not vanish anywhere in the *open* interval, the function moves by at most `π` across the closed
one: apply the strict bound on a slightly smaller interval and let it grow. -/
theorem abs_sub_le_pi_of_forall_cos_ne_zero_Ioo {theta : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn theta (Icc a b)) (h : ∀ t ∈ Ioo a b, Real.cos (theta t) ≠ 0) :
    |theta b - theta a| ≤ π := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simpa using Real.pi_pos.le
  refine le_of_forall_pos_le_add fun eps heps => ?_
  -- continuity at the two endpoints
  have hca : ContinuousWithinAt theta (Icc a b) a := hc a (left_mem_Icc.2 hab)
  have hcb : ContinuousWithinAt theta (Icc a b) b := hc b (right_mem_Icc.2 hab)
  obtain ⟨d1, hd1, hA⟩ := Metric.continuousWithinAt_iff.1 hca (eps / 2) (by linarith)
  obtain ⟨d2, hd2, hB⟩ := Metric.continuousWithinAt_iff.1 hcb (eps / 2) (by linarith)
  set m : ℝ := (a + b) / 2 with hm
  have hma : a < m := by rw [hm]; linarith
  have hmb : m < b := by rw [hm]; linarith
  set c : ℝ := min (a + d1 / 2) m with hcdef
  set d : ℝ := max (b - d2 / 2) m with hddef
  have hac : a < c := lt_min (by linarith) hma
  have hcm : c ≤ m := min_le_right _ _
  have hmd : m ≤ d := le_max_right _ _
  have hdb : d < b := max_lt (by linarith) hmb
  have hcd : c ≤ d := le_trans hcm hmd
  have hsub : Icc c d ⊆ Ioo a b := fun x hx => ⟨lt_of_lt_of_le hac hx.1, lt_of_le_of_lt hx.2 hdb⟩
  have hsub' : Icc c d ⊆ Icc a b := fun x hx => ⟨le_of_lt (hsub hx).1, le_of_lt (hsub hx).2⟩
  have hstrict : |theta d - theta c| < π := by
    refine abs_sub_lt_pi_of_forall_cos_ne_zero (c := c) (d := d) ?_ ?_
    · rw [uIcc_of_le hcd]; exact hc.mono hsub'
    · intro t ht
      rw [uIcc_of_le hcd] at ht
      exact h t (hsub ht)
  have h1 : |theta c - theta a| < eps / 2 := by
    have := hA (x := c) ⟨hac.le, hcm.trans hmb.le⟩
      (by rw [Real.dist_eq, abs_of_pos (by linarith)]
          have : c ≤ a + d1 / 2 := min_le_left _ _
          linarith)
    rwa [Real.dist_eq] at this
  have h2 : |theta b - theta d| < eps / 2 := by
    have := hB (x := d) ⟨le_of_lt (lt_of_lt_of_le hac hcd), le_of_lt hdb⟩
      (by rw [Real.dist_eq, abs_of_neg (by linarith)]
          have : b - d2 / 2 ≤ d := le_max_left _ _
          linarith)
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this
  have t1 : |theta b - theta a| ≤ |theta b - theta d| + |theta d - theta a| :=
    abs_sub_le _ _ _
  have t2 : |theta d - theta a| ≤ |theta d - theta c| + |theta c - theta a| :=
    abs_sub_le _ _ _
  linarith

/-- **Backlund's bound.**  If the cosine of a continuous function `θ` vanishes at no more than `n`
points of the half-open interval `(a, b]`, then `θ` moves by at most `(n + 1) π` across `[a, b]`.

The proof peels off the least zero `x`: on `[a, x]` the cosine has no interior zero, so `θ` moves
by at most `π` there, and the remaining interval `(x, b]` carries one zero fewer. -/
theorem abs_sub_le_of_ncard_cos_eq_zero {theta : ℝ → ℝ} :
    ∀ (n : ℕ) (a b : ℝ), a ≤ b → ContinuousOn theta (Icc a b) →
      {x ∈ Ioc a b | Real.cos (theta x) = 0}.Finite →
      {x ∈ Ioc a b | Real.cos (theta x) = 0}.ncard ≤ n →
      |theta b - theta a| ≤ (n + 1) * π := by
  intro n
  induction n with
  | zero =>
      intro a b hab hc hfin hcard
      have hempty : {x ∈ Ioc a b | Real.cos (theta x) = 0} = ∅ := by
        rw [← Set.ncard_eq_zero hfin]
        omega
      have h : ∀ t ∈ Ioo a b, Real.cos (theta t) ≠ 0 := by
        intro t ht hcos
        have : t ∈ {x ∈ Ioc a b | Real.cos (theta x) = 0} := ⟨⟨ht.1, ht.2.le⟩, hcos⟩
        rw [hempty] at this
        exact this
      simpa using abs_sub_le_pi_of_forall_cos_ne_zero_Ioo hab hc h
  | succ n ih =>
      intro a b hab hc hfin hcard
      set S := {x ∈ Ioc a b | Real.cos (theta x) = 0} with hS
      by_cases hSempty : S = ∅
      · have h : ∀ t ∈ Ioo a b, Real.cos (theta t) ≠ 0 := by
          intro t ht hcos
          have : t ∈ S := ⟨⟨ht.1, ht.2.le⟩, hcos⟩
          rw [hSempty] at this
          exact this
        have := abs_sub_le_pi_of_forall_cos_ne_zero_Ioo hab hc h
        nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) n]
      -- the least zero
      obtain ⟨x, hxS, hxmin⟩ : ∃ x ∈ S, ∀ y ∈ S, x ≤ y := by
        have hne : S.Nonempty := Set.nonempty_iff_ne_empty.2 hSempty
        obtain ⟨x, hx, hmin⟩ := (hfin.toFinset).exists_min_image id
          (by simpa [Set.Finite.toFinset_nonempty] using hne)
        exact ⟨x, by simpa using hx, fun y hy => by simpa using hmin y (by simpa using hy)⟩
      obtain ⟨⟨hax, hxb⟩, hcosx⟩ := hxS
      -- the piece `[a, x]` has no interior zero
      have hax' : a ≤ x := hax.le
      have h1 : |theta x - theta a| ≤ π := by
        refine abs_sub_le_pi_of_forall_cos_ne_zero_Ioo hax' (hc.mono ?_) ?_
        · exact Icc_subset_Icc le_rfl hxb
        · intro t ht hcos
          have htS : t ∈ S := ⟨⟨ht.1, le_trans ht.2.le hxb⟩, hcos⟩
          exact absurd (hxmin t htS) (not_le.2 ht.2)
      -- the piece `[x, b]` carries one zero fewer
      have hsubS : {y ∈ Ioc x b | Real.cos (theta y) = 0} ⊆ S \ {x} := by
        intro y hy
        refine ⟨⟨⟨lt_trans hax hy.1.1, hy.1.2⟩, hy.2⟩, ?_⟩
        simp only [Set.mem_singleton_iff]
        exact ne_of_gt hy.1.1
      have hfin2 : {y ∈ Ioc x b | Real.cos (theta y) = 0}.Finite :=
        (hfin.diff).subset hsubS
      have hcard2 : {y ∈ Ioc x b | Real.cos (theta y) = 0}.ncard ≤ n := by
        have hdiff : (S \ {x}).ncard + 1 = S.ncard := by
          have := Set.ncard_diff_singleton_add_one (a := x) (s := S)
            ⟨⟨hax, hxb⟩, hcosx⟩ hfin
          simpa using this
        have hle : {y ∈ Ioc x b | Real.cos (theta y) = 0}.ncard ≤ (S \ {x}).ncard :=
          Set.ncard_le_ncard hsubS hfin.diff
        omega
      have h2 : |theta b - theta x| ≤ ((n : ℝ) + 1) * π :=
        ih x b hxb (hc.mono (Icc_subset_Icc hax' le_rfl)) hfin2 hcard2
      have : |theta b - theta a| ≤ |theta b - theta x| + |theta x - theta a| :=
        abs_sub_le _ _ _
      push_cast
      linarith

end RiemannHypothesis
