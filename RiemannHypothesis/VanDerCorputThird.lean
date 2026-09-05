/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.VanDerCorputSums
import RiemannHypothesis.WeylDifferencing
import RiemannHypothesis.WeylQuadratic
import RiemannHypothesis.SqrtHarmonic

/-!
# van der Corput's third-derivative test

`RiemannHypothesis.VanDerCorputSums` proves the *second*-derivative test: if `f'' ≍ r` on a range
of `N` integers then `‖∑ e(f n)‖ ≪ N √r + 1/√r`.  `RiemannHypothesis.WeylDifferencing` proves the
A process, which bounds an exponential sum by the differenced sums `∑ e(f(n+k) − f(n))`.

Combining the two is van der Corput's **third-derivative test**: the differenced phase
`f(· + k) − f(·)` has second derivative `≍ k f'''`, so the second-derivative test applies to it,
and optimizing the number `H` of shifts gives

`‖∑_{n < N} e(f n)‖ ≪ N r^(1/6) + √N r^(-1/6)`  when  `f''' ≍ r`,

the exponent pair `(1/6, 2/3)`.  This is the first estimate in the theory of `ζ` that goes beyond
the convexity bound; with the approximate functional equation it is what produces the subconvexity
exponent `1/6` of Hardy and Littlewood.

## Main results

* `norm_sq_sum_e2pi_le_of_deriv_three` — the test with the number of shifts `H` left free:

      H ‖∑_{n < N} e(f (a + n))‖²
        ≤ (N + H) (N + 8 R N H² + 16 H + 20 R N H √H/√r + 80 √H/√r),

  under `r ≤ f''' ≤ R` on `[a, a + N]`, `0 < r`, `H r ≤ 1` and `H ≤ N`.
The choice of `H` is left to the caller; `RiemannHypothesis.AFESubconvexity` makes it for the
phase of `ζ` on a dyadic block.

Nothing here is claimed about `ζ`: these are estimates for exponential sums with a real phase.
The constants are not optimized.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace VanDerCorputThird

open KusminLandau VanDerCorputSums WeylDifferencing

variable {f f' f'' f''' : ℝ → ℝ} {a r R : ℝ} {N H : ℕ}

/-- Reindexing a sum over the integer interval `(0, H)` as a sum over `Ico 1 H` in `ℕ`. -/
theorem sum_Ioo_int_eq_sum_Ico (H : ℕ) (g : ℤ → ℝ) :
    ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), g k = ∑ k ∈ Finset.Ico 1 H, g (k : ℤ) := by
  refine Finset.sum_nbij' (fun k => k.toNat) (fun k => (k : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Ioo] at hk
    simp only [Finset.mem_Ico]
    omega
  · intro k hk
    simp only [Finset.mem_Ico] at hk
    simp only [Finset.mem_Ioo]
    omega
  · intro k hk
    simp only [Finset.mem_Ioo] at hk
    omega
  · intro k _
    simp
  · intro k hk
    simp only [Finset.mem_Ioo] at hk
    congr 1
    omega

/-- The mean value theorem in the form needed for the differenced phase: if `r ≤ f''' ≤ R` on
`[a, b]` then `f''` increases by between `r (y − x)` and `R (y − x)` between any two points. -/
theorem sub_le_of_deriv_bounds {b : ℝ}
    (hf'' : ∀ x ∈ Set.Icc a b, HasDerivAt f'' (f''' x) x)
    (hlb : ∀ x ∈ Set.Icc a b, r ≤ f''' x) (hub : ∀ x ∈ Set.Icc a b, f''' x ≤ R)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x ≤ y) :
    r * (y - x) ≤ f'' y - f'' x ∧ f'' y - f'' x ≤ R * (y - x) := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  · have hsub : Set.Icc x y ⊆ Set.Icc a b := by
      intro z hz
      rw [Set.mem_Icc] at hz
      exact ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
    obtain ⟨c, hc, hcv⟩ :=
      exists_hasDerivAt_eq_slope f'' f''' hlt
        (fun z hz => ((hf'' z (hsub hz)).continuousAt).continuousWithinAt)
        (fun z hz => hf'' z (hsub (Set.Ioo_subset_Icc_self hz)))
    have hcmem : c ∈ Set.Icc a b := hsub (Set.Ioo_subset_Icc_self hc)
    have hpos : 0 < y - x := by linarith
    have h1 : r ≤ (f'' y - f'' x) / (y - x) := by rw [← hcv]; exact hlb c hcmem
    have h2 : (f'' y - f'' x) / (y - x) ≤ R := by rw [← hcv]; exact hub c hcmem
    rw [le_div_iff₀ hpos] at h1
    rw [div_le_iff₀ hpos] at h2
    exact ⟨by linarith, by linarith⟩

/-- The estimate for one differenced sum: for a shift `k` with `1 ≤ k` and `k r ≤ 1`, the
second-derivative test applied to the phase `f(· + k) − f(·)` gives

`‖∑_{j < L} e(f (a + k + j) − f (a + j))‖ ≤ 2 (k R L + 2) (2 + 5/√(k r))`. -/
theorem norm_sum_e2pi_diff_le {k L : ℕ} (hk : 1 ≤ k) (hLk : L + k ≤ N)
    (hf : ∀ x ∈ Set.Icc a (a + (N : ℝ)), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a (a + (N : ℝ)), HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x ∈ Set.Icc a (a + (N : ℝ)), HasDerivAt f'' (f''' x) x)
    (hr : 0 < r) (hkr : (k : ℝ) * r ≤ 1)
    (hlb : ∀ x ∈ Set.Icc a (a + (N : ℝ)), r ≤ f''' x)
    (hub : ∀ x ∈ Set.Icc a (a + (N : ℝ)), f''' x ≤ R) :
    ‖∑ j ∈ range L, e2pi (f (a + j + k) - f (a + j))‖
      ≤ 2 * ((k : ℝ) * R * L + 2) * (2 + 5 / Real.sqrt ((k : ℝ) * r)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkr0 : 0 < (k : ℝ) * r := by positivity
  have hLN : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_add_right_le hLk
  -- membership transfer: `[a, a+L]` and its translate by `k` sit inside `[a, a+N]`
  have hmem : ∀ x ∈ Set.Icc a (a + (L : ℝ)), x ∈ Set.Icc a (a + (N : ℝ)) := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by linarith)⟩
  have hmemk : ∀ x ∈ Set.Icc a (a + (L : ℝ)), x + (k : ℝ) ∈ Set.Icc a (a + (N : ℝ)) := by
    intro x hx
    have hLkN : (L : ℝ) + (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLk
    exact ⟨by linarith [hx.1, hk0], by linarith [hx.2]⟩
  have hmain := norm_sum_e2pi_le_of_deriv_two (f := fun x => f (x + (k : ℝ)) - f x)
    (g := fun x => f' (x + (k : ℝ)) - f' x) (g' := fun x => f'' (x + (k : ℝ)) - f'' x)
    (a := a) (L := L) (r := (k : ℝ) * r) (R := (k : ℝ) * R) hkr0 hkr
    (fun x hx => ((hf _ (hmemk x hx)).comp_add_const x (k : ℝ)).sub (hf x (hmem x hx)))
    (fun x hx => ((hf' _ (hmemk x hx)).comp_add_const x (k : ℝ)).sub (hf' x (hmem x hx)))
    (fun x hx => by
      have h := (sub_le_of_deriv_bounds hf'' hlb hub (hmem x hx) (hmemk x hx)
        (by linarith [hk0])).1
      have hxx : x + (k : ℝ) - x = (k : ℝ) := by ring
      rw [hxx] at h
      linarith [h])
    (fun x hx => by
      have h := (sub_le_of_deriv_bounds hf'' hlb hub (hmem x hx) (hmemk x hx)
        (by linarith [hk0])).2
      have hxx : x + (k : ℝ) - x = (k : ℝ) := by ring
      rw [hxx] at h
      linarith [h])
  refine le_trans (le_of_eq ?_) hmain
  congr 1

/-- The sum over the shifts of the bounds coming from the second-derivative test. -/
theorem sum_diff_bound_le (H : ℕ) {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) :
    ∑ k ∈ Finset.Ico 1 H, 2 * ((k : ℝ) * A + 2) * (2 + 5 / Real.sqrt ((k : ℝ) * r))
      ≤ 4 * A * (H : ℝ) ^ 2 + 8 * H + 10 * A * H * Real.sqrt H / Real.sqrt r
        + 40 * Real.sqrt H / Real.sqrt r := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hcard : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
    have : (H - 1 : ℕ) ≤ H := by omega
    exact_mod_cast this
  have hcard0 : (0 : ℝ) ≤ ((H - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hterm : ∀ k ∈ Finset.Ico 1 H,
      2 * ((k : ℝ) * A + 2) * (2 + 5 / Real.sqrt ((k : ℝ) * r))
        = 4 * (k : ℝ) * A + 8 + 10 * A * Real.sqrt k / Real.sqrt r
          + 20 / (Real.sqrt k * Real.sqrt r) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    have hsplit : Real.sqrt ((k : ℝ) * r) = Real.sqrt k * Real.sqrt r :=
      Real.sqrt_mul hk0.le r
    have hkk : Real.sqrt k * Real.sqrt k = (k : ℝ) := Real.mul_self_sqrt hk0.le
    rw [hsplit]
    field_simp
    nlinarith [hkk, hsk, hsr, hk0]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have h1 : ∑ k ∈ Finset.Ico 1 H, 4 * (k : ℝ) * A ≤ 4 * A * (H : ℝ) ^ 2 := by
    calc ∑ k ∈ Finset.Ico 1 H, 4 * (k : ℝ) * A
        ≤ ∑ _k ∈ Finset.Ico 1 H, 4 * (H : ℝ) * A := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkH : (k : ℝ) ≤ (H : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hk).2.le
          nlinarith
      _ = ((H - 1 : ℕ) : ℝ) * (4 * (H : ℝ) * A) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ 4 * A * (H : ℝ) ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_right hcard
            (show (0 : ℝ) ≤ 4 * (H : ℝ) * A by positivity)]
  have h2 : ∑ _k ∈ Finset.Ico 1 H, (8 : ℝ) ≤ 8 * H := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    nlinarith
  have h3 : ∑ k ∈ Finset.Ico 1 H, 10 * A * Real.sqrt k / Real.sqrt r
      ≤ 10 * A * H * Real.sqrt H / Real.sqrt r := by
    have hsum : ∑ k ∈ Finset.Ico 1 H, 10 * A * Real.sqrt k / Real.sqrt r
        = (10 * A / Real.sqrt r) * ∑ k ∈ Finset.Ico 1 H, Real.sqrt k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hbound : ∑ k ∈ Finset.Ico 1 H, Real.sqrt k ≤ (H : ℝ) * Real.sqrt H := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_sqrt_le H)
      · intro k hk
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
      · intro k _ _
        exact Real.sqrt_nonneg _
    rw [hsum]
    have hpos : 0 ≤ 10 * A / Real.sqrt r := by positivity
    calc (10 * A / Real.sqrt r) * ∑ k ∈ Finset.Ico 1 H, Real.sqrt k
        ≤ (10 * A / Real.sqrt r) * ((H : ℝ) * Real.sqrt H) :=
          mul_le_mul_of_nonneg_left hbound hpos
      _ = 10 * A * H * Real.sqrt H / Real.sqrt r := by field_simp
  have h4 : ∑ k ∈ Finset.Ico 1 H, 20 / (Real.sqrt k * Real.sqrt r)
      ≤ 40 * Real.sqrt H / Real.sqrt r := by
    have hsum : ∑ k ∈ Finset.Ico 1 H, 20 / (Real.sqrt k * Real.sqrt r)
        = (20 / Real.sqrt r) * ∑ k ∈ Finset.Ico 1 H, 1 / Real.sqrt k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [div_mul_eq_div_div_swap]
        ring
    have hIco : Finset.Ico 1 H = Finset.Icc 1 (H - 1) := by
      rcases Nat.eq_zero_or_pos H with rfl | hH
      · simp
      · ext k
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
    have hbound : ∑ k ∈ Finset.Ico 1 H, 1 / Real.sqrt k ≤ 2 * Real.sqrt H := by
      rw [hIco]
      refine le_trans (sum_one_div_sqrt_le (H - 1)) ?_
      have hle : Real.sqrt ((H - 1 : ℕ) : ℝ) ≤ Real.sqrt H := Real.sqrt_le_sqrt hcard
      linarith
    rw [hsum]
    have hpos : 0 ≤ 20 / Real.sqrt r := by positivity
    calc (20 / Real.sqrt r) * ∑ k ∈ Finset.Ico 1 H, 1 / Real.sqrt k
        ≤ (20 / Real.sqrt r) * (2 * Real.sqrt H) := mul_le_mul_of_nonneg_left hbound hpos
      _ = 40 * Real.sqrt H / Real.sqrt r := by field_simp; ring
  linarith

/-- **van der Corput's third-derivative test**, with the number of shifts `H` left free. -/
theorem norm_sq_sum_e2pi_le_of_deriv_three (hH : 0 < H) (hHN : H ≤ N)
    (hf : ∀ x ∈ Set.Icc a (a + (N : ℝ)), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a (a + (N : ℝ)), HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x ∈ Set.Icc a (a + (N : ℝ)), HasDerivAt f'' (f''' x) x)
    (hr : 0 < r) (hHr : (H : ℝ) * r ≤ 1)
    (hlb : ∀ x ∈ Set.Icc a (a + (N : ℝ)), r ≤ f''' x)
    (hub : ∀ x ∈ Set.Icc a (a + (N : ℝ)), f''' x ≤ R) :
    (H : ℝ) * ‖∑ j ∈ range N, e2pi (f (a + j))‖ ^ 2
      ≤ ((N : ℝ) + H) * ((N : ℝ) + 8 * R * N * H ^ 2 + 16 * H
          + 20 * R * N * H * Real.sqrt H / Real.sqrt r
          + 80 * Real.sqrt H / Real.sqrt r) := by
  classical
  have hN0 : 0 < N := lt_of_lt_of_le hH hHN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have haN : a ∈ Set.Icc a (a + (N : ℝ)) := ⟨le_rfl, by linarith⟩
  have hrR : r ≤ R := le_trans (hlb a haN) (hub a haN)
  have hR0 : 0 < R := lt_of_lt_of_le hr hrR
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  set F : ℤ → ℝ := fun n => f (a + (n : ℝ)) with hFdef
  have hA := WeylDifferencing.norm_sq_sum_e2pi_le F N H hH
  -- the sum over the integer interval is the sum over `range N`
  have hLHS : ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (F n)
      = ∑ j ∈ range N, e2pi (f (a + j)) := by
    rw [WeylQuadratic.sum_Ico_int_eq_sum_range]
    simp [hFdef]
  -- the differenced sums are the ones bounded by the second-derivative test
  have hinner : ∀ k ∈ Finset.Ico 1 H,
      ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - (k : ℤ)), e2pi (F (n + (k : ℤ)) - F n)‖
        ≤ 2 * ((k : ℝ) * (R * (N : ℝ)) + 2) * (2 + 5 / Real.sqrt ((k : ℝ) * r)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkH : k < H := (Finset.mem_Ico.mp hk).2
    have hkN : k ≤ N := le_trans hkH.le hHN
    have hkr : (k : ℝ) * r ≤ 1 := by
      have hkHR : (k : ℝ) ≤ (H : ℝ) := by exact_mod_cast hkH.le
      nlinarith
    have hrewrite : ∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - (k : ℤ)), e2pi (F (n + (k : ℤ)) - F n)
        = ∑ j ∈ range (N - k), e2pi (f (a + j + k) - f (a + j)) := by
      rw [WeylQuadratic.sum_Ico_int_eq_sum_range]
      have htoNat : ((N : ℤ) - (k : ℤ)).toNat = N - k := by omega
      rw [htoNat]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hFdef]
      congr 2
      push_cast
      ring_nf
    rw [hrewrite]
    have hmain := norm_sum_e2pi_diff_le (N := N) (k := k) (L := N - k) hk1
      (by omega) hf hf' hf'' hr hkr hlb hub
    refine hmain.trans ?_
    have hfac : (0 : ℝ) < 2 + 5 / Real.sqrt ((k : ℝ) * r) := by
      have : 0 < Real.sqrt ((k : ℝ) * r) := by
        refine Real.sqrt_pos.mpr ?_
        have : (0 : ℝ) < k := by exact_mod_cast hk1
        positivity
      positivity
    have hle : (k : ℝ) * R * ((N - k : ℕ) : ℝ) + 2 ≤ (k : ℝ) * (R * (N : ℝ)) + 2 := by
      have hNk : ((N - k : ℕ) : ℝ) ≤ (N : ℝ) := by
        have : (N - k : ℕ) ≤ N := by omega
        exact_mod_cast this
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [mul_le_mul_of_nonneg_left hNk (mul_nonneg hk0 hR0.le)]
    have h2 : 2 * ((k : ℝ) * R * ((N - k : ℕ) : ℝ) + 2) ≤ 2 * ((k : ℝ) * (R * (N : ℝ)) + 2) := by
      linarith
    exact mul_le_mul_of_nonneg_right h2 hfac.le
  -- assemble
  rw [hLHS] at hA
  rw [sum_Ioo_int_eq_sum_Ico H
    (fun k => ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k), e2pi (F (n + k) - F n)‖)] at hA
  have hsum : ∑ k ∈ Finset.Ico 1 H,
      ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - (k : ℤ)), e2pi (F (n + (k : ℤ)) - F n)‖
      ≤ 4 * (R * (N : ℝ)) * (H : ℝ) ^ 2 + 8 * H
        + 10 * (R * (N : ℝ)) * H * Real.sqrt H / Real.sqrt r
        + 40 * Real.sqrt H / Real.sqrt r :=
    le_trans (Finset.sum_le_sum hinner) (sum_diff_bound_le H (by positivity) hr)
  have hsum0 : 0 ≤ ∑ k ∈ Finset.Ico 1 H,
      ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - (k : ℤ)), e2pi (F (n + (k : ℤ)) - F n)‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  refine hA.trans ?_
  have hfactor : (N : ℝ) + H - 1 ≤ (N : ℝ) + H := by linarith
  have hinner2 : (N : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H,
      ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - (k : ℤ)), e2pi (F (n + (k : ℤ)) - F n)‖
      ≤ (N : ℝ) + 8 * R * N * H ^ 2 + 16 * H
        + 20 * R * N * H * Real.sqrt H / Real.sqrt r + 80 * Real.sqrt H / Real.sqrt r := by
    simp only [div_eq_mul_inv] at hsum ⊢
    linarith
  have hnn : (0 : ℝ) ≤ (N : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H,
      ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - (k : ℤ)), e2pi (F (n + (k : ℤ)) - F n)‖ := by
    linarith
  calc ((N : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H,
          ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - (k : ℤ)), e2pi (F (n + (k : ℤ)) - F n)‖)
      ≤ ((N : ℝ) + H) * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H,
          ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - (k : ℤ)), e2pi (F (n + (k : ℤ)) - F n)‖) :=
        mul_le_mul_of_nonneg_right hfactor hnn
    _ ≤ ((N : ℝ) + H) * ((N : ℝ) + 8 * R * N * H ^ 2 + 16 * H
          + 20 * R * N * H * Real.sqrt H / Real.sqrt r + 80 * Real.sqrt H / Real.sqrt r) :=
        mul_le_mul_of_nonneg_left hinner2 (by linarith)

end VanDerCorputThird

end RiemannHypothesis
