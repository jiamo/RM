/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.KusminLandau

/-!
# The Kusmin–Landau inequality over a general range

`RiemannHypothesis.KusminLandau` proves the first-derivative test for exponential sums under the
hypothesis that `f'` is monotone **and trapped between two consecutive integers** on the whole
range: `k + λ ≤ f' ≤ k + 1 − λ`.  That hypothesis is what the proof by summation by parts needs,
but it is not what the applications provide: there `f'` is monotone and merely stays at distance
at least `λ` from *every* integer, while sweeping across many integers.  This file removes the
restriction, by splitting the range into the maximal subranges on which `⌊f'⌋` is constant — by
monotonicity of `f'` these are consecutive blocks of integers — and adding up the bounds.

## Main results

* `norm_sum_e2pi_le_of_deriv_block` — the one-block case restated with the separation hypothesis
  `∀ m : ℤ, λ ≤ |f' x − m|` in place of explicit bounds `k + λ ≤ f' ≤ k + 1 − λ`.
* `norm_sum_e2pi_le_of_deriv_floor` — the general monotone case, with the number of blocks written
  exactly: `‖∑_{j ≤ K} e(f (c+j))‖ ≤ (⌊f'(c+K)⌋ − ⌊f'(c)⌋ + 1) (1 + 2/λ)`.
* `norm_sum_e2pi_le_of_deriv_general` — the same bound in terms of the total variation
  `V = |f'(c+K) − f'(c)|` of the derivative, and for `f'` monotone *or* antitone:

      ‖∑_{j ≤ K} e(f (c+j))‖ ≤ (V + 2) (1 + 2/λ).

  This is the classical shape `|∑_{a < n ≤ b} e(f(n))| ≪ (V + 1)/λ` of the first-derivative test
  for sums; only the additive constant in the block count differs.

## Proof

Write `k = ⌊f'(c)⌋` and let `m` be the largest index with `f'(c+m) < k + 1`.  On `[c, c+m]`
monotonicity gives `f'(c) ≤ f' ≤ f'(c+m) < k + 1`, and the separation hypothesis upgrades this to
`k + λ ≤ f' ≤ k + 1 − λ`, so `norm_sum_e2pi_le_of_deriv_sub_int` bounds the block by `1 + 2/λ`.
The remaining range starts at `c + m + 1`, where `⌊f'⌋` has increased by at least one, so strong
induction on the length of the range gives the block count `⌊f'(c+K)⌋ − ⌊f'(c)⌋ + 1`.  Finally
separation makes each floor lose a further `λ`, which turns the count into `V + 2 − 2λ`.

The antitone case follows from the monotone one applied to `−f`, since `e(−θ)` is the conjugate
of `e(θ)` and the two sums have the same norm.
-/

noncomputable section

open Complex Real Finset

namespace RiemannHypothesis

namespace KusminLandau

/-- **One block.**  If `f'` is monotone on `[c, c+K]`, stays at distance at least `λ` from every
integer there, and does not reach `⌊f'(c)⌋ + 1`, then the Kusmin–Landau bound applies with no
further hypothesis. -/
theorem norm_sum_e2pi_le_of_deriv_block {K : ℕ} {lam c : ℝ} {f f' : ℝ → ℝ}
    (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc c (c + K), HasDerivAt f (f' x) x)
    (hsep : ∀ x ∈ Set.Icc c (c + K), ∀ m : ℤ, lam ≤ |f' x - m|)
    (hmono : MonotoneOn f' (Set.Icc c (c + K)))
    (hlt : f' (c + K) < (⌊f' c⌋ : ℝ) + 1) :
    ‖∑ j ∈ Finset.range (K + 1), e2pi (f (c + j))‖ ≤ 1 + 2 / lam := by
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hc : c ∈ Set.Icc c (c + (K : ℝ)) := ⟨le_rfl, by linarith⟩
  have hcK : c + (K : ℝ) ∈ Set.Icc c (c + (K : ℝ)) := ⟨by linarith, le_rfl⟩
  set k : ℤ := ⌊f' c⌋ with hk
  have hfloor : (k : ℝ) ≤ f' c := Int.floor_le _
  have hlbc : (k : ℝ) + lam ≤ f' c := by
    have := hsep c hc k
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ f' c - (k : ℝ))] at this
    linarith
  refine norm_sum_e2pi_le_of_deriv_sub_int (k := k) hlam hf ?_ ?_ (Or.inl hmono)
  · intro x hx
    have : f' c ≤ f' x := hmono hc hx hx.1
    linarith
  · intro x hx
    have hxle : f' x ≤ f' (c + (K : ℝ)) := hmono hx hcK hx.2
    have hsx : lam ≤ |f' x - ((k + 1 : ℤ) : ℝ)| := hsep x hx (k + 1)
    have hneg : f' x - ((k + 1 : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
    rw [abs_of_nonpos hneg] at hsx
    push_cast at hsx
    linarith

/-- **The Kusmin–Landau inequality over a general range**, with the block count written exactly.
`f` is differentiable on `[c, c+K]`, `f'` is monotone there and stays at distance at least `λ`
from every integer; then

`‖∑_{j ≤ K} e(f (c+j))‖ ≤ (⌊f'(c+K)⌋ − ⌊f'(c)⌋ + 1) (1 + 2/λ)`,

the first factor being the number of maximal subranges on which `⌊f'⌋` is constant. -/
theorem norm_sum_e2pi_le_of_deriv_floor {lam : ℝ} (hlam : 0 < lam) (K : ℕ) :
    ∀ (c : ℝ) (f f' : ℝ → ℝ),
      (∀ x ∈ Set.Icc c (c + K), HasDerivAt f (f' x) x) →
      (∀ x ∈ Set.Icc c (c + K), ∀ m : ℤ, lam ≤ |f' x - m|) →
      MonotoneOn f' (Set.Icc c (c + K)) →
      ‖∑ j ∈ Finset.range (K + 1), e2pi (f (c + j))‖
        ≤ ((⌊f' (c + K)⌋ - ⌊f' c⌋ + 1 : ℤ) : ℝ) * (1 + 2 / lam) := by
  classical
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro c f f' hf hsep hmono
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hc : c ∈ Set.Icc c (c + (K : ℝ)) := ⟨le_rfl, by linarith⟩
    have hcK : c + (K : ℝ) ∈ Set.Icc c (c + (K : ℝ)) := ⟨by linarith, le_rfl⟩
    have hpos : (0 : ℝ) < 1 + 2 / lam := by positivity
    set k : ℤ := ⌊f' c⌋ with hk
    -- the floor of `f'` at the right end is at least the floor at the left end
    have hfloor_mono : k ≤ ⌊f' (c + (K : ℝ))⌋ :=
      Int.floor_le_floor (hmono hc hcK (by linarith))
    set P : ℕ → Prop := fun j => f' (c + (j : ℝ)) < (k : ℝ) + 1 with hP
    have hP0 : P 0 := by
      simp [hP, hk, Int.lt_floor_add_one (f' c)]
    set m : ℕ := Nat.findGreatest P K with hm
    have hmK : m ≤ K := Nat.findGreatest_le K
    have hPm : P m := Nat.findGreatest_spec (Nat.zero_le K) hP0
    rcases eq_or_lt_of_le hmK with hmEq | hmLt
    · -- a single block covers the whole range
      have hlt : f' (c + (K : ℝ)) < (k : ℝ) + 1 := by rw [← hmEq]; exact hPm
      have hblock := norm_sum_e2pi_le_of_deriv_block hlam hf hsep hmono hlt
      refine hblock.trans ?_
      have h1 : (1 : ℝ) ≤ ((⌊f' (c + K)⌋ - k + 1 : ℤ) : ℝ) := by
        have : (1 : ℤ) ≤ ⌊f' (c + (K : ℝ))⌋ - k + 1 := by omega
        exact_mod_cast this
      nlinarith
    · -- split off the first block `[c, c+m]` and recurse on `[c + m + 1, c + K]`
      have hmsucc : m + 1 ≤ K := hmLt
      have hnotP : ¬ P (m + 1) := Nat.findGreatest_is_greatest (by omega) hmsucc
      have hge : (k : ℝ) + 1 ≤ f' (c + ((m : ℝ) + 1)) := by
        have := not_lt.mp hnotP
        push_cast at this ⊢
        linarith
      -- the first block
      have hmR : (m : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr hmK
      have hsubm : Set.Icc c (c + (m : ℝ)) ⊆ Set.Icc c (c + (K : ℝ)) := by
        intro x hx
        exact ⟨hx.1, hx.2.trans (by linarith)⟩
      have hblock : ‖∑ j ∈ Finset.range (m + 1), e2pi (f (c + j))‖ ≤ 1 + 2 / lam := by
        refine norm_sum_e2pi_le_of_deriv_block hlam (fun x hx => hf x (hsubm hx))
          (fun x hx => hsep x (hsubm hx)) (fun x hx y hy hxy => hmono (hsubm hx) (hsubm hy) hxy) ?_
        exact hPm
      -- the remaining range
      set c' : ℝ := c + ((m : ℝ) + 1) with hc'
      set K' : ℕ := K - (m + 1) with hK'
      have hK'lt : K' < K := by omega
      have hK'R : (K' : ℝ) = (K : ℝ) - (m : ℝ) - 1 := by
        have hcast : ((K - (m + 1) : ℕ) : ℝ) = (K : ℝ) - ((m : ℝ) + 1) := by
          have := Nat.cast_sub (R := ℝ) hmsucc
          push_cast at this
          linarith [this]
        rw [hK', hcast]; ring
      have hend : c' + (K' : ℝ) = c + (K : ℝ) := by rw [hc', hK'R]; ring
      have hsub' : Set.Icc c' (c' + (K' : ℝ)) ⊆ Set.Icc c (c + (K : ℝ)) := by
        intro x hx
        rw [hend] at hx
        refine ⟨?_, hx.2⟩
        have : c ≤ c' := by
          rw [hc']
          have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith
        exact this.trans hx.1
      have hrec := ih K' hK'lt c' f f' (fun x hx => hf x (hsub' hx))
        (fun x hx => hsep x (hsub' hx))
        (fun x hx y hy hxy => hmono (hsub' hx) (hsub' hy) hxy)
      rw [hend] at hrec
      -- the floor at the start of the remaining range has increased
      have hfloor' : k + 1 ≤ ⌊f' c'⌋ := by
        have : ((k + 1 : ℤ) : ℝ) ≤ f' c' := by rw [hc']; push_cast; linarith
        exact Int.le_floor.mpr this
      -- put the two pieces together
      have hsplit : ∑ j ∈ Finset.range (K + 1), e2pi (f (c + j))
          = (∑ j ∈ Finset.range (m + 1), e2pi (f (c + j)))
            + ∑ i ∈ Finset.range (K' + 1), e2pi (f (c' + i)) := by
        have hKsum : K + 1 = (m + 1) + (K' + 1) := by omega
        rw [hKsum, Finset.sum_range_add]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have harg : c + ((m + 1 + i : ℕ) : ℝ) = c' + (i : ℝ) := by
          rw [hc']; push_cast; ring
        rw [harg]
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add hblock hrec).trans ?_
      have hcount : (1 : ℝ) + ((⌊f' (c + K)⌋ - ⌊f' c'⌋ + 1 : ℤ) : ℝ)
          ≤ ((⌊f' (c + K)⌋ - k + 1 : ℤ) : ℝ) := by
        have : (1 : ℤ) + (⌊f' (c + (K : ℝ))⌋ - ⌊f' c'⌋ + 1) ≤ ⌊f' (c + (K : ℝ))⌋ - k + 1 := by
          omega
        exact_mod_cast this
      nlinarith

/-- **The Kusmin–Landau inequality over a general range**, in terms of the total variation
`V = |f'(c+K) − f'(c)|` of the derivative, for `f'` monotone or antitone:

`‖∑_{j ≤ K} e(f (c+j))‖ ≤ (V + 2) (1 + 2/λ)`.

This is the classical first-derivative test for exponential sums with no restriction on the range
of `f'` beyond staying at distance `λ` from the integers. -/
theorem norm_sum_e2pi_le_of_deriv_general {K : ℕ} {lam c : ℝ} {f f' : ℝ → ℝ}
    (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc c (c + K), HasDerivAt f (f' x) x)
    (hsep : ∀ x ∈ Set.Icc c (c + K), ∀ m : ℤ, lam ≤ |f' x - m|)
    (hmono : MonotoneOn f' (Set.Icc c (c + K)) ∨ AntitoneOn f' (Set.Icc c (c + K))) :
    ‖∑ j ∈ Finset.range (K + 1), e2pi (f (c + j))‖
      ≤ (|f' (c + K) - f' c| + 2) * (1 + 2 / lam) := by
  have hpos : (0 : ℝ) < 1 + 2 / lam := by positivity
  -- the monotone case
  have main : ∀ (g g' : ℝ → ℝ),
      (∀ x ∈ Set.Icc c (c + K), HasDerivAt g (g' x) x) →
      (∀ x ∈ Set.Icc c (c + K), ∀ m : ℤ, lam ≤ |g' x - m|) →
      MonotoneOn g' (Set.Icc c (c + K)) →
      ‖∑ j ∈ Finset.range (K + 1), e2pi (g (c + j))‖
        ≤ (|g' (c + K) - g' c| + 2) * (1 + 2 / lam) := by
    intro g g' hg hsepg hmonog
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hc : c ∈ Set.Icc c (c + (K : ℝ)) := ⟨le_rfl, by linarith⟩
    have hcK : c + (K : ℝ) ∈ Set.Icc c (c + (K : ℝ)) := ⟨by linarith, le_rfl⟩
    have hle : g' c ≤ g' (c + (K : ℝ)) := hmonog hc hcK (by linarith)
    have hbound := norm_sum_e2pi_le_of_deriv_floor hlam K c g g' hg hsepg hmonog
    refine hbound.trans ?_
    -- `⌊b⌋ − ⌊a⌋ + 1 ≤ (b − a) + 2`
    have h1 : ((⌊g' (c + (K : ℝ))⌋ : ℝ)) ≤ g' (c + (K : ℝ)) := Int.floor_le _
    have h2 : g' c - 1 < ((⌊g' c⌋ : ℝ)) := by
      have := Int.lt_floor_add_one (g' c); linarith
    have hcast : ((⌊g' (c + (K : ℝ))⌋ - ⌊g' c⌋ + 1 : ℤ) : ℝ)
        = ((⌊g' (c + (K : ℝ))⌋ : ℝ)) - ((⌊g' c⌋ : ℝ)) + 1 := by push_cast; ring
    have habs : |g' (c + (K : ℝ)) - g' c| = g' (c + (K : ℝ)) - g' c :=
      abs_of_nonneg (by linarith)
    rw [hcast, habs]
    have : ((⌊g' (c + (K : ℝ))⌋ : ℝ)) - ((⌊g' c⌋ : ℝ)) + 1
        ≤ (g' (c + (K : ℝ)) - g' c) + 2 := by linarith
    nlinarith
  rcases hmono with hmo | hanti
  · exact main f f' hf hsep hmo
  · -- replace `f` by `−f`: the sums are complex conjugates of each other
    have hg : ∀ x ∈ Set.Icc c (c + (K : ℝ)), HasDerivAt (fun y => -f y) (-f' x) x :=
      fun x hx => (hf x hx).neg
    have hsepg : ∀ x ∈ Set.Icc c (c + (K : ℝ)), ∀ m : ℤ, lam ≤ |(-f' x) - m| := by
      intro x hx m
      have := hsep x hx (-m)
      calc lam ≤ |f' x - ((-m : ℤ) : ℝ)| := this
        _ = |(-f' x) - ((m : ℤ) : ℝ)| := by rw [← abs_neg]; congr 1; push_cast; ring
    have hmonog : MonotoneOn (fun x => -f' x) (Set.Icc c (c + (K : ℝ))) :=
      fun x hx y hy hxy => neg_le_neg (hanti hx hy hxy)
    have hmain := main (fun y => -f y) (fun x => -f' x) hg hsepg hmonog
    have hnorm : ∀ j : ℕ, e2pi (-f (c + j)) = (starRingEnd ℂ) (e2pi (f (c + j))) := by
      intro j
      simp only [e2pi]
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.ext_iff]
    have hsum : ∑ j ∈ Finset.range (K + 1), e2pi (-f (c + j))
        = (starRingEnd ℂ) (∑ j ∈ Finset.range (K + 1), e2pi (f (c + j))) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hnorm j
    rw [hsum, RCLike.norm_conj] at hmain
    have habs : |(-f' (c + (K : ℝ))) - (-f' c)| = |f' (c + (K : ℝ)) - f' c| := by
      rw [← abs_neg]; congr 1; ring
    rw [habs] at hmain
    exact hmain

end KusminLandau

end RiemannHypothesis
