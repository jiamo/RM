/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.KoksmaSharp

/-!
# The van der Corput sequence: an explicit sequence of low discrepancy

Every module of this repository that bounds a discrepancy so far bounds it *from above by
something that tends to zero slowly*: the Erdős–Turán route of `RiemannHypothesis.Discrepancy`
gives `D_N(α n) ≤ 2 (20 + 2/c) N^(−1/9)` for badly approximable `α`, and nothing in the
repository exhibits a sequence whose discrepancy decays at the optimal logarithmic rate.  This
module supplies one, unconditionally and with explicit constants: the **van der Corput
sequence**, the base-two radical inverse

    vdc n = 0.b₀b₁b₂…  (binary)   for   n = …b₂b₁b₀  (binary),

satisfies

    D_N(vdc) ≤ 2 (log₂ N + 1) / N   (`discrepancy_vdc_le`),

for every `N ≥ 1`, where `log₂ N + 1` is `Nat.size N`.  In particular `D_N(vdc) → 0`
(`tendsto_discrepancy_vdc`), so by the Koksma inequalities of `RiemannHypothesis.KoksmaSharp`
and `RiemannHypothesis.KoksmaVariation` the averages `(1/N) ∑_{n<N} f(vdc n)` converge to
`∫₀¹ f` for every function of bounded variation, with the *quantitative* error bound
`L · 2 (log₂ N + 1) / N` for `L`-Lipschitz `f` (`koksma_vdc_lipschitz`).

## Main definitions

* `vdc` — the van der Corput sequence, defined by the recursion `vdc n = (n % 2 + vdc (n / 2))/2`.
* `revBits j n` — the natural number whose binary digits are the lowest `j` digits of `n`,
  reversed; the index of the dyadic cell of length `2^(-j)` containing `vdc n`.

## Main results

* `vdc_nonneg`, `vdc_lt_one` — the sequence lives in `[0, 1)`, so `Int.fract (vdc n) = vdc n`.
* `vdc_split` — `vdc n = (revBits j n + vdc (n / 2^j)) / 2^j`: the first `j` binary digits of
  `vdc n` are the lowest `j` digits of `n`, reversed.
* `image_revBits_block` — on any block of `2^j` *consecutive* indices the cell index
  `revBits j` is a bijection onto `{0, …, 2^j − 1}`: each dyadic cell of length `2^(-j)`
  receives exactly one point.
* `abs_blockCount_sub_le_one` — hence the counting error of any initial segment `[0, x)` over
  such a block is at most `1`.
* `abs_count_sub_le_size` — splitting `{a, …, a + N − 1}` into the blocks given by the binary
  digits of `N` gives `|#{n ∈ [a, a+N) : vdc n < x} − N x| ≤ Nat.size N`.
* `discrepancy_vdc_le` — `D_N(vdc) ≤ 2 · Nat.size N / N`.
* `abs_countIn_vdc_div_sub_le` — the counting form: every `[a, b) ⊆ [0, 1]` receives its share to
  within `2 (log₂ N + 1)/N`.
* `abs_countIn_zero_sub_le_size` — the star form, with the constant `1` in place of `2`.
* `one_div_two_mul_le_discrepancy` — for *every* sequence, `D_N ≥ 1/(2N)`: among the `2N` cells
  of length `1/(2N)` the first `N` points must miss one.
* `discrepancy_vdc_bounds` — hence `1/(2N) ≤ D_N(vdc) ≤ 2 (log₂ N + 1)/N`: the rate proved here
  is optimal up to the logarithm.
* `tendsto_discrepancy_vdc` — `D_N(vdc) → 0`.
* `koksma_vdc_lipschitz`, `koksma_vdc_variation`, `tendsto_average_vdc_variation` — the
  quadrature consequences.

The declarations live in the namespace `RiemannHypothesis.VanDerCorput`, shared with
`RiemannHypothesis/VanDerCorput.lean` — the derivative tests for exponential integrals are due
to the same author; the names do not collide.

## Scope

The bound `2 (log₂ N + 1)/N` is of the optimal order.  What is proved here in that direction is
only the trivial lower bound `D_N ≥ 1/(2N)` (`one_div_two_mul_le_discrepancy`), which leaves a
factor `log N`; the sharp statement, that `N · D_N` is unbounded for every sequence (Schmidt's
theorem), is *not* proved here.  The constant `2` comes from writing an
interval `[a, b)` as a difference of two initial segments and is not optimised; the star
discrepancy version proved on the way (`abs_count_sub_le_size` with `a = 0`) carries the
constant `1`.  Nothing here concerns `ζ`.
-/

noncomputable section

open Filter Topology

namespace RiemannHypothesis

namespace VanDerCorput

open WeylCount WeylDiscrepancy

/-! ### The sequence -/

/-- **The van der Corput sequence** in base two: `vdc n` is the real number in `[0, 1)` whose
binary digits are those of `n`, reversed. -/
def vdc : ℕ → ℝ
  | 0 => 0
  | (n + 1) => ((((n + 1) % 2 : ℕ) : ℝ) + vdc ((n + 1) / 2)) / 2
decreasing_by omega

/-- The defining recursion, in a form valid at `0` as well. -/
theorem vdc_eq (n : ℕ) : vdc n = (((n % 2 : ℕ) : ℝ) + vdc (n / 2)) / 2 := by
  cases n with
  | zero => simp [vdc]
  | succ m => rw [vdc]

theorem vdc_nonneg (n : ℕ) : 0 ≤ vdc n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [vdc]
    · have h : n / 2 < n := Nat.div_lt_self hn (by norm_num)
      have := ih _ h
      rw [vdc_eq]
      positivity

theorem vdc_lt_one (n : ℕ) : vdc n < 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [vdc]
    · have h : n / 2 < n := Nat.div_lt_self hn (by norm_num)
      have h1 := ih _ h
      have h2 : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
        have : n % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
        exact_mod_cast this
      rw [vdc_eq]
      linarith

/-- The sequence takes its values in `[0, 1)`, so taking fractional parts changes nothing. -/
@[simp]
theorem fract_vdc (n : ℕ) : Int.fract (vdc n) = vdc n :=
  Int.fract_eq_self.2 ⟨vdc_nonneg n, vdc_lt_one n⟩

/-! ### The first few values

The sequence begins `0, 1/2, 1/4, 3/4, 1/8, 5/8, 3/8, 7/8`, which is the classical van der
Corput sequence: the definition is not a vacuous one. -/

@[simp]
theorem vdc_zero : vdc 0 = 0 := by simp [vdc]

theorem vdc_one : vdc 1 = 1 / 2 := by rw [vdc_eq]; norm_num

theorem vdc_two : vdc 2 = 1 / 4 := by rw [vdc_eq]; norm_num [vdc_one]

theorem vdc_three : vdc 3 = 3 / 4 := by rw [vdc_eq]; norm_num [vdc_one]

theorem vdc_four : vdc 4 = 1 / 8 := by rw [vdc_eq]; norm_num [vdc_two]

theorem vdc_five : vdc 5 = 5 / 8 := by rw [vdc_eq]; norm_num [vdc_two]

theorem vdc_six : vdc 6 = 3 / 8 := by rw [vdc_eq]; norm_num [vdc_three]

theorem vdc_seven : vdc 7 = 7 / 8 := by rw [vdc_eq]; norm_num [vdc_three]

/-! ### The dyadic cell of a point -/

/-- `revBits j n` is the number whose binary digits are the lowest `j` digits of `n`, reversed;
equivalently, the index of the dyadic cell `[k/2^j, (k+1)/2^j)` containing `vdc n`. -/
def revBits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (j + 1), n => n % 2 * 2 ^ j + revBits j (n / 2)

theorem revBits_lt (j n : ℕ) : revBits j n < 2 ^ j := by
  induction j generalizing n with
  | zero => simp [revBits]
  | succ j ih =>
      have h := ih (n / 2)
      have h2 : n % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
      simp only [revBits, pow_succ]
      nlinarith [Nat.one_le_two_pow (n := j)]

/-- The digits of `vdc n` split at position `j`: the first `j` are the lowest `j` digits of `n`
reversed, and the rest are the digits of `vdc (n / 2^j)`. -/
theorem vdc_split (j n : ℕ) : vdc n = ((revBits j n : ℝ) + vdc (n / 2 ^ j)) / 2 ^ j := by
  induction j generalizing n with
  | zero => simp [revBits]
  | succ j ih =>
      rw [vdc_eq n, ih (n / 2)]
      have hdiv : n / 2 / 2 ^ j = n / 2 ^ (j + 1) := by
        rw [Nat.div_div_eq_div_mul]; ring_nf
      rw [hdiv]
      simp only [revBits]
      push_cast
      field_simp
      ring

/-- `vdc n` lies in the dyadic cell of length `2^(-j)` indexed by `revBits j n`. -/
theorem vdc_mem_cell (j n : ℕ) :
    (revBits j n : ℝ) / 2 ^ j ≤ vdc n ∧ vdc n < ((revBits j n : ℝ) + 1) / 2 ^ j := by
  have h := vdc_split j n
  have h0 := vdc_nonneg (n / 2 ^ j)
  have h1 := vdc_lt_one (n / 2 ^ j)
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  rw [h]
  constructor
  · gcongr; linarith
  · gcongr

/-! ### One point in each cell, on each block of `2^j` consecutive indices -/

theorem mod_two_mul (b n : ℕ) : n % (2 * b) = 2 * ((n / 2) % b) + n % 2 := by
  have h1 : (n % (2 * b)) / 2 = (n / 2) % b := Nat.mod_mul_right_div_self n 2 b
  have h2 : (n % (2 * b)) % 2 = n % 2 := Nat.mod_mul_right_mod n 2 b
  omega

/-- The cell index determines the index modulo `2^j`. -/
theorem revBits_inj_mod {j n m : ℕ} (h : revBits j n = revBits j m) : n % 2 ^ j = m % 2 ^ j := by
  induction j generalizing n m with
  | zero => simp [Nat.mod_one]
  | succ j ih =>
      simp only [revBits] at h
      have hn := revBits_lt j (n / 2)
      have hm := revBits_lt j (m / 2)
      have hpar : n % 2 = m % 2 := by
        rcases Nat.mod_two_eq_zero_or_one n with h1 | h1 <;>
          rcases Nat.mod_two_eq_zero_or_one m with h2 | h2 <;>
          rw [h1, h2] at h ⊢ <;> simp at h ⊢ <;> omega
      rw [hpar] at h
      have hrev : revBits j (n / 2) = revBits j (m / 2) := by omega
      have hmod := ih hrev
      have hh : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [hh, mod_two_mul, mod_two_mul, hmod, hpar]

theorem revBits_injOn (j a : ℕ) : Set.InjOn (revBits j) ↑(Finset.Ico a (a + 2 ^ j)) := by
  intro n hn m hm h
  simp only [Finset.coe_Ico, Set.mem_Ico] at hn hm
  have hmod := revBits_inj_mod h
  rcases le_total n m with hnm | hnm
  · have hd : 2 ^ j ∣ (m - n) := (Nat.modEq_iff_dvd' hnm).mp hmod
    rcases Nat.eq_zero_or_pos (m - n) with h0 | h0
    · omega
    · exact absurd (Nat.le_of_dvd h0 hd) (by omega)
  · have hd : 2 ^ j ∣ (n - m) := (Nat.modEq_iff_dvd' hnm).mp hmod.symm
    rcases Nat.eq_zero_or_pos (n - m) with h0 | h0
    · omega
    · exact absurd (Nat.le_of_dvd h0 hd) (by omega)

/-- **Each dyadic cell of length `2^(-j)` receives exactly one of any `2^j` consecutive points.**
-/
theorem image_revBits_block (j a : ℕ) :
    Finset.image (revBits j) (Finset.Ico a (a + 2 ^ j)) = Finset.range (2 ^ j) := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    simp only [Finset.mem_image] at hk
    obtain ⟨n, -, rfl⟩ := hk
    exact Finset.mem_range.2 (revBits_lt j n)
  · rw [Finset.card_range, Finset.card_image_of_injOn (revBits_injOn j a)]
    simp

/-! ### The counting error -/

/-- The number of indices `n` in the block `[a, a + N)` with `vdc n < x`. -/
def countLt (x : ℝ) (a N : ℕ) : ℕ :=
  ((Finset.Ico a (a + N)).filter fun n => vdc n < x).card

theorem card_floor_le (M : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hyM : y ≤ M) :
    (y - 1 : ℝ) ≤ (((Finset.range M).filter fun k : ℕ => (k : ℝ) + 1 ≤ y).card : ℝ) := by
  have ht : (⌊y⌋₊ : ℕ) ≤ M := (Nat.floor_le_of_le hyM).trans (by simp)
  have hsub : Finset.range ⌊y⌋₊ ⊆ (Finset.range M).filter fun k : ℕ => (k : ℝ) + 1 ≤ y := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨lt_of_lt_of_le hk ht, ?_⟩
    have h : (k : ℝ) + 1 ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hk
    exact h.trans (Nat.floor_le hy0)
  have hcard := Finset.card_le_card hsub
  have h1 : y - 1 < (⌊y⌋₊ : ℝ) := Nat.sub_one_lt_floor y
  have h2 : ((⌊y⌋₊ : ℕ) : ℝ)
      ≤ (((Finset.range M).filter fun k : ℕ => (k : ℝ) + 1 ≤ y).card : ℝ) := by
    exact_mod_cast (by simpa using hcard)
  linarith

theorem card_ceil_le (M : ℕ) {y : ℝ} (hy0 : 0 ≤ y) :
    ((((Finset.range M).filter fun k : ℕ => (k : ℝ) < y).card : ℝ)) ≤ y + 1 := by
  have hsub : ((Finset.range M).filter fun k : ℕ => (k : ℝ) < y) ⊆ Finset.range ⌈y⌉₊ := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact Nat.lt_ceil.2 hk.2
  have hcard := Finset.card_le_card hsub
  have h1 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have h2 : ((((Finset.range M).filter fun k : ℕ => (k : ℝ) < y).card : ℕ) : ℝ) ≤ (⌈y⌉₊ : ℝ) := by
    exact_mod_cast (by simpa using hcard)
  linarith

/-- **The counting error over a block of `2^j` consecutive indices is at most one.** -/
theorem abs_blockCount_sub_le_one (j a : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(countLt x a (2 ^ j) : ℝ) - 2 ^ j * x| ≤ 1 := by
  classical
  set B := (Finset.Ico a (a + 2 ^ j)).filter (fun n => vdc n < x) with hB
  set y : ℝ := 2 ^ j * x with hy
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hyM : y ≤ ((2 ^ j : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hBsub : (B : Set ℕ) ⊆ ↑(Finset.Ico a (a + 2 ^ j)) := by
    intro n hn
    have hn' : n ∈ B := hn
    simp only [hB, Finset.mem_filter] at hn'
    exact_mod_cast hn'.1
  have hinj : Set.InjOn (revBits j) ↑B := (revBits_injOn j a).mono hBsub
  have hcard : (B.image (revBits j)).card = B.card := Finset.card_image_of_injOn hinj
  have hup : B.image (revBits j) ⊆ (Finset.range (2 ^ j)).filter fun k : ℕ => (k : ℝ) < y := by
    intro k hk
    simp only [Finset.mem_image] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    simp only [hB, Finset.mem_filter] at hn
    have hcell := (vdc_mem_cell j n).1
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨revBits_lt j n, ?_⟩
    have : (revBits j n : ℝ) / 2 ^ j < x := lt_of_le_of_lt hcell hn.2
    rw [div_lt_iff₀ hpow] at this
    rw [hy]
    linarith
  have hlow : ((Finset.range (2 ^ j)).filter fun k : ℕ => (k : ℝ) + 1 ≤ y)
      ⊆ B.image (revBits j) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    have hmem : k ∈ Finset.image (revBits j) (Finset.Ico a (a + 2 ^ j)) := by
      rw [image_revBits_block]
      exact Finset.mem_range.2 hk.1
    simp only [Finset.mem_image] at hmem
    obtain ⟨n, hn, hnk⟩ := hmem
    have hcell := (vdc_mem_cell j n).2
    have hlt : vdc n < x := by
      have hle : ((revBits j n : ℝ) + 1) / 2 ^ j ≤ x := by
        rw [div_le_iff₀ hpow, hnk]
        rw [hy] at hk
        linarith [hk.2]
      exact lt_of_lt_of_le hcell hle
    exact Finset.mem_image.2 ⟨n, by simp only [hB, Finset.mem_filter]; exact ⟨hn, hlt⟩, hnk⟩
  have hupc : (B.card : ℝ) ≤ y + 1 := by
    have := Finset.card_le_card hup
    rw [hcard] at this
    have hcast : (B.card : ℝ)
        ≤ (((Finset.range (2 ^ j)).filter fun k : ℕ => (k : ℝ) < y).card : ℝ) := by
      exact_mod_cast this
    exact hcast.trans (card_ceil_le _ hy0)
  have hlowc : y - 1 ≤ (B.card : ℝ) := by
    have := Finset.card_le_card hlow
    rw [hcard] at this
    have hcast : ((((Finset.range (2 ^ j)).filter fun k : ℕ => (k : ℝ) + 1 ≤ y).card : ℕ) : ℝ)
        ≤ (B.card : ℝ) := by
      exact_mod_cast this
    exact (card_floor_le _ hy0 hyM).trans hcast
  have hcountB : countLt x a (2 ^ j) = B.card := rfl
  rw [hcountB, abs_le]
  constructor <;> linarith

/-- **The counting error over any block of `N` consecutive indices is at most `log₂ N + 1`.** -/
theorem abs_count_sub_le_size (a N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(countLt x a N : ℝ) - N * x| ≤ Nat.size N := by
  classical
  induction N using Nat.strong_induction_on generalizing a with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [countLt]
    · set j := Nat.size N - 1 with hj
      have hsize : 0 < Nat.size N := Nat.size_pos.2 hN
      have hjs : j < Nat.size N := by omega
      have h1 : 2 ^ j ≤ N := Nat.lt_size.1 hjs
      have h2 : N < 2 ^ (j + 1) := by
        have : Nat.size N ≤ j + 1 := by omega
        exact Nat.size_le.1 this
      have hpow : 0 < 2 ^ j := Nat.two_pow_pos j
      set N' := N - 2 ^ j with hN'
      have hN'lt : N' < 2 ^ j := by
        have : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
        omega
      have hN'N : N' < N := by omega
      have hsplit : countLt x a N = countLt x a (2 ^ j) + countLt x (a + 2 ^ j) N' := by
        have hun : Finset.Ico a (a + 2 ^ j) ∪ Finset.Ico (a + 2 ^ j) (a + N)
            = Finset.Ico a (a + N) :=
          Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)
        have hdisj : Disjoint ((Finset.Ico a (a + 2 ^ j)).filter fun n => vdc n < x)
            ((Finset.Ico (a + 2 ^ j) (a + N)).filter fun n => vdc n < x) := by
          refine Finset.disjoint_filter_filter ?_
          rw [Finset.disjoint_left]
          intro n hn hn'
          simp only [Finset.mem_Ico] at hn hn'
          omega
        have heq : a + 2 ^ j + N' = a + N := by omega
        simp only [countLt, heq]
        rw [← hun, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
      have hb1 := abs_blockCount_sub_le_one j a hx0 hx1
      have hb2 := ih N' hN'N (a + 2 ^ j)
      have hcastN : (N : ℝ) = (2 ^ j : ℕ) + (N' : ℕ) := by
        push_cast
        have : ((N' : ℕ) : ℝ) = (N : ℝ) - (2 ^ j : ℕ) := by
          have : (2 ^ j : ℕ) ≤ N := h1
          push_cast [hN']
          rw [Nat.cast_sub this]
          push_cast
          ring
        push_cast at this ⊢
        linarith
      have hsizeN' : Nat.size N' ≤ j := Nat.size_le.2 hN'lt
      have hsizecast : (Nat.size N' : ℝ) + 1 ≤ Nat.size N := by
        have : (Nat.size N' : ℕ) + 1 ≤ Nat.size N := by omega
        exact_mod_cast this
      have hcount : (countLt x a N : ℝ)
          = (countLt x a (2 ^ j) : ℝ) + (countLt x (a + 2 ^ j) N' : ℝ) := by
        rw [hsplit]; push_cast; ring
      have hpowcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
      rw [hcount]
      have hkey : (countLt x a (2 ^ j) : ℝ) + (countLt x (a + 2 ^ j) N' : ℝ) - N * x
          = ((countLt x a (2 ^ j) : ℝ) - 2 ^ j * x)
            + ((countLt x (a + 2 ^ j) N' : ℝ) - (N' : ℕ) * x) := by
        rw [hcastN, hpowcast]; ring
      rw [hkey]
      calc |((countLt x a (2 ^ j) : ℝ) - 2 ^ j * x)
              + ((countLt x (a + 2 ^ j) N' : ℝ) - (N' : ℕ) * x)|
          ≤ |(countLt x a (2 ^ j) : ℝ) - 2 ^ j * x|
              + |(countLt x (a + 2 ^ j) N' : ℝ) - (N' : ℕ) * x| := abs_add_le _ _
        _ ≤ 1 + Nat.size N' := add_le_add hb1 hb2
        _ ≤ Nat.size N := by linarith

/-! ### The discrepancy of the van der Corput sequence -/

theorem countIn_vdc_eq (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    (countIn vdc a b N : ℝ) = (countLt b 0 N : ℝ) - (countLt a 0 N : ℝ) := by
  classical
  have h0 : (0 : ℕ) + N = N := by omega
  have hsub : ((Finset.range N).filter fun n => vdc n < a)
      ⊆ ((Finset.range N).filter fun n => vdc n < b) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, lt_of_lt_of_le hn.2 hab⟩
  have hset : ((Finset.range N).filter fun n => a ≤ Int.fract (vdc n) ∧ Int.fract (vdc n) < b)
      = ((Finset.range N).filter fun n => vdc n < b)
        \ ((Finset.range N).filter fun n => vdc n < a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, fract_vdc, not_and, not_lt]
    constructor
    · rintro ⟨hn, h1, h2⟩
      exact ⟨⟨hn, h2⟩, fun _ => h1⟩
    · rintro ⟨⟨hn, h2⟩, h1⟩
      exact ⟨hn, h1 hn, h2⟩
  have hcards := Finset.card_le_card hsub
  simp only [countIn, countLt, h0, Nat.Ico_zero_eq_range]
  rw [hset, Finset.card_sdiff_of_subset hsub, Nat.cast_sub hcards]

/-- **The van der Corput sequence has discrepancy at most `2 (log₂ N + 1)/N`.** -/
theorem discrepancy_vdc_le {N : ℕ} (hN : 0 < N) :
    discrepancy vdc N ≤ 2 * Nat.size N / N := by
  refine discrepancy_le_of_forall vdc fun a b ha hab hb => ?_
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := abs_count_sub_le_size 0 N (x := b) (le_trans ha hab) hb
  have h2 := abs_count_sub_le_size 0 N (x := a) ha (le_trans hab hb)
  have hkey : |(countIn vdc a b N : ℝ) - N * (b - a)| ≤ 2 * Nat.size N := by
    rw [countIn_vdc_eq a b hab N]
    have hrw : (countLt b 0 N : ℝ) - (countLt a 0 N : ℝ) - N * (b - a)
        = ((countLt b 0 N : ℝ) - N * b) + (-((countLt a 0 N : ℝ) - N * a)) := by ring
    rw [hrw]
    calc |((countLt b 0 N : ℝ) - N * b) + (-((countLt a 0 N : ℝ) - N * a))|
        ≤ |(countLt b 0 N : ℝ) - N * b| + |-((countLt a 0 N : ℝ) - N * a)| := abs_add_le _ _
      _ = |(countLt b 0 N : ℝ) - N * b| + |(countLt a 0 N : ℝ) - N * a| := by rw [abs_neg]
      _ ≤ Nat.size N + Nat.size N := add_le_add h1 h2
      _ = 2 * Nat.size N := by ring
  have hrw2 : (countIn vdc a b N : ℝ) / N - (b - a)
      = ((countIn vdc a b N : ℝ) - N * (b - a)) / N := by
    field_simp
  rw [hrw2, abs_div, abs_of_pos hNR]
  gcongr

/-- An elementary bound used to turn `Nat.size N ≤ log₂ N + 1` into a rate: `k² ≤ 4 · 2^k`. -/
theorem sq_le_four_mul_two_pow (k : ℕ) : k ^ 2 ≤ 4 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hk : k < 2 ^ k := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      nlinarith [ih, hk]

theorem tendsto_size_atTop : Tendsto (fun N : ℕ => (Nat.size N : ℝ)) atTop atTop := by
  refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun a ha => ?_⟩)
  exact le_of_lt (Nat.lt_size.2 ha)

/-- **The star form, with the constant `1`**: the counting error of an initial segment `[0, x)`
is at most `log₂ N + 1`, without the factor `2` of `discrepancy_vdc_le`. -/
theorem abs_countIn_zero_sub_le_size {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {N : ℕ} (hN : 0 < N) :
    |(countIn vdc 0 x N : ℝ) / N - x| ≤ Nat.size N / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcount : (countIn vdc 0 x N : ℝ) = (countLt x 0 N : ℝ) := by
    have h := countIn_vdc_eq 0 x hx0 N
    have hzero : countLt (0 : ℝ) 0 N = 0 := by
      classical
      simp only [countLt, Finset.card_eq_zero]
      refine Finset.filter_false_of_mem fun n _ => ?_
      exact not_lt.2 (vdc_nonneg n)
    rw [h, hzero]
    simp
  rw [hcount]
  have hrw : (countLt x 0 N : ℝ) / N - x = ((countLt x 0 N : ℝ) - N * x) / N := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hNR]
  gcongr
  exact abs_count_sub_le_size 0 N hx0 hx1

/-- The counting form, with an explicit rate: every subinterval `[a, b)` of `[0, 1]` receives its
share of the first `N` van der Corput points to within `2 (log₂ N + 1)/N`. -/
theorem abs_countIn_vdc_div_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {N : ℕ}
    (hN : 0 < N) :
    |(countIn vdc a b N : ℝ) / N - (b - a)| ≤ 2 * Nat.size N / N :=
  (le_discrepancy vdc ha hab hb N).trans (discrepancy_vdc_le hN)

/-! ### A lower bound for the discrepancy of an arbitrary sequence -/

/-- **No sequence has discrepancy below `1/(2N)`**: among the `2N` cells of length `1/(2N)` the
first `N` points miss one, and that cell witnesses a deviation `1/(2N)`.  (The optimal lower
bound, of order `log N / N`, is Schmidt's theorem and is not proved here.) -/
theorem one_div_two_mul_le_discrepancy (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    1 / (2 * N) ≤ discrepancy x N := by
  classical
  set M : ℕ := 2 * N with hM
  have hM0 : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  set g : ℕ → ℕ := fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ with hg
  obtain ⟨k, hkM, hk⟩ : ∃ k ∈ Finset.range M, k ∉ Finset.image g (Finset.range N) := by
    have h2 := Finset.card_image_le (s := Finset.range N) (f := g)
    have hlt : (Finset.image g (Finset.range N)).card < (Finset.range M).card := by
      simp only [Finset.card_range] at h2 ⊢
      omega
    exact Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_range] at hkM
  have hka : (0 : ℝ) ≤ (k : ℝ) / M := by positivity
  have hkb : ((k : ℝ) + 1) / M ≤ 1 := by
    rw [div_le_one hMR]
    have : (k : ℝ) + 1 ≤ M := by exact_mod_cast hkM
    linarith
  have hab : (k : ℝ) / M ≤ ((k : ℝ) + 1) / M := by gcongr; linarith
  have hcount : countIn x ((k : ℝ) / M) (((k : ℝ) + 1) / M) N = 0 := by
    simp only [countIn, Finset.card_eq_zero]
    refine Finset.filter_false_of_mem fun n hn => ?_
    rintro ⟨h1, h2⟩
    refine hk (Finset.mem_image.2 ⟨n, hn, ?_⟩)
    have h1' : (k : ℝ) ≤ (M : ℝ) * Int.fract (x n) := by
      rw [div_le_iff₀ hMR] at h1
      linarith
    have h2' : (M : ℝ) * Int.fract (x n) < (k : ℝ) + 1 := by
      rw [lt_div_iff₀ hMR] at h2
      linarith
    simp only [hg]
    have : ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k := by
      refine Nat.floor_eq_iff (by positivity) |>.2 ⟨h1', ?_⟩
      exact_mod_cast h2'
    exact this
  have hle := le_discrepancy x hka hab hkb N
  rw [hcount] at hle
  have hdiff : ((k : ℝ) + 1) / M - (k : ℝ) / M = 1 / M := by
    field_simp
    ring
  rw [hdiff] at hle
  simpa [hM, abs_of_nonneg, hMR.le] using hle

/-- The rate of `discrepancy_vdc_le` is optimal up to the logarithm: for every `N ≥ 1`,
`1/(2N) ≤ D_N(vdc) ≤ 2 (log₂ N + 1)/N`. -/
theorem discrepancy_vdc_bounds {N : ℕ} (hN : 0 < N) :
    1 / (2 * N) ≤ discrepancy vdc N ∧ discrepancy vdc N ≤ 2 * Nat.size N / N :=
  ⟨one_div_two_mul_le_discrepancy vdc hN, discrepancy_vdc_le hN⟩

/-- `Nat.size N / N → 0`: the bound of `discrepancy_vdc_le` tends to zero. -/
theorem tendsto_size_div_atTop : Tendsto (fun N : ℕ => (Nat.size N : ℝ) / N) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => 8 / (Nat.size N : ℝ)) atTop (𝓝 0) :=
    tendsto_size_atTop.const_div_atTop 8
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => by positivity) ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  have hsize : 0 < Nat.size N := Nat.size_pos.2 hN
  have hpow : 2 ^ (Nat.size N - 1) ≤ N := Nat.lt_size.1 (by omega)
  have hsq : (Nat.size N) ^ 2 ≤ 8 * N := by
    have h4 := sq_le_four_mul_two_pow (Nat.size N)
    have hstep : 2 ^ Nat.size N = 2 * 2 ^ (Nat.size N - 1) := by
      conv_lhs => rw [show Nat.size N = (Nat.size N - 1) + 1 by omega]
      ring
    omega
  have hsqR : ((Nat.size N : ℝ)) ^ 2 ≤ 8 * N := by exact_mod_cast hsq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (0 : ℝ) < Nat.size N := by exact_mod_cast hsize
  rw [div_le_div_iff₀ hNR hsR]
  nlinarith

/-- **The discrepancy of the van der Corput sequence tends to zero**: it is equidistributed. -/
theorem tendsto_discrepancy_vdc : Tendsto (fun N : ℕ => discrepancy vdc N) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => 2 * ((Nat.size N : ℝ) / N)) atTop (𝓝 0) := by
    simpa using tendsto_size_div_atTop.const_mul 2
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => discrepancy_nonneg vdc N) ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  simpa [mul_div_assoc] using discrepancy_vdc_le hN

/-! ### Quadrature -/

/-- **Koksma's inequality for the van der Corput sequence, Lipschitz case**: the quadrature error
of the first `N` points is at most `2 L (log₂ N + 1)/N`. -/
theorem koksma_vdc_lipschitz {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → |f t - f s| ≤ L * |t - s|)
    {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (vdc n)) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ L * (2 * Nat.size N / N) := by
  have h := koksma_lipschitz_sharp hL hlip vdc hN
  simp only [fract_vdc] at h
  exact h.trans (mul_le_mul_of_nonneg_left (discrepancy_vdc_le hN) hL)

/-- **Koksma's inequality for the van der Corput sequence, bounded variation case.** -/
theorem koksma_vdc_variation {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1))
    {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (vdc n)) / N - ∫ t in (0 : ℝ)..1, f t|
      ≤ 2 * WeylDiscrepancy.unitVariation f * (2 * Nat.size N / N) := by
  have h := koksma_variation_le hf vdc hN
  simp only [fract_vdc] at h
  refine h.trans (mul_le_mul_of_nonneg_left (discrepancy_vdc_le hN) ?_)
  have := unitVariation_nonneg f
  linarith

/-- The van der Corput sequence integrates every function of bounded variation correctly. -/
theorem tendsto_average_vdc_variation {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (vdc n)) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  have h := tendsto_average_of_tendsto_discrepancy_variation hf tendsto_discrepancy_vdc
  simpa only [fract_vdc] using h

end VanDerCorput

end RiemannHypothesis
