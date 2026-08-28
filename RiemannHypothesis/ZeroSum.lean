/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroCount

/-!
# Summability over the nontrivial zeroes: `∑_ρ 1/(1 + γ²) < ∞`

The Riemann–von Mangoldt upper bound `N(T) = O(T log T)` of `RiemannHypothesis.ZeroCount` is
enough to prove the classical convergence statements over the nontrivial zeroes of `ζ`, which
are the analytic input to the Hadamard product and to the explicit formula.

Main results:

* `countable_nontrivialZeroSet` : the set of nontrivial zeroes is countable;
* `summable_inv_one_add_im_sq` : `∑_ρ 1 / (1 + (im ρ)²)` converges;
* `summable_inv_one_add_norm_sq` : `∑_ρ 1 / (1 + ‖ρ‖²)` converges;
* `summable_inv_norm_sq` : `∑_ρ 1 / ‖ρ‖²` converges.

Zeroes are counted *without* multiplicity throughout, exactly as in
`RiemannHypothesis.ZeroCount`.

The proof is a dyadic decomposition: the zeroes with `2^k ≤ |γ| < 2^(k+1)` number at most
`N(2^(k+1)) = O(2^k (k+1))` by the Riemann–von Mangoldt bound, and each contributes at most
`4^(-k)`, so the block contributes `O((k+1) 2^(-k))` and the blocks sum.  A band decomposition
into unit intervals would *not* suffice with only the global bound `N(T) = O(T log T)`.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

/-- The set of all nontrivial zeroes of `ζ`: the zeroes inside the critical strip. -/
def nontrivialZeroSet : Set ℂ := {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

lemma mem_nontrivialZeros_of_mem {s : ℂ} (hs : s ∈ nontrivialZeroSet) {T : ℝ}
    (hT : |s.im| ≤ T) : s ∈ nontrivialZeros T :=
  ⟨hs.1, hs.2.1, hs.2.2, hT⟩

/-- **The nontrivial zeroes form a countable set**: each bounded height contains only finitely
many, by `finite_nontrivialZeros`. -/
theorem countable_nontrivialZeroSet : nontrivialZeroSet.Countable := by
  have hcover : nontrivialZeroSet = ⋃ n : ℕ, nontrivialZeros n := by
    ext s
    constructor
    · intro hs
      obtain ⟨n, hn⟩ := exists_nat_ge |s.im|
      exact Set.mem_iUnion.2 ⟨n, mem_nontrivialZeros_of_mem hs hn⟩
    · intro hs
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hs
      exact ⟨hn.1, hn.2.1, hn.2.2.1⟩
  rw [hcover]
  exact Set.countable_iUnion fun n => (finite_nontrivialZeros n).countable

/-! ## The dyadic block decomposition -/

/-- The dyadic block index of a point: `2^(blockIndex s) ≤ |im s| < 2^(blockIndex s + 1)`
whenever `|im s| ≥ 1`, and `blockIndex s = 0` when `|im s| < 1`. -/
def blockIndex (s : ℂ) : ℕ := Nat.log 2 ⌊|s.im|⌋₊

lemma abs_im_lt_two_pow_succ (s : ℂ) : |s.im| < 2 ^ (blockIndex s + 1) := by
  have h1 : |s.im| < (⌊|s.im|⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : ⌊|s.im|⌋₊ < 2 ^ (blockIndex s + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : ((⌊|s.im|⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (blockIndex s + 1) : ℕ) : ℝ) := by
    exact_mod_cast h2
  have : ((2 ^ (blockIndex s + 1) : ℕ) : ℝ) = 2 ^ (blockIndex s + 1) := by push_cast; ring
  linarith [this ▸ h3]

lemma inv_one_add_im_sq_le (s : ℂ) :
    1 / (1 + s.im ^ 2) ≤ 1 / 4 ^ blockIndex s := by
  rcases Nat.eq_zero_or_pos (blockIndex s) with h | h
  · rw [h]
    simp only [pow_zero, div_one]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg s.im]
  · -- `blockIndex s ≥ 1` forces `⌊|im s|⌋₊ ≠ 0`, hence `2 ^ blockIndex s ≤ |im s|`
    have hfloor : ⌊|s.im|⌋₊ ≠ 0 := by
      intro h0
      rw [blockIndex, h0] at h
      simp at h
    have h2 : 2 ^ blockIndex s ≤ ⌊|s.im|⌋₊ := Nat.pow_log_le_self 2 hfloor
    have h3 : ((2 ^ blockIndex s : ℕ) : ℝ) ≤ (⌊|s.im|⌋₊ : ℝ) := by exact_mod_cast h2
    have h4 : ((⌊|s.im|⌋₊ : ℕ) : ℝ) ≤ |s.im| := Nat.floor_le (abs_nonneg _)
    have h5 : (2 : ℝ) ^ blockIndex s ≤ |s.im| := by
      have : ((2 ^ blockIndex s : ℕ) : ℝ) = (2 : ℝ) ^ blockIndex s := by push_cast; ring
      linarith [this ▸ h3]
    have h6 : (4 : ℝ) ^ blockIndex s ≤ s.im ^ 2 := by
      have hpow : (0 : ℝ) < 2 ^ blockIndex s := by positivity
      have : ((2 : ℝ) ^ blockIndex s) ^ 2 ≤ |s.im| ^ 2 := by nlinarith
      calc (4 : ℝ) ^ blockIndex s = ((2 : ℝ) ^ blockIndex s) ^ 2 := by
            rw [← pow_mul, mul_comm (blockIndex s) 2, pow_mul]; norm_num
        _ ≤ |s.im| ^ 2 := this
        _ = s.im ^ 2 := sq_abs _
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith

/-- `∑_{k < K} (k+1) / 2^k = 4 - 2 (K+2) / 2^K`. -/
lemma sum_succ_div_two_pow (K : ℕ) :
    ∑ k ∈ range K, ((k : ℝ) + 1) / 2 ^ k = 4 - 2 * ((K : ℝ) + 2) / 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have h : (0 : ℝ) < 2 ^ K := by positivity
    field_simp
    push_cast
    ring

lemma sum_succ_div_two_pow_le (K : ℕ) :
    ∑ k ∈ range K, ((k : ℝ) + 1) / 2 ^ k ≤ 4 := by
  rw [sum_succ_div_two_pow]
  have h : (0 : ℝ) < 2 ^ K := by positivity
  have : 0 ≤ 2 * ((K : ℝ) + 2) / 2 ^ K := by positivity
  linarith

/-! ## The summability bound -/

/-- The uniform bound on finite sums: `∑_{ρ ∈ S} 1/(1 + (im ρ)²) ≤ 8C` for every finite set `S`
of nontrivial zeroes, where `C` is the Riemann–von Mangoldt constant. -/
theorem sum_inv_one_add_im_sq_le :
    ∃ B : ℝ, 0 < B ∧ ∀ S : Finset ℂ, (∀ ρ ∈ S, ρ ∈ nontrivialZeroSet) →
      ∑ ρ ∈ S, 1 / (1 + ρ.im ^ 2) ≤ B := by
  classical
  obtain ⟨C, hC0, hC⟩ := ncard_nontrivialZeros_le
  refine ⟨8 * C, by positivity, ?_⟩
  intro S hS
  set K : ℕ := S.sup blockIndex with hK
  have hmaps : ∀ ρ ∈ S, blockIndex ρ ∈ range (K + 1) := by
    intro ρ hρ
    exact mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup hρ))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun ρ : ℂ => 1 / (1 + ρ.im ^ 2))]
  have hblock : ∀ k ∈ range (K + 1),
      ∑ ρ ∈ S with blockIndex ρ = k, 1 / (1 + ρ.im ^ 2) ≤ 2 * C * (((k : ℝ) + 1) / 2 ^ k) := by
    intro k _
    set F : Finset ℂ := {ρ ∈ S | blockIndex ρ = k} with hF
    -- every element of `F` is a nontrivial zero of height at most `2^(k+1)`
    have hsub : (F : Set ℂ) ⊆ nontrivialZeros ((2 : ℝ) ^ (k + 1)) := by
      intro ρ hρ
      have hρ' : ρ ∈ F := hρ
      rw [hF, Finset.mem_filter] at hρ'
      refine mem_nontrivialZeros_of_mem (hS ρ hρ'.1) ?_
      have := abs_im_lt_two_pow_succ ρ
      rw [hρ'.2] at this
      exact this.le
    have hcard : (F.card : ℝ) ≤ C * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1)) := by
      have hfin := finite_nontrivialZeros ((2 : ℝ) ^ (k + 1))
      have h1 : (F : Set ℂ).ncard ≤ (nontrivialZeros ((2 : ℝ) ^ (k + 1))).ncard :=
        Set.ncard_le_ncard hsub hfin
      have h2 : (F : Set ℂ).ncard = F.card := Set.ncard_coe_finset F
      have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
      have := hC ((2 : ℝ) ^ (k + 1)) h3
      have h4 : (F.card : ℝ) ≤ ((nontrivialZeros ((2 : ℝ) ^ (k + 1))).ncard : ℝ) := by
        rw [← h2]; exact_mod_cast h1
      linarith
    have hlog : Real.log ((2 : ℝ) ^ (k + 1)) ≤ (k : ℝ) + 1 := by
      rw [Real.log_pow]
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      have : ((k : ℕ) + 1 : ℝ) * Real.log 2 ≤ ((k : ℕ) + 1 : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
      push_cast
      linarith
    have hsum : ∑ ρ ∈ F, 1 / (1 + ρ.im ^ 2) ≤ (F.card : ℝ) * (1 / 4 ^ k) := by
      have : ∀ ρ ∈ F, 1 / (1 + ρ.im ^ 2) ≤ 1 / 4 ^ k := by
        intro ρ hρ
        rw [hF, Finset.mem_filter] at hρ
        have := inv_one_add_im_sq_le ρ
        rwa [hρ.2] at this
      calc ∑ ρ ∈ F, 1 / (1 + ρ.im ^ 2) ≤ ∑ _ρ ∈ F, (1 / 4 ^ k : ℝ) :=
            Finset.sum_le_sum this
        _ = (F.card : ℝ) * (1 / 4 ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard' : (F.card : ℝ) ≤ C * (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) := by
      refine hcard.trans ?_
      have hpos : (0 : ℝ) < C * (2 : ℝ) ^ (k + 1) := by positivity
      exact mul_le_mul_of_nonneg_left hlog hpos.le
    have h4k : (0 : ℝ) < 4 ^ k := by positivity
    have hkey : C * (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) * (1 / 4 ^ k)
        = 2 * C * (((k : ℝ) + 1) / 2 ^ k) := by
      have h2k : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by
        rw [← mul_pow]; norm_num
      have h2kpos : (0 : ℝ) < 2 ^ k := by positivity
      rw [h2k, pow_succ]
      field_simp
    calc ∑ ρ ∈ F, 1 / (1 + ρ.im ^ 2) ≤ (F.card : ℝ) * (1 / 4 ^ k) := hsum
      _ ≤ C * (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) * (1 / 4 ^ k) := by
          apply mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ = 2 * C * (((k : ℝ) + 1) / 2 ^ k) := hkey
  calc ∑ k ∈ range (K + 1), ∑ ρ ∈ S with blockIndex ρ = k, 1 / (1 + ρ.im ^ 2)
      ≤ ∑ k ∈ range (K + 1), 2 * C * (((k : ℝ) + 1) / 2 ^ k) := Finset.sum_le_sum hblock
    _ = 2 * C * ∑ k ∈ range (K + 1), ((k : ℝ) + 1) / 2 ^ k := by rw [Finset.mul_sum]
    _ ≤ 2 * C * 4 := by
        apply mul_le_mul_of_nonneg_left (sum_succ_div_two_pow_le (K + 1)) (by positivity)
    _ = 8 * C := by ring

/-- **`∑_ρ 1/(1 + γ²) < ∞`**, the sum being over the nontrivial zeroes `ρ = β + iγ` of `ζ`,
counted without multiplicity. -/
theorem summable_inv_one_add_im_sq :
    Summable (fun ρ : nontrivialZeroSet => 1 / (1 + ((ρ : ℂ).im) ^ 2)) := by
  classical
  obtain ⟨B, _, hB⟩ := sum_inv_one_add_im_sq_le
  refine summable_of_sum_le (c := B) (fun ρ => by positivity) (fun u => ?_)
  have hinj : Set.InjOn (fun ρ : nontrivialZeroSet => (ρ : ℂ)) u :=
    fun a _ b _ h => Subtype.ext h
  have himg : ∀ ρ ∈ u.image (fun ρ : nontrivialZeroSet => (ρ : ℂ)), ρ ∈ nontrivialZeroSet := by
    intro ρ hρ
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hρ
    exact a.2
  have := hB _ himg
  rwa [Finset.sum_image (fun a ha b hb h => hinj ha hb h)] at this

/-- `∑_ρ 1/(1 + ‖ρ‖²) < ∞`: immediate from `summable_inv_one_add_im_sq`, since `|γ| ≤ ‖ρ‖`. -/
theorem summable_inv_one_add_norm_sq :
    Summable (fun ρ : nontrivialZeroSet => 1 / (1 + ‖(ρ : ℂ)‖ ^ 2)) := by
  refine summable_inv_one_add_im_sq.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
  have h : |((ρ : ℂ)).im| ≤ ‖(ρ : ℂ)‖ := Complex.abs_im_le_norm _
  have h2 : ((ρ : ℂ)).im ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith

/-- The nontrivial zeroes are bounded away from the origin: there are only finitely many of
height at most `1`, and none of them is `0`. -/
theorem exists_pos_le_norm_of_nontrivialZero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ∈ nontrivialZeroSet, δ ≤ ‖ρ‖ := by
  classical
  set F : Finset ℂ := (finite_nontrivialZeros 1).toFinset with hF
  have hpos : ∀ ρ ∈ F, 0 < ‖ρ‖ := by
    intro ρ hρ
    rw [hF, Set.Finite.mem_toFinset] at hρ
    have : ρ ≠ 0 := by
      intro h
      have := hρ.2.1
      rw [h] at this
      simp at this
    simpa [norm_pos_iff] using this
  rcases F.eq_empty_or_nonempty with hE | hNE
  · refine ⟨1, one_pos, fun ρ hρ => ?_⟩
    rcases le_or_gt |ρ.im| 1 with h | h
    · exfalso
      have : ρ ∈ F := by rw [hF, Set.Finite.mem_toFinset]; exact mem_nontrivialZeros_of_mem hρ h
      rw [hE] at this
      simp at this
    · exact le_trans h.le (Complex.abs_im_le_norm ρ)
  · refine ⟨min 1 (F.inf' hNE (fun ρ => ‖ρ‖)), ?_, fun ρ hρ => ?_⟩
    · refine lt_min one_pos ?_
      rw [Finset.lt_inf'_iff]
      exact fun ρ hρ => hpos ρ hρ
    · rcases le_or_gt |ρ.im| 1 with h | h
      · have hmem : ρ ∈ F := by
          rw [hF, Set.Finite.mem_toFinset]; exact mem_nontrivialZeros_of_mem hρ h
        exact le_trans (min_le_right _ _) (Finset.inf'_le _ hmem)
      · exact le_trans (min_le_left _ _) (le_trans h.le (Complex.abs_im_le_norm ρ))

/-- **`∑_ρ 1/‖ρ‖² < ∞`**: the classical convergence statement for the nontrivial zeroes of `ζ`,
counted without multiplicity. -/
theorem summable_inv_norm_sq :
    Summable (fun ρ : nontrivialZeroSet => 1 / ‖(ρ : ℂ)‖ ^ 2) := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_of_nontrivialZero
  set c : ℝ := 1 + 1 / δ ^ 2 with hc
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    (summable_inv_one_add_norm_sq.mul_left c)
  have hρ : δ ≤ ‖(ρ : ℂ)‖ := hδle _ ρ.2
  have hnpos : (0 : ℝ) < ‖(ρ : ℂ)‖ := lt_of_lt_of_le hδ hρ
  have hδ2 : δ ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by nlinarith
  have hn2 : (0 : ℝ) < ‖(ρ : ℂ)‖ ^ 2 := by positivity
  have hpos1 : (0 : ℝ) < 1 + ‖(ρ : ℂ)‖ ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ ‖(ρ : ℂ)‖ ^ 2 / δ ^ 2 := (one_le_div (by positivity)).2 hδ2
  have hexp : c * ‖(ρ : ℂ)‖ ^ 2 = ‖(ρ : ℂ)‖ ^ 2 + ‖(ρ : ℂ)‖ ^ 2 / δ ^ 2 := by
    rw [hc]; field_simp
  rw [mul_one_div, div_le_div_iff₀ hn2 hpos1]
  nlinarith

end RiemannHypothesis
