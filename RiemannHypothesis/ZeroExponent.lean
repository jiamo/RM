/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.ZeroSum

/-!
# The exponent of convergence of the nontrivial zeroes is at most `1`

`RiemannHypothesis.ZeroSum` proves `∑_ρ 1/‖ρ‖² < ∞` for the nontrivial zeroes of `ζ`.  Here that
is sharpened to the classical statement that the *exponent of convergence* of the zero set is at
most `1`:

* `summable_inv_norm_rpow` : for every `e > 0` the sum `∑_ρ ‖ρ‖^(-(1+e))` converges.

The proof is the dyadic decomposition of `RiemannHypothesis.ZeroSum`, run with a sharper weight:
the zeroes with `2^k ≤ |γ| < 2^(k+1)` number at most `N(2^(k+1)) = O(2^k (k+1))` by the
Riemann–von Mangoldt upper bound of `RiemannHypothesis.ZeroCount`, and each of them contributes
at most `2^(-k(1+e))`, so the `k`-th block contributes `O((k+1) 2^(-k e))` and the blocks sum by
the convergence of `∑ (k+1) r^k` for `r = 2^(-e) < 1`.

Zeroes are counted *without* multiplicity, exactly as in `RiemannHypothesis.ZeroCount`.

The complementary statement — that the exponent of convergence is exactly `1`, i.e. that
`∑_ρ 1/‖ρ‖` diverges — is proved in `RiemannHypothesis.ZeroExponentOne`, from the
Riemann–von Mangoldt lower bound `N(T) ≫ T log T` and the theorem that at least five sixths of
the zeroes are distinct.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

/-! ## Two elementary lemmas -/

/-- `∑_k (k+1) r^k` converges for `0 ≤ r < 1`. -/
lemma summable_succ_mul_geometric {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * r ^ k) := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have h2 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h3 : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one h0 h1
  simpa [pow_one, add_mul, one_mul] using h2.add h3

/-- In a dyadic block of positive index the imaginary part is at least `2^k`. -/
lemma two_pow_blockIndex_le_abs_im {s : ℂ} (h : 1 ≤ blockIndex s) :
    (2 : ℝ) ^ blockIndex s ≤ |s.im| := by
  have hfloor : ⌊|s.im|⌋₊ ≠ 0 := by
    intro h0
    rw [blockIndex, h0] at h
    simp at h
  have h2 : 2 ^ blockIndex s ≤ ⌊|s.im|⌋₊ := Nat.pow_log_le_self 2 hfloor
  have h3 : ((2 ^ blockIndex s : ℕ) : ℝ) ≤ (⌊|s.im|⌋₊ : ℝ) := by exact_mod_cast h2
  have h4 : ((⌊|s.im|⌋₊ : ℕ) : ℝ) ≤ |s.im| := Nat.floor_le (abs_nonneg _)
  have hcast : ((2 ^ blockIndex s : ℕ) : ℝ) = (2 : ℝ) ^ blockIndex s := by push_cast; ring
  linarith [hcast ▸ h3]

/-! ## The uniform bound on finite sums -/

/-- The dyadic estimate: for every `e > 0` the sums `∑_{ρ ∈ S} ‖ρ‖^(-(1+e))` over finite sets `S`
of nontrivial zeroes are bounded by an absolute constant depending only on `e`. -/
theorem sum_inv_norm_rpow_le {e : ℝ} (he : 0 < e) :
    ∃ B : ℝ, 0 < B ∧ ∀ S : Finset ℂ, (∀ ρ ∈ S, ρ ∈ nontrivialZeroSet) →
      ∑ ρ ∈ S, ‖ρ‖ ^ (-(1 + e)) ≤ B := by
  classical
  obtain ⟨C, hC0, hC⟩ := ncard_nontrivialZeros_le
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_norm_of_nontrivialZero
  set δ : ℝ := min 1 δ₀ with hδdef
  have hδ : 0 < δ := lt_min one_pos hδ₀
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδle : ∀ ρ ∈ nontrivialZeroSet, δ ≤ ‖ρ‖ := fun ρ hρ => le_trans (min_le_right _ _)
    (hδ₀le ρ hρ)
  set D : ℝ := δ ^ (-(1 + e)) with hD
  have hD1 : 1 ≤ D := by
    rw [hD]
    have := Real.rpow_le_rpow_of_nonpos hδ hδ1 (by linarith : -(1 + e) ≤ 0)
    simpa using this
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD1
  -- the geometric ratio
  set r : ℝ := (2 : ℝ) ^ (-e) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsummable := summable_succ_mul_geometric hr0.le hr1
  set A : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) * r ^ k with hA
  have hA1 : 1 ≤ A := by
    have h0 : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) * r ^ k := fun k => by positivity
    have := Summable.sum_le_tsum (Finset.range 1) (fun k _ => h0 k) hsummable
    simpa [hA] using this
  refine ⟨2 * C * D * A, by positivity, ?_⟩
  intro S hS
  set K : ℕ := S.sup blockIndex with hK
  have hmaps : ∀ ρ ∈ S, blockIndex ρ ∈ range (K + 1) := fun ρ hρ =>
    mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup hρ))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun ρ : ℂ => ‖ρ‖ ^ (-(1 + e)))]
  -- the term bound inside the `k`-th block
  have hterm : ∀ k : ℕ, ∀ ρ ∈ nontrivialZeroSet, blockIndex ρ = k →
      ‖ρ‖ ^ (-(1 + e)) ≤ D * ((2 : ℝ) ^ (-(1 + e))) ^ k := by
    intro k ρ hρ hbk
    have hnorm : δ ≤ ‖ρ‖ := hδle ρ hρ
    have hpos : 0 < ‖ρ‖ := lt_of_lt_of_le hδ hnorm
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have : ‖ρ‖ ^ (-(1 + e)) ≤ δ ^ (-(1 + e)) :=
        Real.rpow_le_rpow_of_nonpos hδ hnorm (by linarith)
      simpa [hD] using this
    · have him : (2 : ℝ) ^ k ≤ |ρ.im| := by
        have := two_pow_blockIndex_le_abs_im (s := ρ) (by omega : 1 ≤ blockIndex ρ)
        rwa [hbk] at this
      have h2k : (2 : ℝ) ^ k ≤ ‖ρ‖ := le_trans him (Complex.abs_im_le_norm ρ)
      have h2kpos : (0 : ℝ) < 2 ^ k := by positivity
      have hstep : ‖ρ‖ ^ (-(1 + e)) ≤ ((2 : ℝ) ^ k) ^ (-(1 + e)) :=
        Real.rpow_le_rpow_of_nonpos h2kpos h2k (by linarith)
      have hpow : ((2 : ℝ) ^ k) ^ (-(1 + e)) = ((2 : ℝ) ^ (-(1 + e))) ^ k := by
        rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 + e))) k,
          ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
      rw [hpow] at hstep
      have hnn : (0 : ℝ) ≤ ((2 : ℝ) ^ (-(1 + e))) ^ k := by positivity
      nlinarith
  -- the block bound
  have hblock : ∀ k ∈ range (K + 1),
      ∑ ρ ∈ S with blockIndex ρ = k, ‖ρ‖ ^ (-(1 + e)) ≤ 2 * C * D * (((k : ℝ) + 1) * r ^ k) := by
    intro k _
    set F : Finset ℂ := {ρ ∈ S | blockIndex ρ = k} with hF
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
      have h5 := hC ((2 : ℝ) ^ (k + 1)) h3
      have h4 : (F.card : ℝ) ≤ ((nontrivialZeros ((2 : ℝ) ^ (k + 1))).ncard : ℝ) := by
        rw [← h2]; exact_mod_cast h1
      linarith
    have hlog : Real.log ((2 : ℝ) ^ (k + 1)) ≤ (k : ℝ) + 1 := by
      rw [Real.log_pow]
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      have hmul : ((k : ℕ) + 1 : ℝ) * Real.log 2 ≤ ((k : ℕ) + 1 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      push_cast
      linarith
    have hcard' : (F.card : ℝ) ≤ C * (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) := by
      refine hcard.trans ?_
      have hpos : (0 : ℝ) < C * (2 : ℝ) ^ (k + 1) := by positivity
      exact mul_le_mul_of_nonneg_left hlog hpos.le
    have hsum : ∑ ρ ∈ F, ‖ρ‖ ^ (-(1 + e)) ≤ (F.card : ℝ) * (D * ((2 : ℝ) ^ (-(1 + e))) ^ k) := by
      have hb : ∀ ρ ∈ F, ‖ρ‖ ^ (-(1 + e)) ≤ D * ((2 : ℝ) ^ (-(1 + e))) ^ k := by
        intro ρ hρ
        rw [hF, Finset.mem_filter] at hρ
        exact hterm k ρ (hS ρ hρ.1) hρ.2
      calc ∑ ρ ∈ F, ‖ρ‖ ^ (-(1 + e))
          ≤ ∑ _ρ ∈ F, D * ((2 : ℝ) ^ (-(1 + e))) ^ k := Finset.sum_le_sum hb
        _ = (F.card : ℝ) * (D * ((2 : ℝ) ^ (-(1 + e))) ^ k) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hratio : (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (-(1 + e))) ^ k = 2 * r ^ k := by
      have hmul : (2 : ℝ) * (2 : ℝ) ^ (-(1 + e)) = r := by
        have h1 : (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(1 + e)) = (2 : ℝ) ^ (1 + -(1 + e)) :=
          (Real.rpow_add (by norm_num) _ _).symm
        rw [Real.rpow_one] at h1
        rw [h1, hr]
        norm_num
      calc (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (-(1 + e))) ^ k
          = 2 * ((2 : ℝ) * (2 : ℝ) ^ (-(1 + e))) ^ k := by
            rw [mul_pow, pow_succ]; ring
        _ = 2 * r ^ k := by rw [hmul]
    have hnn : (0 : ℝ) ≤ D * ((2 : ℝ) ^ (-(1 + e))) ^ k := by positivity
    calc ∑ ρ ∈ F, ‖ρ‖ ^ (-(1 + e))
        ≤ (F.card : ℝ) * (D * ((2 : ℝ) ^ (-(1 + e))) ^ k) := hsum
      _ ≤ (C * (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1)) * (D * ((2 : ℝ) ^ (-(1 + e))) ^ k) :=
          mul_le_mul_of_nonneg_right hcard' hnn
      _ = C * D * ((k : ℝ) + 1) * ((2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (-(1 + e))) ^ k) := by ring
      _ = C * D * ((k : ℝ) + 1) * (2 * r ^ k) := by rw [hratio]
      _ = 2 * C * D * (((k : ℝ) + 1) * r ^ k) := by ring
  have hpartial : ∑ k ∈ range (K + 1), ((k : ℝ) + 1) * r ^ k ≤ A :=
    Summable.sum_le_tsum _ (fun k _ => by positivity) hsummable
  calc ∑ k ∈ range (K + 1), ∑ ρ ∈ S with blockIndex ρ = k, ‖ρ‖ ^ (-(1 + e))
      ≤ ∑ k ∈ range (K + 1), 2 * C * D * (((k : ℝ) + 1) * r ^ k) := Finset.sum_le_sum hblock
    _ = 2 * C * D * ∑ k ∈ range (K + 1), ((k : ℝ) + 1) * r ^ k := by rw [Finset.mul_sum]
    _ ≤ 2 * C * D * A := by
        exact mul_le_mul_of_nonneg_left hpartial (by positivity)

/-! ## The summability statement -/

/-- **The exponent of convergence of the nontrivial zeroes is at most `1`**: for every `e > 0`
the sum `∑_ρ ‖ρ‖^(-(1+e))` over the nontrivial zeroes of `ζ`, counted without multiplicity,
converges. -/
theorem summable_inv_norm_rpow {e : ℝ} (he : 0 < e) :
    Summable (fun ρ : nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-(1 + e))) := by
  classical
  obtain ⟨B, _, hB⟩ := sum_inv_norm_rpow_le he
  refine summable_of_sum_le (c := B) (fun ρ => by positivity) (fun u => ?_)
  have hinj : Set.InjOn (fun ρ : nontrivialZeroSet => (ρ : ℂ)) u :=
    fun a _ b _ h => Subtype.ext h
  have himg : ∀ ρ ∈ u.image (fun ρ : nontrivialZeroSet => (ρ : ℂ)), ρ ∈ nontrivialZeroSet := by
    intro ρ hρ
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hρ
    exact a.2
  have hsum := hB _ himg
  rwa [Finset.sum_image (fun a ha b hb h => hinj ha hb h)] at hsum

end RiemannHypothesis
