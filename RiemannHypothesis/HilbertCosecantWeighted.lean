/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.HilbertCosecant
import RiemannHypothesis.LocalSpacingMaximal

/-!
# The weighted cosecant inequality

For real `α_1, …, α_n`, weights `δ_r > 0` with `δ_r ≤ intDist (α_r − α_s)` for every `s ≠ r`
(`intDist` is the distance to the nearest integer of `RiemannHypothesis/LargeSieve.lean`), and
complex `u_r`,

  `|∑_{r ≠ s} u_r conj(u_s) / sin π(α_r − α_s)| ≤ (5 √2 / π) ∑_r |u_r|² / δ_r`
  (`weightedCosecantInequality`, and `weightedCosecantInequality_finset` over a finite set).

This is the weighted form of `HilbertCosecant.cosecantHilbertInequality`; Montgomery and Vaughan
(*Hilbert's inequality*, J. London Math. Soc. (2) 8 (1974), 73–82) prove it with the constant
`3/2`.  The constant here, `5 √2 / π ≈ 2.251`, is the one that follows from the weighted
Hilbert inequality with `5 √2` (`RiemannHypothesis/MontgomeryVaughanWeighted.lean`), about `1.50`
times theirs.

## The argument

The proof reruns the weighted eigenvector argument of `MontgomeryVaughanWeighted.lean` with the
kernel `B r s = √δ_r √δ_s csc π(α_r − α_s)` (`wcscKernel`):

* `sum_delta_csc_mul_csc`, `wcsc_eigen_identity` — the cosecant identity
  `csc a csc b = csc (b − a)(cot a − cot b)` (`HilbertCosecant.cscKernel_mul_cscKernel`) with the
  weights `δ_r`; the cotangent column sums cancel for an eigenvector and
  `μ² ‖v‖² = ∑_{s,t} v_s conj(v_t) √δ_s √δ_t (δ_s + δ_t) csc·cot + ∑_s δ_s b_s |v_s|²`;
* `|csc · cot| ≤ csc²`, and the two periodized maximal bounds
  `δ_s ∑_r δ_r csc² π(α_r − α_s) ≤ 6/π²` (`delta_mul_sum_delta_cscSq_le`) and
  `∑_{s ≠ t} a_s a_t δ_s^{3/2} δ_t^{1/2} csc² π(α_s − α_t) ≤ (2 √120/π²) ∑ a_t²`
  (`sum_sum_cscSq_le`).  Both come from the line bounds of
  `RiemannHypothesis/LocalSpacingMaximal.lean` applied to the periodized points `α_t + m`,
  `|m| ≤ M` (which carry the spacings `δ_t` because `δ_t ≤ 1`), the expansion
  `π² csc² πx = ∑_{m ∈ ℤ} (x + m)⁻²` (`HilbertCosecant.hasSum_inv_sq_int`), and, for the bilinear
  bound, a window argument letting `M → ∞`;
* hence `μ² ≤ (6 + 4 √120)/π² < 50/π²` (`wcsc_eigenvalue_sq_le`), and the spectral theorem and
  Cauchy–Schwarz finish.  The hypothesis `δ_r ≤ 1` is removed at the end: with two or more points
  it follows from `δ_r ≤ intDist ≤ 1/2`, and with one point the form is `0`.

No new hypothesis is assumed.  The constant `3/2` is not proved.
-/

open Complex Finset Matrix

namespace RiemannHypothesis

namespace HilbertCosecantWeighted

open LocalSpacing LargeSieve HilbertCosecant

variable {n : ℕ}

/-- A finite sum of series of nonnegative terms is bounded by `B` as soon as all its symmetric
truncations are. -/
lemma sum_hasSum_le_of_window {κ : Type*} (S : Finset κ) (g : κ → ℤ → ℝ) (G : κ → ℝ)
    (hg : ∀ t ∈ S, ∀ k, 0 ≤ g t k) (hG : ∀ t ∈ S, HasSum (g t) (G t)) {B : ℝ}
    (hB : ∀ M : ℕ, ∑ t ∈ S, ∑ k ∈ Icc (-(M : ℤ)) M, g t k ≤ B) :
    ∑ t ∈ S, G t ≤ B := by
  have hsum : HasSum (fun k => ∑ t ∈ S, g t k) (∑ t ∈ S, G t) := hasSum_sum hG
  rw [← hsum.tsum_eq]
  refine Real.tsum_le_of_sum_le (fun k => sum_nonneg fun t ht => hg t ht k) fun T => ?_
  obtain ⟨M, hM⟩ : ∃ M : ℕ, T ⊆ Icc (-(M : ℤ)) M := by
    refine ⟨T.sup Int.natAbs, fun k hk => ?_⟩
    have h := Finset.le_sup (f := Int.natAbs) hk
    simp only [mem_Icc]
    omega
  calc ∑ k ∈ T, ∑ t ∈ S, g t k ≤ ∑ k ∈ Icc (-(M : ℤ)) M, ∑ t ∈ S, g t k :=
        sum_le_sum_of_subset_of_nonneg hM fun k _ _ => sum_nonneg fun t ht => hg t ht k
    _ = ∑ t ∈ S, ∑ k ∈ Icc (-(M : ℤ)) M, g t k := sum_comm
    _ ≤ B := hB M

/-- The periodized points `α_t + m`. -/
def perLam (α : Fin n → ℝ) (p : Fin n × ℤ) : ℝ := α p.1 + p.2

/-- The periodized points carry the local spacings `δ_t`, provided `δ_t ≤ 1`. -/
lemma perLam_sep {α δ : Fin n → ℝ} (hδ1 : ∀ r, δ r ≤ 1)
    (hsep : ∀ r s, r ≠ s → δ r ≤ intDist (α r - α s)) {p q : Fin n × ℤ} (hpq : p ≠ q) :
    δ p.1 ≤ |perLam α p - perLam α q| := by
  unfold perLam
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
    have hdiff : α p.1 + (p.2 : ℝ) - (α q.1 + q.2) = ((p.2 - q.2 : ℤ) : ℝ) := by
      rw [h1]; push_cast; ring
    rw [hdiff]
    have : (1 : ℝ) ≤ |((p.2 - q.2 : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h2)
    linarith [hδ1 p.1]
  · have hdiff : α p.1 + (p.2 : ℝ) - (α q.1 + q.2) = (α p.1 - α q.1) - ((q.2 - p.2 : ℤ) : ℝ) := by
      push_cast; ring
    rw [hdiff]
    exact (hsep p.1 q.1 h1).trans (intDist_le_abs_sub_int _ _)

/-- Sums over the off-diagonal pairs. -/
lemma sum_offDiag_eq (f : Fin n × Fin n → ℝ) :
    ∑ p ∈ univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2), f p
      = ∑ s, ∑ t ∈ univ.erase s, f (s, t) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_filter, Finset.filter_ne]

lemma card_Icc_symm (M : ℕ) : ((Icc (-(M : ℤ)) M).card : ℝ) = 2 * M + 1 := by
  rw [Int.card_Icc]
  have : (M : ℤ) + 1 - -(M : ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]
  push_cast; ring

/-- **The column sums of the weighted `csc²` kernel**: `δ_s ∑_r δ_r csc² π(α_r − α_s) ≤ 6/π²`,
from `delta_mul_sum_delta_div_sq_le` for the periodized points `α_r + m`. -/
lemma delta_mul_sum_delta_cscSq_le {α δ : Fin n → ℝ} (hδ : ∀ r, 0 < δ r)
    (hδ1 : ∀ r, δ r ≤ 1) (hsep : ∀ r s, r ≠ s → δ r ≤ intDist (α r - α s)) (s : Fin n) :
    δ s * ∑ r, δ r * cscKernel α r s ^ 2 ≤ 6 / Real.pi ^ 2 := by
  classical
  have hδs := hδ s
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hnotint : ∀ r ∈ univ.erase s, ∀ m : ℤ, α r - α s ≠ m := fun r hr m =>
    ne_int_of_le_intDist (hδ r) (hsep r s (ne_of_mem_erase hr)) m
  set g : Fin n → ℤ → ℝ := fun r m => δ r / (α r - α s + m) ^ 2 with hg
  have hG : ∀ r ∈ univ.erase s,
      HasSum (g r) (δ r * (Real.pi ^ 2 / Real.sin (Real.pi * (α r - α s)) ^ 2)) := by
    intro r hr
    have := (hasSum_inv_sq_int (hnotint r hr)).mul_left (δ r)
    have hgr : g r = fun i : ℤ => δ r * (1 / (α r - α s + i) ^ 2) := by
      funext m; simp only [hg]; ring
    rw [hgr]; exact this
  have hwin : ∀ M : ℕ, ∑ r ∈ univ.erase s, ∑ k ∈ Icc (-(M : ℤ)) M, g r k ≤ 6 / δ s := by
    intro M
    set P : Finset (Fin n × ℤ) := univ ×ˢ Icc (-(M : ℤ)) M with hP
    have hp0 : ((s, 0) : Fin n × ℤ) ∈ P := by simp [hP]
    have h6 := delta_mul_sum_delta_div_sq_le (lam := fun p : P => perLam α p.1)
      (δ := fun p : P => δ p.1.1) (fun p => hδ _)
      (fun p q hpq => perLam_sep hδ1 hsep (fun h => hpq (Subtype.ext h))) ⟨(s, 0), hp0⟩
    have hconv : ∑ t ∈ univ.erase (⟨(s, 0), hp0⟩ : P),
        δ t.1.1 / (perLam α (s, 0) - perLam α t.1) ^ 2
        = ∑ q ∈ P, δ q.1 / (perLam α (s, 0) - perLam α q) ^ 2 := by
      rw [Finset.sum_erase univ (by simp)]
      exact Finset.sum_coe_sort P (fun q => δ q.1 / (perLam α (s, 0) - perLam α q) ^ 2)
    have hlow : ∑ r ∈ univ.erase s, ∑ k ∈ Icc (-(M : ℤ)) M, g r k
        ≤ ∑ q ∈ P, δ q.1 / (perLam α (s, 0) - perLam α q) ^ 2 := by
      rw [hP, Finset.sum_product]
      refine le_trans (le_of_eq ?_) (sum_le_sum_of_subset_of_nonneg (erase_subset s univ)
        fun r _ _ => sum_nonneg fun k _ => div_nonneg (hδ r).le (sq_nonneg _))
      refine sum_congr rfl fun r _ => sum_congr rfl fun k _ => ?_
      simp only [hg, perLam]
      congr 1
      push_cast
      ring
    have h6' : δ s * ∑ q ∈ P, δ q.1 / (perLam α (s, 0) - perLam α q) ^ 2 ≤ 6 := by
      rw [← hconv]; exact h6
    rw [le_div_iff₀ hδs]
    nlinarith
  have hmain := sum_hasSum_le_of_window (univ.erase s) g _
    (fun r _ k => div_nonneg (hδ r).le (sq_nonneg _)) hG hwin
  rw [← Finset.sum_erase univ (a := s) (by simp [cscKernel_self])]
  have heq : ∑ r ∈ univ.erase s, δ r * cscKernel α r s ^ 2
      = (1 / Real.pi ^ 2) * ∑ r ∈ univ.erase s,
          δ r * (Real.pi ^ 2 / Real.sin (Real.pi * (α r - α s)) ^ 2) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun r _ => ?_
    unfold cscKernel
    field_simp
  rw [heq]
  calc δ s * (1 / Real.pi ^ 2 * ∑ r ∈ univ.erase s,
          δ r * (Real.pi ^ 2 / Real.sin (Real.pi * (α r - α s)) ^ 2))
      ≤ δ s * (1 / Real.pi ^ 2 * (6 / δ s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain (by positivity)) hδs.le
    _ = 6 / Real.pi ^ 2 := by field_simp

/-- The truncated periodized bilinear bound: for every `K`,
`∑_{s ≠ t} c_{st} ∑_{|k| ≤ K} (α_s − α_t + k)⁻² ≤ 2 √120 ∑ a_t²`. -/
lemma sum_sum_window_le {α δ : Fin n → ℝ} (hδ : ∀ r, 0 < δ r)
    (hδ1 : ∀ r, δ r ≤ 1) (hsep : ∀ r s, r ≠ s → δ r ≤ intDist (α r - α s))
    {a : Fin n → ℝ} (ha : ∀ t, 0 ≤ a t) (K : ℕ) :
    ∑ s, ∑ t ∈ univ.erase s, ∑ k ∈ Icc (-(K : ℤ)) K,
        a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t)) / (α s - α t + k) ^ 2
      ≤ 2 * Real.sqrt 120 * ∑ t, a t ^ 2 := by
  classical
  set c : Fin n → Fin n → ℝ := fun s t => a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t))
    with hc
  have hc0 : ∀ s t, 0 ≤ c s t := fun s t => by
    have := ha s; have := ha t; have := hδ s; positivity
  set X : ℝ := ∑ s, ∑ t ∈ univ.erase s, ∑ k ∈ Icc (-(K : ℤ)) K, c s t / (α s - α t + k) ^ 2
    with hX
  set B : ℝ := 2 * Real.sqrt 120 * ∑ t, a t ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  -- the bound for the window of radius `K + N`
  have hstep : ∀ N : ℕ, (2 * (N : ℝ) + 1) * X ≤ B * (2 * ((K + N : ℕ) : ℝ) + 1) := by
    intro N
    set M : ℕ := K + N with hM
    set W : Finset ℤ := Icc (-(M : ℤ)) M with hW
    set W' : Finset ℤ := Icc (-(N : ℤ)) N with hW'
    set P : Finset (Fin n × ℤ) := univ ×ˢ W with hP
    set F : Fin n × ℤ → Fin n × ℤ → ℝ := fun p q =>
      a p.1 * a q.1 * (δ p.1 * Real.sqrt (δ p.1) * Real.sqrt (δ q.1))
        / (perLam α p - perLam α q) ^ 2 with hF
    have hF0 : ∀ p q, 0 ≤ F p q := fun p q => div_nonneg (hc0 p.1 q.1) (sq_nonneg _)
    have hLS := sum_sum_mul_div_sq_le (lam := fun p : P => perLam α p.1)
      (δ := fun p : P => δ p.1.1) (fun p => hδ _)
      (fun p q hpq => perLam_sep hδ1 hsep (fun h => hpq (Subtype.ext h)))
      (a := fun p : P => a p.1.1) (fun p => ha _)
    -- the left side as a double sum over `P`
    have hL : ∑ p : P, ∑ q ∈ univ.erase p, a p.1.1 * a q.1.1
          * (δ p.1.1 * Real.sqrt (δ p.1.1) * Real.sqrt (δ q.1.1))
          / (perLam α p.1 - perLam α q.1) ^ 2
        = ∑ p ∈ P, ∑ q ∈ P, F p q := by
      rw [← Finset.sum_coe_sort P (fun p => ∑ q ∈ P, F p q)]
      refine sum_congr rfl fun p _ => ?_
      rw [Finset.sum_erase univ (by simp)]
      exact Finset.sum_coe_sort P (F p.1)
    -- the right side
    have hR : ∑ p : P, a p.1.1 ^ 2 = (2 * (M : ℝ) + 1) * ∑ t, a t ^ 2 := by
      rw [Finset.sum_coe_sort P (fun p => a p.1 ^ 2), hP, Finset.sum_product, Finset.mul_sum]
      refine sum_congr rfl fun t _ => ?_
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hW, card_Icc_symm]
    -- the lower bound
    have hlow : (2 * (N : ℝ) + 1) * X ≤ ∑ p ∈ P, ∑ q ∈ P, F p q := by
      rw [hP, Finset.sum_product]
      have hinner : ∀ s, (2 * (N : ℝ) + 1)
            * ∑ t ∈ univ.erase s, ∑ k ∈ Icc (-(K : ℤ)) K, c s t / (α s - α t + k) ^ 2
          ≤ ∑ j ∈ W, ∑ q ∈ univ ×ˢ W, F (s, j) q := by
        intro s
        rw [← card_Icc_symm N, ← nsmul_eq_mul, ← Finset.sum_const]
        refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg
          (show W' ⊆ W from Icc_subset_Icc (by omega) (by omega))
          fun j _ _ => sum_nonneg fun q _ => hF0 _ _)
        refine sum_le_sum fun j hj => ?_
        rw [Finset.sum_product]
        refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (erase_subset s univ)
          fun t _ _ => sum_nonneg fun l _ => hF0 _ _)
        refine sum_le_sum fun t _ => ?_
        have hinj : Set.InjOn (fun k : ℤ => j - k) (Icc (-(K : ℤ)) K : Set ℤ) :=
          fun k _ k' _ h => by simpa using h
        have himg : (Icc (-(K : ℤ)) K).image (fun k : ℤ => j - k) ⊆ W := by
          intro l hl
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
          simp only [mem_Icc, hW, hM] at hk hj ⊢
          push_cast
          omega
        refine le_trans (le_of_eq ?_) (sum_le_sum_of_subset_of_nonneg himg
          fun l _ _ => hF0 _ _)
        rw [Finset.sum_image hinj]
        refine sum_congr rfl fun k _ => ?_
        simp only [hF, hc, perLam]
        congr 1
        push_cast
        ring
      calc (2 * (N : ℝ) + 1) * X
          = ∑ s, (2 * (N : ℝ) + 1)
              * ∑ t ∈ univ.erase s, ∑ k ∈ Icc (-(K : ℤ)) K, c s t / (α s - α t + k) ^ 2 := by
            rw [hX, Finset.mul_sum]
        _ ≤ ∑ s, ∑ j ∈ W, ∑ q ∈ univ ×ˢ W, F (s, j) q := sum_le_sum fun s _ => hinner s
    have := hLS
    rw [hL, hR] at this
    calc (2 * (N : ℝ) + 1) * X ≤ ∑ p ∈ P, ∑ q ∈ P, F p q := hlow
      _ ≤ 2 * Real.sqrt 120 * ((2 * (M : ℝ) + 1) * ∑ t, a t ^ 2) := this
      _ = B * (2 * ((K + N : ℕ) : ℝ) + 1) := by rw [hB, hM]; ring
  -- letting the window grow
  by_contra hcon
  push Not at hcon
  have hgap : 0 < X - B := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (K : ℝ) * B / (X - B))
  have h := hstep N
  push_cast at h
  have h2 : 2 * (K : ℝ) * B < N * (X - B) := by
    rwa [div_lt_iff₀ hgap] at hN
  nlinarith

/-- **The periodized bilinear bound**:
`∑_{s ≠ t} a_s a_t δ_s^{3/2} δ_t^{1/2} csc² π(α_s − α_t) ≤ (2 √120 / π²) ∑ a_t²` for `a ≥ 0`. -/
theorem sum_sum_cscSq_le {α δ : Fin n → ℝ} (hδ : ∀ r, 0 < δ r)
    (hδ1 : ∀ r, δ r ≤ 1) (hsep : ∀ r s, r ≠ s → δ r ≤ intDist (α r - α s))
    {a : Fin n → ℝ} (ha : ∀ t, 0 ≤ a t) :
    ∑ s, ∑ t ∈ univ.erase s,
        a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t)) * cscKernel α s t ^ 2
      ≤ 2 * Real.sqrt 120 / Real.pi ^ 2 * ∑ t, a t ^ 2 := by
  classical
  set c : Fin n → Fin n → ℝ := fun s t => a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t))
    with hc
  have hc0 : ∀ s t, 0 ≤ c s t := fun s t => by
    have := ha s; have := ha t; have := hδ s; positivity
  have hpi : 0 < Real.pi ^ 2 := by positivity
  set S := univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2) with hS
  set g : Fin n × Fin n → ℤ → ℝ := fun p k => c p.1 p.2 / (α p.1 - α p.2 + k) ^ 2 with hg
  have hG : ∀ p ∈ S, HasSum (g p)
      (c p.1 p.2 * (Real.pi ^ 2 / Real.sin (Real.pi * (α p.1 - α p.2)) ^ 2)) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hni : ∀ m : ℤ, α p.1 - α p.2 ≠ m :=
      ne_int_of_le_intDist (hδ p.1) (hsep p.1 p.2 hne)
    have := (hasSum_inv_sq_int hni).mul_left (c p.1 p.2)
    have hgp : g p = fun i : ℤ => c p.1 p.2 * (1 / (α p.1 - α p.2 + i) ^ 2) := by
      funext m; simp only [hg]; ring
    rw [hgp]; exact this
  have hwin : ∀ M : ℕ, ∑ p ∈ S, ∑ k ∈ Icc (-(M : ℤ)) M, g p k
      ≤ 2 * Real.sqrt 120 * ∑ t, a t ^ 2 := by
    intro M
    rw [hS, sum_offDiag_eq (fun p => ∑ k ∈ Icc (-(M : ℤ)) M, g p k)]
    exact sum_sum_window_le hδ hδ1 hsep ha M
  have hmain := sum_hasSum_le_of_window S g _
    (fun p _ k => div_nonneg (hc0 _ _) (sq_nonneg _)) hG hwin
  rw [hS, sum_offDiag_eq] at hmain
  have heq : ∑ s, ∑ t ∈ univ.erase s,
        a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t)) * cscKernel α s t ^ 2
      = (1 / Real.pi ^ 2) * ∑ s, ∑ t ∈ univ.erase s,
          c s t * (Real.pi ^ 2 / Real.sin (Real.pi * (α s - α t)) ^ 2) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun t _ => ?_
    simp only [hc, cscKernel]
    field_simp
  rw [heq]
  calc 1 / Real.pi ^ 2 * ∑ s, ∑ t ∈ univ.erase s,
          c s t * (Real.pi ^ 2 / Real.sin (Real.pi * (α s - α t)) ^ 2)
      ≤ 1 / Real.pi ^ 2 * (2 * Real.sqrt 120 * ∑ t, a t ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 2 * Real.sqrt 120 / Real.pi ^ 2 * ∑ t, a t ^ 2 := by ring

/-- The weighted cosecant kernel `√δ_r √δ_s csc π(α_r − α_s)` (`0` on the diagonal). -/
noncomputable def wcscKernel (α δ : Fin n → ℝ) (r s : Fin n) : ℝ :=
  Real.sqrt (δ r) * Real.sqrt (δ s) * cscKernel α r s

lemma wcscKernel_swap (α δ : Fin n → ℝ) (r s : Fin n) :
    wcscKernel α δ s r = - wcscKernel α δ r s := by
  unfold wcscKernel; rw [cscKernel_swap α r s]; ring

/-- `c_s = ∑_r δ_r cot π(α_r − α_s)`. -/
noncomputable def wcotColSum (α δ : Fin n → ℝ) (s : Fin n) : ℝ := ∑ r, δ r * cotKernel α r s

/-- `b_s = ∑_r δ_r csc² π(α_r − α_s)`. -/
noncomputable def wcscColSq (α δ : Fin n → ℝ) (s : Fin n) : ℝ :=
  ∑ r, δ r * cscKernel α r s ^ 2

/-- The weighted cosecant identity, summed over `r`. -/
lemma sum_delta_csc_mul_csc {α : Fin n → ℝ} (δ : Fin n → ℝ)
    (hinj : ∀ r s, r ≠ s → Real.sin (Real.pi * (α r - α s)) ≠ 0) (s t : Fin n) :
    ∑ r, δ r * cscKernel α r s * cscKernel α r t
      = cscKernel α s t * (wcotColSum α δ s - wcotColSum α δ t)
        + (δ s + δ t) * (cscKernel α s t * cotKernel α s t)
        + (if s = t then wcscColSq α δ s else 0) := by
  by_cases hst : s = t
  · subst hst
    simp [cscKernel_self, wcscColSq, sq, mul_assoc]
  rw [Finset.sum_congr rfl fun r _ => by rw [mul_assoc, cscKernel_mul_cscKernel hinj r hst]]
  simp only [mul_add, Finset.sum_add_distrib, if_neg hst, add_zero]
  have h1 : ∑ r, δ r * (if r = s then cscKernel α s t * cotKernel α s t else 0)
      = δ s * (cscKernel α s t * cotKernel α s t) := by simp
  have h2 : ∑ r, δ r * (if r = t then cscKernel α s t * cotKernel α s t else 0)
      = δ t * (cscKernel α s t * cotKernel α s t) := by simp
  rw [h1, h2]
  unfold wcotColSum
  have : ∑ r, δ r * (cscKernel α s t * (cotKernel α r s - cotKernel α r t))
      = cscKernel α s t * (∑ r, δ r * cotKernel α r s - ∑ r, δ r * cotKernel α r t) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [this]
  ring

/-- **The weighted eigenvector identity for the cosecant kernel.** -/
theorem wcsc_eigen_identity {α δ : Fin n → ℝ}
    (hinj : ∀ r s, r ≠ s → Real.sin (Real.pi * (α r - α s)) ≠ 0)
    (hδ : ∀ r, 0 ≤ δ r) (v : Fin n → ℂ) (μ : ℝ)
    (hv : ∀ r, ∑ s, (wcscKernel α δ r s : ℂ) * v s = I * μ * v r) :
    ((μ ^ 2 * ∑ r, ‖v r‖ ^ 2 : ℝ) : ℂ)
      = ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t)
          * ((Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t)
              * (cscKernel α s t * cotKernel α s t) : ℝ) : ℂ)
        + ((∑ s, δ s * wcscColSq α δ s * ‖v s‖ ^ 2 : ℝ) : ℂ) := by
  set W : Fin n → Fin n → ℝ := wcscKernel α δ with hW
  set K : Fin n → Fin n → ℝ := cscKernel α with hK
  set a := wcotColSum α δ with ha
  set b := wcscColSq α δ with hb
  set w : Fin n → ℝ := fun r => Real.sqrt (δ r) with hw
  have hww : ∀ r, w r * w r = δ r := fun r => Real.mul_self_sqrt (hδ r)
  have hWdef : ∀ r s, W r s = w r * w s * K r s := fun r s => rfl
  have hvc : ∀ r, ∑ s, (W r s : ℂ) * (starRingEnd ℂ) (v s)
      = -(I * μ) * (starRingEnd ℂ) (v r) := by
    intro r
    have := congrArg (starRingEnd ℂ) (hv r)
    simpa [map_sum, map_mul, Complex.conj_ofReal, Complex.conj_I] using this
  have hcol : ∀ t, ∑ s, (W s t : ℂ) * v s = -(I * μ * v t) := by
    intro t
    rw [← hv t, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hW, wcscKernel_swap α δ t s]; push_cast; ring
  have hnorm : ∀ r, v r * (starRingEnd ℂ) (v r) = ((‖v r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hL : (∑ r, (∑ s, (W r s : ℂ) * v s) * (starRingEnd ℂ) (∑ t, (W r t : ℂ) * v t))
      = ((μ ^ 2 * ∑ r, ‖v r‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hv r, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have := hnorm r
    push_cast at this
    linear_combination (μ:ℂ)^2 * this - (μ:ℂ)^2 * v r * (starRingEnd ℂ) (v r) * Complex.I_sq
  have hE : (∑ r, (∑ s, (W r s : ℂ) * v s) * (starRingEnd ℂ) (∑ t, (W r t : ℂ) * v t))
      = ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t)
          * ((w s * w t * ∑ r, δ r * K r s * K r t : ℝ) : ℂ) := by
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hWdef, hWdef, ← hww r]
    push_cast
    ring
  have hX1 : ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a s : ℂ))
      = ∑ s, (a s : ℂ) * (-(I * μ)) * ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    have := hvc s
    rw [← hnorm s]
    calc ∑ t, v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a s : ℂ))
        = v s * (a s : ℂ) * ∑ t, (W s t : ℂ) * (starRingEnd ℂ) (v t) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => ?_; ring
      _ = _ := by rw [this]; ring
  have hX2 : ∑ s, ∑ t, v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a t : ℂ))
      = ∑ s, (a s : ℂ) * (-(I * μ)) * ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have := hcol t
    rw [← hnorm t]
    calc ∑ s, v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a t : ℂ))
        = (starRingEnd ℂ) (v t) * (a t : ℂ) * ∑ s, (W s t : ℂ) * v s := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring
      _ = _ := by rw [this]; ring
  rw [← hL, hE]
  have hterm : ∀ s t, v s * (starRingEnd ℂ) (v t)
      * ((w s * w t * ∑ r, δ r * K r s * K r t : ℝ) : ℂ)
      = v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a s : ℂ))
        - v s * (starRingEnd ℂ) (v t) * ((W s t : ℂ) * (a t : ℂ))
        + v s * (starRingEnd ℂ) (v t)
          * ((Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t)
              * (cscKernel α s t * cotKernel α s t) : ℝ) : ℂ)
        + (if s = t then ((δ s * b s * ‖v s‖ ^ 2 : ℝ) : ℂ) else 0) := by
    intro s t
    rw [sum_delta_csc_mul_csc δ hinj s t]
    split_ifs with h
    · subst h
      have h1 := hnorm s
      have h2 : ((w s * w s : ℝ) : ℂ) = (δ s : ℂ) := by rw [hww s]
      have hk : K s s = 0 := cscKernel_self α s
      have hk' : cscKernel α s s = 0 := cscKernel_self α s
      rw [hWdef, hk, hk']
      push_cast at h1 h2 ⊢
      linear_combination ((w s : ℂ) * w s * b s) * h1 + (b s : ℂ) * (‖v s‖ : ℂ) ^ 2 * h2
    · simp only [hWdef, hw]
      push_cast
      ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, hX1, hX2]
  push_cast
  ring

/-- `√120 < 11`. -/
lemma sqrt_120_lt : Real.sqrt 120 < 11 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **The weighted eigenvalue bound for the cosecant kernel**: `μ² ≤ 50 / π²`. -/
theorem wcsc_eigenvalue_sq_le {α δ : Fin n → ℝ} (hδ : ∀ r, 0 < δ r) (hδ1 : ∀ r, δ r ≤ 1)
    (hsep : ∀ r s, r ≠ s → δ r ≤ intDist (α r - α s))
    (v : Fin n → ℂ) (μ : ℝ) (hv0 : ∃ r, v r ≠ 0)
    (hv : ∀ r, ∑ s, (wcscKernel α δ r s : ℂ) * v s = I * μ * v r) :
    μ ^ 2 ≤ 50 / Real.pi ^ 2 := by
  have hinj : ∀ r s, r ≠ s → Real.sin (Real.pi * (α r - α s)) ≠ 0 := fun r s h =>
    sin_pi_mul_ne_zero_of_ne_int (ne_int_of_le_intDist (hδ r) (hsep r s h))
  have hid := wcsc_eigen_identity hinj (fun r => (hδ r).le) v μ hv
  set a : Fin n → ℝ := fun t => ‖v t‖ with hadef
  have ha : ∀ t, 0 ≤ a t := fun t => norm_nonneg _
  set g : Fin n → Fin n → ℝ := fun s t =>
    a s * a t * (δ s * Real.sqrt (δ s) * Real.sqrt (δ t)) * cscKernel α s t ^ 2 with hgdef
  have hA : (∑ s, ∑ t, v s * (starRingEnd ℂ) (v t)
      * ((Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t)
          * (cscKernel α s t * cotKernel α s t) : ℝ) : ℂ)).re
      ≤ ∑ s, ∑ t, (g s t + g t s) := by
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [Complex.re_mul_ofReal]
    have hc : 0 ≤ Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t) := by
      have := hδ s; have := hδ t; positivity
    have hre : |(v s * (starRingEnd ℂ) (v t)).re| ≤ a s * a t := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, RCLike.norm_conj]
    have hcc := abs_csc_mul_cot_le α s t
    calc (v s * (starRingEnd ℂ) (v t)).re
          * (Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t)
            * (cscKernel α s t * cotKernel α s t))
        ≤ |(v s * (starRingEnd ℂ) (v t)).re|
          * (Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t)
            * |cscKernel α s t * cotKernel α s t|) := by
          refine (le_abs_self _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg hc]
      _ ≤ a s * a t * (Real.sqrt (δ s) * Real.sqrt (δ t) * (δ s + δ t)
            * cscKernel α s t ^ 2) := by
          apply mul_le_mul hre (mul_le_mul_of_nonneg_left hcc hc)
            (mul_nonneg hc (abs_nonneg _)) (by positivity)
      _ = g s t + g t s := by
          simp only [hgdef]
          rw [show cscKernel α t s ^ 2 = cscKernel α s t ^ 2 by rw [cscKernel_swap, neg_sq]]
          ring
  have hB : ∑ s, ∑ t, (g s t + g t s) = 2 * ∑ s, ∑ t, g s t := by
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_comm (f := fun s t => g t s)]
    ring
  have hC : ∑ s, ∑ t, g s t ≤ 2 * Real.sqrt 120 / Real.pi ^ 2 * ∑ t, a t ^ 2 := by
    refine le_trans (le_of_eq ?_) (sum_sum_cscSq_le hδ hδ1 hsep ha)
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_erase (s := Finset.univ) (a := s) (by simp [hgdef, cscKernel_self])]
  have hD : ∑ s, δ s * wcscColSq α δ s * ‖v s‖ ^ 2 ≤ 6 / Real.pi ^ 2 * ∑ t, a t ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have h6 := delta_mul_sum_delta_cscSq_le hδ hδ1 hsep s
    exact mul_le_mul_of_nonneg_right h6 (sq_nonneg _)
  have hre := congrArg Complex.re hid
  rw [Complex.ofReal_re, Complex.add_re, Complex.ofReal_re] at hre
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hS : 0 ≤ ∑ t, a t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
  have htot : μ ^ 2 * ∑ r, ‖v r‖ ^ 2 ≤ 50 / Real.pi ^ 2 * ∑ t, a t ^ 2 := by
    have h11 := sqrt_120_lt
    have hk : 2 * (2 * Real.sqrt 120 / Real.pi ^ 2) + 6 / Real.pi ^ 2 ≤ 50 / Real.pi ^ 2 := by
      have he : 2 * (2 * Real.sqrt 120 / Real.pi ^ 2) + 6 / Real.pi ^ 2
          = (4 * Real.sqrt 120 + 6) / Real.pi ^ 2 := by ring
      rw [he, div_le_div_iff_of_pos_right hpi]
      linarith
    nlinarith
  obtain ⟨r0, hr0⟩ := hv0
  have hpos : 0 < ∑ r, ‖v r‖ ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun r => ‖v r‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ r0))
  exact le_of_mul_le_mul_right htot hpos

/-! ## The spectral theorem -/

/-- The Hermitian matrix `i B`, `(i B) r s = i √δ_r √δ_s csc π(α_r − α_s)`. -/
noncomputable def wcscMatrix (α δ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun r s => I * (wcscKernel α δ r s : ℂ)

lemma wcscMatrix_isHermitian (α δ : Fin n → ℝ) : (wcscMatrix α δ).IsHermitian := by
  ext r s
  simp only [wcscMatrix, conjTranspose_apply, of_apply, star_mul', Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, wcscKernel_swap α δ r s]
  push_cast; ring

lemma toEuclideanLin_wcscMatrix_apply (α δ : Fin n → ℝ) (x : EuclideanSpace ℂ (Fin n))
    (r : Fin n) :
    (Matrix.toEuclideanLin (wcscMatrix α δ) x).ofLp r
      = I * ∑ s, (wcscKernel α δ r s : ℂ) * x.ofLp s := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, wcscMatrix, Finset.mul_sum,
    mul_assoc]

/-- A bound `μ² ≤ C` on the eigenvalues of `B` gives `‖(i B) x‖² ≤ C ‖x‖²`. -/
lemma norm_wcscMatrix_apply_le {α δ : Fin n → ℝ} (C : ℝ)
    (heig : ∀ (v : Fin n → ℂ) (μ : ℝ), (∃ r, v r ≠ 0) →
      (∀ r, ∑ s, (wcscKernel α δ r s : ℂ) * v s = I * μ * v r) → μ ^ 2 ≤ C)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin (wcscMatrix α δ) x‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
  set T := Matrix.toEuclideanLin (wcscMatrix α δ)
  have hT : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr (wcscMatrix_isHermitian α δ)
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by simp
  set b := hT.eigenvectorBasis hn
  set ν := hT.eigenvalues hn
  have hν : ∀ i, ν i ^ 2 ≤ C := by
    intro i
    have hu := hT.apply_eigenvectorBasis hn i
    rw [← neg_sq]
    refine heig (b i).ofLp (-ν i) ?_ ?_
    · by_contra h
      push Not at h
      have : b i = 0 := by ext r; simp [h r]
      have h1 := b.orthonormal.1 i
      rw [this, norm_zero] at h1
      exact zero_ne_one h1
    · intro r
      have := congrArg (fun y : EuclideanSpace ℂ (Fin n) => y.ofLp r) hu
      simp only [toEuclideanLin_wcscMatrix_apply, T] at this
      rw [PiLp.smul_apply] at this
      push_cast
      linear_combination (-I) * this
        + (∑ s, (wcscKernel α δ r s : ℂ) * (b i).ofLp s) * Complex.I_sq
  have hrepr : ∀ i, b.repr (T x) i = (ν i : ℂ) * b.repr x i := by
    intro i
    rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, ← hT,
      hT.apply_eigenvectorBasis hn i, inner_smul_left, RCLike.conj_ofReal]
    rfl
  rw [← b.repr.norm_map (T x), ← b.repr.norm_map x, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hrepr, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_right (hν i) (by positivity)

/-! ## The theorem -/

/-- The inequality under the extra hypothesis `δ_r ≤ 1`. -/
lemma weightedCosecantInequality_aux {n : ℕ} (α δ : Fin n → ℝ) (hδ : ∀ r, 0 < δ r)
    (hδ1 : ∀ r, δ r ≤ 1) (hsep : ∀ r s : Fin n, r ≠ s → δ r ≤ intDist (α r - α s))
    (u : Fin n → ℂ) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (α r - α s)) : ℂ)‖
      ≤ 5 * Real.sqrt 2 / Real.pi * ∑ r, ‖u r‖ ^ 2 / δ r := by
  set w : Fin n → ℝ := fun r => Real.sqrt (δ r) with hwdef
  have hwpos : ∀ r, 0 < w r := fun r => Real.sqrt_pos.mpr (hδ r)
  have hww : ∀ r, w r * w r = δ r := fun r => Real.mul_self_sqrt (hδ r).le
  set x : Fin n → ℂ := fun r => u r / (w r : ℂ) with hxdef
  have hxu : ∀ r, u r = (w r : ℂ) * x r := by
    intro r
    have : (w r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos r).ne'
    simp only [hxdef]; field_simp
  set T := Matrix.toEuclideanLin (wcscMatrix α δ)
  set xe : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  have hpi : 0 < Real.pi := Real.pi_pos
  have h50 : (5 * Real.sqrt 2 / Real.pi) ^ 2 = 50 / Real.pi ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hop : ‖T xe‖ ≤ 5 * Real.sqrt 2 / Real.pi * ‖xe‖ := by
    have h := norm_wcscMatrix_apply_le (α := α) (δ := δ) (50 / Real.pi ^ 2)
      (fun v μ hv0 hv => wcsc_eigenvalue_sq_le hδ hδ1 hsep v μ hv0 hv) xe
    rw [← h50, ← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  have hxe : ‖xe‖ ^ 2 = ∑ r, ‖u r‖ ^ 2 / δ r := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hx : xe.ofLp r = x r := rfl
    rw [hx, hxdef]
    simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hwpos r), div_pow,
      sq (w r), hww r]
  have hform : ∑ r, ∑ s ∈ Finset.univ.erase r,
      u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (α r - α s)) : ℂ)
        = I * inner ℂ (T xe) xe := by
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [toEuclideanLin_wcscMatrix_apply]
    have hdiag : ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (α r - α s)) : ℂ)
        = ∑ s, x r * (starRingEnd ℂ) (x s) * (wcscKernel α δ r s : ℂ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      simp only [wcscKernel, cscKernel_self, mul_zero, Complex.ofReal_zero, zero_add]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hxu r, hxu s]
      simp only [cscKernel, map_mul, Complex.conj_ofReal, div_eq_mul_inv, hwdef]
      push_cast
      ring
    rw [hdiag]
    have hx : ∀ i, xe.ofLp i = x i := fun i => rfl
    simp only [RCLike.inner_apply, map_mul, map_sum, Complex.conj_I, Complex.conj_ofReal, hx]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    linear_combination (x r * (starRingEnd ℂ) (x s) * (wcscKernel α δ r s : ℂ)) * Complex.I_sq
  rw [hform, norm_mul, Complex.norm_I, one_mul, ← hxe]
  calc ‖inner ℂ (T xe) xe‖ ≤ ‖T xe‖ * ‖xe‖ := norm_inner_le_norm _ _
    _ ≤ 5 * Real.sqrt 2 / Real.pi * ‖xe‖ * ‖xe‖ :=
        mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = 5 * Real.sqrt 2 / Real.pi * ‖xe‖ ^ 2 := by ring

/-- **The weighted cosecant inequality** (constant `5 √2 / π`).  For real `α_r`, weights
`δ_r > 0` with `δ_r ≤ intDist (α_r − α_s)` for every `s ≠ r`, and complex `u_r`,
`|∑_{r ≠ s} u_r conj(u_s) / sin π(α_r − α_s)| ≤ (5 √2 / π) ∑_r |u_r|² / δ_r`.
Montgomery and Vaughan's constant is `3/2`; `5 √2 / π ≈ 2.251`. -/
theorem weightedCosecantInequality {n : ℕ} (α δ : Fin n → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s : Fin n, r ≠ s → δ r ≤ intDist (α r - α s)) (u : Fin n → ℂ) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (α r - α s)) : ℂ)‖
      ≤ 5 * Real.sqrt 2 / Real.pi * ∑ r, ‖u r‖ ^ 2 / δ r := by
  by_cases h1 : ∀ r, δ r ≤ 1
  · exact weightedCosecantInequality_aux α δ hδ h1 hsep u
  push Not at h1
  obtain ⟨r0, hr0⟩ := h1
  -- a single point: every `s ≠ r0` would force `δ r0 ≤ 1/2`
  have hall : ∀ s, s = r0 := by
    intro s
    by_contra hs
    have := (hsep r0 s (Ne.symm hs)).trans (intDist_le_half _)
    linarith
  have hzero : ∑ r, ∑ s ∈ Finset.univ.erase r,
      u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (α r - α s)) : ℂ) = 0 := by
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s hs => ?_
    exact absurd ((hall s).trans (hall r).symm) (Finset.ne_of_mem_erase hs)
  rw [hzero, norm_zero]
  have : 0 ≤ ∑ r, ‖u r‖ ^ 2 / δ r :=
    Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (hδ r).le
  positivity

/-- **The weighted cosecant inequality over a finite set** of an arbitrary index type. -/
theorem weightedCosecantInequality_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t δ : ι → ℝ) (x : ι → ℂ) (hδ : ∀ i ∈ s, 0 < δ i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i ≤ intDist (t i - t j)) :
    ‖∑ i ∈ s, ∑ j ∈ s.erase i,
        x i * (starRingEnd ℂ) (x j) / (Real.sin (Real.pi * (t i - t j)) : ℂ)‖
      ≤ 5 * Real.sqrt 2 / Real.pi * ∑ i ∈ s, ‖x i‖ ^ 2 / δ i := by
  set e := s.equivFin
  set α : Fin s.card → ℝ := fun k => t (e.symm k) with hα
  set d : Fin s.card → ℝ := fun k => δ (e.symm k) with hd
  set u : Fin s.card → ℂ := fun k => x (e.symm k) with hu
  have hre : ∀ {M : Type} [AddCommMonoid M] (g : ι → M),
      ∑ i ∈ s, g i = ∑ k, g (e.symm k) := by
    intro M _ g
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp e.symm (fun i => g i)).symm
  have hsepα : ∀ r q : Fin s.card, r ≠ q → d r ≤ intDist (α r - α q) := by
    intro r q hrq
    exact hsep _ (e.symm r).2 _ (e.symm q).2 (fun h => hrq (e.symm.injective (Subtype.ext h)))
  have hmain := weightedCosecantInequality α d (fun k => hδ _ (e.symm k).2) hsepα u
  set F : ι → ι → ℂ := fun i j =>
    x i * (starRingEnd ℂ) (x j) / (Real.sin (Real.pi * (t i - t j)) : ℂ) with hF
  have hdiag : ∀ i, F i i = 0 := fun i => by simp [hF]
  have hL : ∑ i ∈ s, ∑ j ∈ s.erase i, F i j
      = ∑ r, ∑ q ∈ Finset.univ.erase r,
          u r * (starRingEnd ℂ) (u q) / (Real.sin (Real.pi * (α r - α q)) : ℂ) := by
    have h1 : ∑ i ∈ s, ∑ j ∈ s.erase i, F i j = ∑ i ∈ s, ∑ j ∈ s, F i j :=
      Finset.sum_congr rfl fun i _ => Finset.sum_erase s (hdiag i)
    have h2 : ∀ r : Fin s.card, ∑ q ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u q) / (Real.sin (Real.pi * (α r - α q)) : ℂ)
        = ∑ q, F (e.symm r) (e.symm q) :=
      fun r => Finset.sum_erase _ (by simp [hu, hα])
    rw [h1, Finset.sum_congr rfl fun r _ => h2 r, hre]
    exact Finset.sum_congr rfl fun r _ => hre _
  have hR : ∑ r, ‖u r‖ ^ 2 / d r = ∑ i ∈ s, ‖x i‖ ^ 2 / δ i :=
    (hre (fun i => ‖x i‖ ^ 2 / δ i)).symm
  rw [hL, ← hR]
  exact hmain

end HilbertCosecantWeighted

end RiemannHypothesis
