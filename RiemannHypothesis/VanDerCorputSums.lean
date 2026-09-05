/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib
import RiemannHypothesis.KusminLandau

/-!
# van der Corput's second-derivative test for exponential sums

`RiemannHypothesis.KusminLandau` proves the *first*-derivative test for exponential sums: if the
phase `f` has a monotone derivative that stays at distance at least `λ` from every integer, then
`‖∑ e(f n)‖ ≤ 1 + 2/λ`, with no dependence on the number of terms.  That hypothesis is very strong:
it fails as soon as `f'` crosses an integer, which for a phase with a genuinely varying derivative
it does repeatedly.

This file removes the hypothesis, at the price of a bound that grows with the range.  The classical
statement, van der Corput's *second*-derivative test, is: if `f'' ≍ r` on an interval of length `N`,
then

`‖∑_{n} e(f n)‖ ≪ N √r + 1/√r`.

The proof is the classical one, and is exactly the combination of the two ingredients the open
boundaries of `M1-KUSMIN-LANDAU` and `M1-VAN-DER-CORPUT` named as missing: split the range of
summation according to the position of `f'` relative to the integers.  Where `f'` is at distance at
least `λ` from every integer, Kusmin–Landau applies and contributes `1 + 2/λ`; where `f'` is within
`λ` of an integer, `f'` moves at speed at least `r`, so at most `2λ/r + 1` integers are involved
and the terms are counted trivially.  Each such block is indexed by the integer nearest to `f'`, of
which there are at most (the total variation of `f'`) `+ 2`; and `λ = √r/2` balances the two.

## Main results

* `norm_sum_e2pi_le_of_grow` — the bound with the separation parameter `λ` left free:

      ‖∑_{j < L} e(f (a + j))‖ ≤ 2 (V + 2) ((1 + 2/λ) + (2λ/r + 1)),

  where `V = f'(a + L) − f'(a)` is the total variation of the derivative, under the hypothesis
  that `f'` increases at speed at least `r`.
* `norm_sum_e2pi_le_of_grow_sqrt` — the balanced choice `λ = √r/2`, giving `2 (V + 2) (2 + 5/√r)`.
* `norm_sum_e2pi_le_of_deriv_two` — **the second-derivative test**: if `r ≤ f'' ≤ R` on
  `[a, a + L]` with `0 < r ≤ 1`, then

      ‖∑_{j < L} e(f (a + j))‖ ≤ 2 (R L + 2) (2 + 5/√r).

  For `R ≍ r` this is the classical `≪ L √r + 1/√r`, the exponent pair `(1/2, 1/2)`.
* `norm_sum_e2pi_le_of_deriv_two_neg` — the same bound for a *decreasing* derivative,
  `−R ≤ f'' ≤ −r`, obtained by conjugating every term.
* `norm_sum_e2pi_logPhase_le` — the worked instance of the phase of `ζ`, `f(x) = −(τ/2π) log x`,
  on a dyadic block `[N, 2N]`.

Nothing here is claimed about `ζ` itself: no subconvexity bound, no approximate functional
equation, no density estimate.  The constants are not optimized.

## Implementation notes

The blocks are produced not by an induction that peels maximal runs, but by a classification map
`cls`: the index `j` is sent to the pair consisting of the integer `k = ⌊f'(a + j) + λ⌋` and the
Boolean recording whether `f'(a + j) ≥ k + λ`.  Since `λ ≤ 1/2`, the sets `[k − λ, k + λ)` and
`[k + λ, k + 1 − λ)` tile the line, so this is exactly the classification "near the integer `k`" /
"in the good window to the right of `k`", and `Finset.sum_fiberwise_of_maps_to` splits the sum
along it.  Monotonicity of `f'` makes each fibre an interval of indices (`cls_eq_of_between`),
which is what allows Kusmin–Landau — a statement about a contiguous block — to be applied to it.
-/

noncomputable section

open Complex Real Finset

namespace RiemannHypothesis

namespace VanDerCorputSums

open KusminLandau

variable {f g : ℝ → ℝ} {a lam r : ℝ} {L : ℕ}

/-! ## The classification of the indices -/

open Classical in
/-- The class of the index `j`: the integer `k = ⌊g (a + j) + λ⌋`, together with the Boolean
recording whether `g (a + j)` lies in the *good* window `[k + λ, k + 1 − λ)` (`true`) or in the
*bad* window `[k − λ, k + λ)` (`false`).  For `0 < λ ≤ 1/2` these two windows, over all integers
`k`, tile the real line. -/
def cls (g : ℝ → ℝ) (a lam : ℝ) (j : ℕ) : ℤ × Bool :=
  (⌊g (a + j) + lam⌋, decide ((⌊g (a + j) + lam⌋ : ℝ) + lam ≤ g (a + j)))

lemma cls_fst (g : ℝ → ℝ) (a lam : ℝ) (j : ℕ) :
    (cls g a lam j).1 = ⌊g (a + j) + lam⌋ := rfl

lemma cls_snd_iff {g : ℝ → ℝ} {a lam : ℝ} {j : ℕ} :
    (cls g a lam j).2 = true ↔ ((cls g a lam j).1 : ℝ) + lam ≤ g (a + j) := by
  simp [cls]

/-- The lower bound on `g (a + j)` implied by the value of the first coordinate of its class. -/
lemma cls_le (g : ℝ → ℝ) (a lam : ℝ) (j : ℕ) :
    ((cls g a lam j).1 : ℝ) - lam ≤ g (a + j) := by
  have := Int.floor_le (g (a + j) + lam)
  rw [cls_fst]
  linarith

/-- The upper bound on `g (a + j)` implied by the value of the first coordinate of its class. -/
lemma lt_cls (g : ℝ → ℝ) (a lam : ℝ) (j : ℕ) :
    g (a + j) < ((cls g a lam j).1 : ℝ) + 1 - lam := by
  have := Int.lt_floor_add_one (g (a + j) + lam)
  rw [cls_fst]
  linarith

/-- **The fibres of `cls` are intervals**: if `i` and `m` have the same class and the value of `g`
at `j` lies between its values at `i` and at `m`, then `j` has that class too. -/
lemma cls_eq_of_between (hlam : 0 < lam) {i j m : ℕ}
    (hij : g (a + i) ≤ g (a + j)) (hjm : g (a + j) ≤ g (a + m))
    (him : cls g a lam i = cls g a lam m) :
    cls g a lam j = cls g a lam i := by
  set k : ℤ := (cls g a lam i).1 with hk
  have hkm : (cls g a lam m).1 = k := by rw [hk, him]
  have hi1 := cls_le g a lam i
  have hi2 := lt_cls g a lam i
  have hm1 := cls_le g a lam m
  have hm2 := lt_cls g a lam m
  rw [hkm] at hm1 hm2
  rw [← hk] at hi1 hi2
  -- in both cases the value at `j` lies in a window of length `< 1` around `k`
  rcases hb : (cls g a lam i).2 with _ | _
  · -- the bad window `[k − λ, k + λ)`
    have hmfalse : (cls g a lam m).2 = false := by rw [← him]; exact hb
    have hmlt : g (a + m) < (k : ℝ) + lam := by
      by_contra hcon
      push Not at hcon
      have : (cls g a lam m).2 = true := cls_snd_iff.mpr (by rw [hkm]; linarith)
      rw [hmfalse] at this
      exact Bool.noConfusion this
    have hfl : ⌊g (a + j) + lam⌋ = k := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith
    have hsnd : (cls g a lam j).2 = false := by
      by_contra hcon
      have h1 : (cls g a lam j).2 = true := by
        cases h : (cls g a lam j).2 with
        | false => exact absurd h hcon
        | true => rfl
      have := cls_snd_iff.mp h1
      rw [cls_fst, hfl] at this
      linarith
    refine Prod.ext ?_ ?_
    · rw [cls_fst, hfl, hk]
    · rw [hsnd, hb]
  · -- the good window `[k + λ, k + 1 − λ)`
    have hige : (k : ℝ) + lam ≤ g (a + i) := by
      have := cls_snd_iff.mp hb
      rw [← hk] at this
      exact this
    have hfl : ⌊g (a + j) + lam⌋ = k := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith
    have hsnd : (cls g a lam j).2 = true := by
      refine cls_snd_iff.mpr ?_
      rw [cls_fst, hfl]
      linarith
    refine Prod.ext ?_ ?_
    · rw [cls_fst, hfl, hk]
    · rw [hsnd, hb]

/-! ## Monotonicity of the derivative -/

/-- A sample point lies in the interval of definition. -/
lemma mem_Icc_sample (a : ℝ) {L j : ℕ} (hj : j ≤ L) :
    a + (j : ℝ) ∈ Set.Icc a (a + (L : ℝ)) := by
  have hjL : (j : ℝ) ≤ (L : ℝ) := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  exact ⟨by linarith, by linarith⟩

variable (hr : 0 < r)
  (hgrow : ∀ x ∈ Set.Icc a (a + (L : ℝ)), ∀ y ∈ Set.Icc a (a + (L : ℝ)), x ≤ y →
    r * (y - x) ≤ g y - g x)

include hr hgrow

/-- A derivative that increases at speed at least `r > 0` is monotone. -/
lemma monotoneOn_of_grow : MonotoneOn g (Set.Icc a (a + (L : ℝ))) := by
  intro x hx y hy hxy
  have h := hgrow x hx y hy hxy
  nlinarith [sub_nonneg.mpr hxy]

/-- Monotonicity along the sample points. -/
lemma sample_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L) : g (a + i) ≤ g (a + j) := by
  refine monotoneOn_of_grow hr hgrow (mem_Icc_sample a (hij.trans hj)) (mem_Icc_sample a hj) ?_
  have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  linarith

omit hr in
/-- The values of `g` at the sample points separate at speed at least `r`. -/
lemma sample_gap {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L) :
    r * ((j : ℝ) - (i : ℝ)) ≤ g (a + j) - g (a + i) := by
  have hle : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have h := hgrow _ (mem_Icc_sample a (hij.trans hj)) _ (mem_Icc_sample a hj) (by linarith)
  have hrw : a + (j : ℝ) - (a + (i : ℝ)) = (j : ℝ) - (i : ℝ) := by ring
  rwa [hrw] at h

omit hr hgrow

/-! ## The bound on a single fibre -/

/-- **Each fibre of the classification contributes a bounded amount.**  A fibre in which `g` is at
distance at least `λ` from every integer is bounded by Kusmin–Landau, one in which `g` is within
`λ` of an integer contains at most `2λ/r + 1` indices and is bounded trivially. -/
theorem norm_fiber_sum_le (hr : 0 < r) (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt f (g x) x)
    (hgrow : ∀ x ∈ Set.Icc a (a + (L : ℝ)), ∀ y ∈ Set.Icc a (a + (L : ℝ)), x ≤ y →
      r * (y - x) ≤ g y - g x)
    (p : ℤ × Bool) :
    ‖∑ j ∈ (range L).filter (fun j => cls g a lam j = p), e2pi (f (a + j))‖
      ≤ (1 + 2 / lam) + (2 * lam / r + 1) := by
  classical
  set F := (range L).filter (fun j => cls g a lam j = p) with hFdef
  have hMnn : (0 : ℝ) ≤ (1 + 2 / lam) + (2 * lam / r + 1) := by positivity
  rcases F.eq_empty_or_nonempty with hemp | hne
  · rw [hemp]
    simpa using hMnn
  set q := F.min' hne with hq
  set m := F.max' hne with hm
  have hqF : q ∈ F := F.min'_mem hne
  have hmF : m ∈ F := F.max'_mem hne
  have hqm : q ≤ m := F.min'_le m hmF
  have hmL : m < L := mem_range.mp (mem_filter.mp hmF).1
  have hclsq : cls g a lam q = p := (mem_filter.mp hqF).2
  have hclsm : cls g a lam m = p := (mem_filter.mp hmF).2
  -- the fibre is the interval of indices from `q` to `m`
  have hFeq : F = Finset.Icc q m := by
    ext j
    constructor
    · intro hj
      exact Finset.mem_Icc.mpr ⟨F.min'_le j hj, F.le_max' j hj⟩
    · intro hj
      rw [Finset.mem_Icc] at hj
      have hjL : j < L := lt_of_le_of_lt hj.2 hmL
      refine mem_filter.mpr ⟨mem_range.mpr hjL, ?_⟩
      have h1 : g (a + q) ≤ g (a + j) := sample_mono hr hgrow hj.1 hjL.le
      have h2 : g (a + j) ≤ g (a + m) := sample_mono hr hgrow hj.2 hmL.le
      have := cls_eq_of_between hlam h1 h2 (hclsq.trans hclsm.symm)
      rw [this, hclsq]
  -- rewrite the sum as a sum over an initial segment
  have hsum : ∑ j ∈ F, e2pi (f (a + j))
      = ∑ i ∈ range (m - q + 1), e2pi (f ((a + (q : ℝ)) + i)) := by
    rw [hFeq, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    have hlen : m + 1 - q = m - q + 1 := by omega
    rw [hlen]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    push_cast
    ring
  rw [hsum]
  -- the two cases
  rcases hp2 : p.2 with _ | _
  · -- bad window: at most `2λ/r + 1` terms, each of modulus one
    have hqlow : ((p.1 : ℝ)) - lam ≤ g (a + q) := by
      have := cls_le g a lam q
      rwa [hclsq] at this
    have hmhigh : g (a + m) < (p.1 : ℝ) + lam := by
      by_contra hcon
      push Not at hcon
      have : (cls g a lam m).2 = true := cls_snd_iff.mpr (by rw [hclsm]; linarith)
      rw [hclsm, hp2] at this
      exact Bool.noConfusion this
    have hgap := sample_gap hgrow hqm hmL.le
    have hlt : ((m : ℝ) - (q : ℝ)) < 2 * lam / r := by
      rw [lt_div_iff₀ hr, mul_comm]
      linarith
    have hcard : ((m - q + 1 : ℕ) : ℝ) ≤ 2 * lam / r + 1 := by
      have hcast : ((m - q : ℕ) : ℝ) = (m : ℝ) - (q : ℝ) := by
        have : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hqm
        push_cast [Nat.cast_sub hqm]
        ring
      push_cast
      rw [hcast]
      linarith
    calc ‖∑ i ∈ range (m - q + 1), e2pi (f ((a + (q : ℝ)) + i))‖
        ≤ ∑ i ∈ range (m - q + 1), ‖e2pi (f ((a + (q : ℝ)) + i))‖ := norm_sum_le _ _
      _ = ((m - q + 1 : ℕ) : ℝ) := by simp
      _ ≤ 2 * lam / r + 1 := hcard
      _ ≤ (1 + 2 / lam) + (2 * lam / r + 1) := by
          have : (0 : ℝ) ≤ 1 + 2 / lam := by positivity
          linarith
  · -- good window: Kusmin–Landau
    have hqge : (p.1 : ℝ) + lam ≤ g (a + q) := by
      have := cls_snd_iff.mp (by rw [hclsq, hp2])
      rwa [hclsq] at this
    have hmlt : g (a + m) < (p.1 : ℝ) + 1 - lam := by
      have := lt_cls g a lam m
      rwa [hclsm] at this
    have hcast : ((m - q : ℕ) : ℝ) = (m : ℝ) - (q : ℝ) := by
      push_cast [Nat.cast_sub hqm]
      ring
    have hsub : Set.Icc (a + (q : ℝ)) (a + (q : ℝ) + ((m - q : ℕ) : ℝ))
        ⊆ Set.Icc a (a + (L : ℝ)) := by
      intro x hx
      rw [Set.mem_Icc] at hx ⊢
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      have hmL' : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hmL.le
      rw [hcast] at hx
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    have hg_between : ∀ x ∈ Set.Icc (a + (q : ℝ)) (a + (q : ℝ) + ((m - q : ℕ) : ℝ)),
        g (a + q) ≤ g x ∧ g x ≤ g (a + m) := by
      intro x hx
      have hx' := hx
      rw [Set.mem_Icc, hcast] at hx'
      have hxmem : x ∈ Set.Icc a (a + (L : ℝ)) := hsub hx
      have hqmem : a + (q : ℝ) ∈ Set.Icc a (a + (L : ℝ)) :=
        mem_Icc_sample a (le_of_lt (lt_of_le_of_lt hqm hmL))
      have hmmem : a + (m : ℝ) ∈ Set.Icc a (a + (L : ℝ)) := mem_Icc_sample a hmL.le
      refine ⟨monotoneOn_of_grow hr hgrow hqmem hxmem (by linarith [hx'.1]),
        monotoneOn_of_grow hr hgrow hxmem hmmem (by linarith [hx'.2])⟩
    have hKL := KusminLandau.norm_sum_e2pi_le_of_deriv_sub_int
      (K := m - q) (lam := lam) (c := a + (q : ℝ)) (k := p.1) (f := f) (f' := g) hlam
      (fun x hx => hf x (hsub hx))
      (fun x hx => le_trans hqge (hg_between x hx).1)
      (fun x hx => le_trans (hg_between x hx).2 (le_of_lt hmlt))
      (Or.inl fun x hx y hy hxy =>
        monotoneOn_of_grow hr hgrow (hsub hx) (hsub hy) hxy)
    refine le_trans hKL ?_
    have : (0 : ℝ) ≤ 2 * lam / r + 1 := by positivity
    linarith

/-! ## The main estimate -/

/-- **van der Corput's second-derivative test for sums, with the separation `λ` free.**  If the
derivative `g = f'` increases at speed at least `r > 0` on `[a, a + L]`, then

`‖∑_{j < L} e(f (a + j))‖ ≤ 2 (V + 2) ((1 + 2/λ) + (2λ/r + 1))`,

where `V = g (a + L) − g a` is the total variation of the derivative. -/
theorem norm_sum_e2pi_le_of_grow (hr : 0 < r) (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt f (g x) x)
    (hgrow : ∀ x ∈ Set.Icc a (a + (L : ℝ)), ∀ y ∈ Set.Icc a (a + (L : ℝ)), x ≤ y →
      r * (y - x) ≤ g y - g x) :
    ‖∑ j ∈ range L, e2pi (f (a + j))‖
      ≤ 2 * ((g (a + (L : ℝ)) - g a) + 2) * ((1 + 2 / lam) + (2 * lam / r + 1)) := by
  classical
  set M : ℝ := (1 + 2 / lam) + (2 * lam / r + 1) with hM
  have hMnn : (0 : ℝ) ≤ M := by positivity
  set P := (range L).image (cls g a lam) with hP
  have hmaps : ∀ j ∈ range L, cls g a lam j ∈ P := fun j hj => Finset.mem_image_of_mem _ hj
  -- the classes that occur have first coordinate between two floors
  set k0 : ℤ := ⌊g a + lam⌋ with hk0
  set k1 : ℤ := ⌊g (a + (L : ℝ)) + lam⌋ with hk1
  have hPsub : P ⊆ (Finset.Icc k0 k1) ×ˢ (Finset.univ : Finset Bool) := by
    intro p hp
    rw [hP, Finset.mem_image] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    have hjL : j < L := mem_range.mp hj
    have h1 : g a ≤ g (a + j) := by
      have := sample_mono hr hgrow (Nat.zero_le j) hjL.le
      simpa using this
    have h2 : g (a + j) ≤ g (a + (L : ℝ)) := by
      have := sample_mono (L := L) hr hgrow hjL.le le_rfl
      simpa using this
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · rw [cls_fst, hk0]
      exact Int.floor_le_floor (by linarith)
    · rw [cls_fst, hk1]
      exact Int.floor_le_floor (by linarith)
  have hk01 : k0 ≤ k1 := by
    have h : g a ≤ g (a + (L : ℝ)) := by
      have := sample_mono (i := 0) (j := L) (L := L) hr hgrow (Nat.zero_le L) le_rfl
      simpa using this
    exact Int.floor_le_floor (by linarith)
  have hcardP : (P.card : ℝ) ≤ 2 * ((g (a + (L : ℝ)) - g a) + 2) := by
    have h1 : P.card ≤ ((Finset.Icc k0 k1) ×ˢ (Finset.univ : Finset Bool)).card :=
      Finset.card_le_card hPsub
    have h2 : ((Finset.Icc k0 k1) ×ˢ (Finset.univ : Finset Bool)).card
        = (k1 + 1 - k0).toNat * 2 := by
      rw [Finset.card_product, Int.card_Icc]
      simp
    have h3 : (((k1 + 1 - k0).toNat : ℤ) : ℝ) ≤ (g (a + (L : ℝ)) - g a) + 2 := by
      rw [Int.toNat_of_nonneg (by omega)]
      have hle : (k1 : ℝ) ≤ g (a + (L : ℝ)) + lam := Int.floor_le _
      have hgt : (g a + lam) - 1 < (k0 : ℝ) := by
        have := Int.lt_floor_add_one (g a + lam)
        rw [← hk0] at this
        linarith
      push_cast
      linarith
    calc (P.card : ℝ) ≤ (((k1 + 1 - k0).toNat * 2 : ℕ) : ℝ) := by
          exact_mod_cast h2 ▸ (Nat.cast_le.mpr h1)
      _ = ((k1 + 1 - k0).toNat : ℝ) * 2 := by push_cast; ring
      _ ≤ ((g (a + (L : ℝ)) - g a) + 2) * 2 := by
          have : (((k1 + 1 - k0).toNat : ℤ) : ℝ) = ((k1 + 1 - k0).toNat : ℝ) := by push_cast; ring
          nlinarith [h3, this]
      _ = 2 * ((g (a + (L : ℝ)) - g a) + 2) := by ring
  calc ‖∑ j ∈ range L, e2pi (f (a + j))‖
      = ‖∑ p ∈ P, ∑ j ∈ (range L).filter (fun j => cls g a lam j = p), e2pi (f (a + j))‖ := by
        rw [Finset.sum_fiberwise_of_maps_to hmaps]
    _ ≤ ∑ p ∈ P, ‖∑ j ∈ (range L).filter (fun j => cls g a lam j = p), e2pi (f (a + j))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p ∈ P, M :=
        Finset.sum_le_sum fun p _ => norm_fiber_sum_le hr hlam hf hgrow p
    _ = (P.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * ((g (a + (L : ℝ)) - g a) + 2) * M := by
        exact mul_le_mul_of_nonneg_right hcardP hMnn

/-- **The balanced choice `λ = √r/2`**: for `0 < r ≤ 1`,

`‖∑_{j < L} e(f (a + j))‖ ≤ 2 (V + 2) (2 + 5/√r)`. -/
theorem norm_sum_e2pi_le_of_grow_sqrt (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt f (g x) x)
    (hgrow : ∀ x ∈ Set.Icc a (a + (L : ℝ)), ∀ y ∈ Set.Icc a (a + (L : ℝ)), x ≤ y →
      r * (y - x) ≤ g y - g x) :
    ‖∑ j ∈ range L, e2pi (f (a + j))‖
      ≤ 2 * ((g (a + (L : ℝ)) - g a) + 2) * (2 + 5 / Real.sqrt r) := by
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsq1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr hr1
  have hsqsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  set lam : ℝ := Real.sqrt r / 2 with hlamdef
  have hlam : 0 < lam := by positivity
  have hmain := norm_sum_e2pi_le_of_grow (lam := lam) hr hlam hf hgrow
  refine hmain.trans ?_
  have hval : (1 + 2 / lam) + (2 * lam / r + 1) = 2 + 5 / Real.sqrt r := by
    rw [hlamdef]
    field_simp
    nlinarith [hsqsq, hsq]
  rw [hval]

/-! ## The second-derivative form -/

/-- **van der Corput's second-derivative test for exponential sums.**  If `f'' ` exists on
`[a, a + L]` and satisfies `0 < r ≤ f'' ≤ R` there, with `r ≤ 1`, then

`‖∑_{j < L} e(f (a + j))‖ ≤ 2 (R L + 2) (2 + 5/√r)`.

For `R` comparable to `r` this is the classical `≪ L √r + 1/√r`, the exponent pair `(1/2, 1/2)`.
No consequence for `ζ` is claimed. -/
theorem norm_sum_e2pi_le_of_deriv_two {g' : ℝ → ℝ} {R : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt g (g' x) x)
    (hlb : ∀ x ∈ Set.Icc a (a + (L : ℝ)), r ≤ g' x)
    (hub : ∀ x ∈ Set.Icc a (a + (L : ℝ)), g' x ≤ R) :
    ‖∑ j ∈ range L, e2pi (f (a + j))‖ ≤ 2 * (R * L + 2) * (2 + 5 / Real.sqrt r) := by
  -- the mean value theorem turns the bounds on `g'` into two-sided control of the increments
  have hslope : ∀ x ∈ Set.Icc a (a + (L : ℝ)), ∀ y ∈ Set.Icc a (a + (L : ℝ)), x ≤ y →
      r * (y - x) ≤ g y - g x ∧ g y - g x ≤ R * (y - x) := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · simp
    · have hsub : Set.Icc x y ⊆ Set.Icc a (a + (L : ℝ)) := by
        intro z hz
        rw [Set.mem_Icc] at hz
        exact ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
      obtain ⟨c, hc, hcv⟩ :=
        exists_hasDerivAt_eq_slope g g' hlt
          (fun z hz => ((hg z (hsub hz)).continuousAt).continuousWithinAt)
          (fun z hz => hg z (hsub (Set.Ioo_subset_Icc_self hz)))
      have hcmem : c ∈ Set.Icc a (a + (L : ℝ)) := hsub (Set.Ioo_subset_Icc_self hc)
      have hpos : 0 < y - x := by linarith
      have h1 : r ≤ (g y - g x) / (y - x) := by rw [← hcv]; exact hlb c hcmem
      have h2 : (g y - g x) / (y - x) ≤ R := by rw [← hcv]; exact hub c hcmem
      rw [le_div_iff₀ hpos] at h1
      rw [div_le_iff₀ hpos] at h2
      exact ⟨by linarith, by linarith⟩
  have hgrow : ∀ x ∈ Set.Icc a (a + (L : ℝ)), ∀ y ∈ Set.Icc a (a + (L : ℝ)), x ≤ y →
      r * (y - x) ≤ g y - g x := fun x hx y hy hxy => (hslope x hx y hy hxy).1
  have hmain := norm_sum_e2pi_le_of_grow_sqrt hr hr1 hf hgrow
  refine hmain.trans ?_
  have hVle : g (a + (L : ℝ)) - g a ≤ R * L := by
    have hmem0 : a ∈ Set.Icc a (a + (L : ℝ)) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      exact ⟨le_rfl, by linarith⟩
    have hmemL : a + (L : ℝ) ∈ Set.Icc a (a + (L : ℝ)) := mem_Icc_sample a (le_refl L)
    have h := (hslope a hmem0 (a + (L : ℝ)) hmemL (by
      have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith)).2
    have hrw : a + (L : ℝ) - a = (L : ℝ) := by ring
    rwa [hrw] at h
  have hpos : (0 : ℝ) < 2 + 5 / Real.sqrt r := by
    have : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    positivity
  have h2 : 2 * ((g (a + (L : ℝ)) - g a) + 2) ≤ 2 * (R * L + 2) := by linarith
  exact mul_le_mul_of_nonneg_right h2 hpos.le

/-- `e(−θ)` is the complex conjugate of `e(θ)`. -/
lemma e2pi_neg (theta : ℝ) : e2pi (-theta) = (starRingEnd ℂ) (e2pi theta) := by
  rw [e2pi, e2pi, ← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

/-- **The second-derivative test for a decreasing derivative.**  If `f'' ≤ −r < 0` and
`f'' ≥ −R` on `[a, a + L]`, with `r ≤ 1`, the same bound holds: replacing `f` by `−f`
conjugates every term and so leaves the norm of the sum unchanged. -/
theorem norm_sum_e2pi_le_of_deriv_two_neg {g' : ℝ → ℝ} {R : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a (a + (L : ℝ)), HasDerivAt g (g' x) x)
    (hlb : ∀ x ∈ Set.Icc a (a + (L : ℝ)), -R ≤ g' x)
    (hub : ∀ x ∈ Set.Icc a (a + (L : ℝ)), g' x ≤ -r) :
    ‖∑ j ∈ range L, e2pi (f (a + j))‖ ≤ 2 * (R * L + 2) * (2 + 5 / Real.sqrt r) := by
  have h := norm_sum_e2pi_le_of_deriv_two (f := fun x => -f x) (g := fun x => -g x)
    (g' := fun x => -g' x) (r := r) (R := R) hr hr1
    (fun x hx => (hf x hx).neg) (fun x hx => (hg x hx).neg)
    (fun x hx => by simpa using neg_le_neg (hub x hx))
    (fun x hx => by simpa using neg_le_neg (hlb x hx))
  refine le_trans (le_of_eq ?_) h
  have hsum : ∑ j ∈ range L, e2pi (-f (a + j))
      = (starRingEnd ℂ) (∑ j ∈ range L, e2pi (f (a + j))) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => e2pi_neg _
  rw [hsum, RCLike.norm_conj]

/-! ## The worked instance: the phase of `ζ` on a dyadic block -/

/-- **The second-derivative test for the phase of `ζ`.**  For the phase `f (x) = −(t/2π) log x`,
whose exponential is `x^(-i t)`, summed over the dyadic block `[N, 2N)`:

`‖∑_{j < N} (N + j)^(-i t)‖ ≤ 2 (t/(2πN) + 2) (2 + 5/√(t/(8πN²)))`.

The second derivative of the phase is `(t/2π)/x²`, which on `[N, 2N]` lies between
`r = t/(8πN²)` and `R = t/(2πN²)`; the hypothesis `t ≤ 8πN²` is exactly `r ≤ 1`.  Nothing is
claimed about `ζ` itself: this is a bound for one block, with no summation over blocks and no
approximate functional equation. -/
theorem norm_sum_e2pi_logPhase_le {N : ℕ} {t : ℝ} (hN : 0 < N) (ht : 0 < t)
    (hts : t ≤ 8 * Real.pi * (N : ℝ) ^ 2) :
    ‖∑ j ∈ range N, e2pi (-(t / (2 * Real.pi)) * Real.log ((N : ℝ) + (j : ℝ)))‖
      ≤ 2 * (t / (2 * Real.pi * (N : ℝ)) + 2)
          * (2 + 5 / Real.sqrt (t / (8 * Real.pi * (N : ℝ) ^ 2))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set c : ℝ := t / (2 * Real.pi) with hc
  have hcpos : 0 < c := by positivity
  set r : ℝ := t / (8 * Real.pi * (N : ℝ) ^ 2) with hrdef
  set R : ℝ := t / (2 * Real.pi * (N : ℝ) ^ 2) with hRdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one (by positivity)]
    exact hts
  -- every point of the block is positive
  have hxpos : ∀ x ∈ Set.Icc (N : ℝ) ((N : ℝ) + (N : ℝ)), 0 < x :=
    fun x hx => lt_of_lt_of_le hN0 hx.1
  have hmain := norm_sum_e2pi_le_of_deriv_two (f := fun x => -c * Real.log x)
    (g := fun x => -c / x) (g' := fun x => c / x ^ 2) (a := (N : ℝ)) (L := N) (r := r) (R := R)
    hrpos hr1 ?_ ?_ ?_ ?_
  · refine hmain.trans_eq ?_
    have hRL : R * (N : ℝ) = t / (2 * Real.pi * (N : ℝ)) := by
      rw [hRdef]
      field_simp
    rw [hRL]
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hxpos x hx)
    have h := (Real.hasDerivAt_log hx0).const_mul (-c)
    convert h using 1
    all_goals try rfl
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hxpos x hx)
    have h := (hasDerivAt_inv hx0).const_mul (-c)
    have hrw : (fun y : ℝ => -c * y⁻¹) = fun y : ℝ => -c / y := by
      funext y; rw [div_eq_mul_inv]
    rw [hrw] at h
    convert h using 1
    all_goals try rfl
    all_goals field_simp
  · intro x hx
    have hxp := hxpos x hx
    have hxle : x ≤ 2 * (N : ℝ) := by have := hx.2; linarith
    have hsq : x ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
    have hexp : c * (8 * Real.pi * (N : ℝ) ^ 2) = 4 * (N : ℝ) ^ 2 * t := by
      rw [hc]; field_simp; ring
    rw [hrdef, div_le_div_iff₀ (by positivity) (by positivity), hexp]
    nlinarith [ht.le, hsq]
  · intro x hx
    have hxp := hxpos x hx
    have hxge : (N : ℝ) ≤ x := hx.1
    have hsq : (N : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
    have hexp : c * (2 * Real.pi * (N : ℝ) ^ 2) = (N : ℝ) ^ 2 * t := by
      rw [hc]; field_simp
    rw [hRdef, div_le_div_iff₀ (by positivity) (by positivity), hexp]
    nlinarith [ht.le, hsq]

end VanDerCorputSums

end RiemannHypothesis
