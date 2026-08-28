/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.KusminLandau

/-!
# van der Corput's A process: Weyl differencing

`RiemannHypothesis.VanDerCorput` proves the first and second derivative tests for exponential
*integrals*, and `RiemannHypothesis.KusminLandau` the first derivative test for exponential *sums*.
Both are useless on their own for a phase that moves *slowly*: the Kusmin–Landau inequality needs
`f'` to stay away from the integers, and there is nothing to be gained when `f'` is tiny.

van der Corput's **A process** — Weyl differencing — is the manoeuvre that removes that
obstruction.  It bounds an exponential sum by the *differenced* sums `∑ e(f(n+k) − f(n))`, whose
phases move `k` times as fast; iterating it, and interleaving it with the B process, is how the
exponent pairs of the theory of `ζ` are produced.

The content of the A process is an inequality about an arbitrary finitely supported sequence of
complex numbers, with no arithmetic in it at all.  That is how it is proved here.

## Main results

With `S = ∑_{0 ≤ n < N} z n` and the correlations `corr z N k = ∑_{0 ≤ n < N} z (n+k) * conj (z n)`,
for a sequence `z : ℤ → ℂ` vanishing outside `[0, N)`:

* `mul_normSq_sum_le` — the **van der Corput inequality**: for every `H ≥ 1`,

      H ‖S‖² ≤ (N + H − 1) · ∑_{|k| < H} ‖corr z N k‖.

  The right-hand side has `2H − 1` terms; the diagonal term `k = 0` is `∑ ‖z n‖²`, so the
  inequality is nontrivial exactly when the correlations at nonzero shifts are small.

* `mul_normSq_sum_le_weighted` — the classical sharper form, with the Fejér weights that the
  double sum really produces:

      H² ‖S‖² ≤ (N + H − 1) · ∑_{|k| < H} (H − |k|) ‖corr z N k‖.

* `norm_sq_sum_e2pi_le` — the arithmetic form, for `z n = e(f n)` on `[0, N)`:

      H ‖∑_{n < N} e(f n)‖² ≤ (N + H − 1) · (N + 2 ∑_{k=1}^{H−1} ‖∑_{n < N−k} e(f(n+k) − f(n))‖).

  This is the shape in which the A process is applied: the inner sums are exponential sums with
  phase `f(·+k) − f(·)`, a difference quotient of `f` times `k`.

## Proof

Three steps, all elementary.

1. *Averaging over shifted windows.*  Because `z` vanishes outside `[0, N)`, every window
   `[n, n+H)` with `n` in `I = [1−H, N)` sees the whole of `S` after summation:
   `∑_{n ∈ I} B n = H · S`, where `B n = ∑_{h < H} z (n + h)` is the block sum.

2. *Cauchy–Schwarz*, in the form `(∑_{n ∈ I} ‖B n‖)² ≤ #I · ∑_{n ∈ I} ‖B n‖²`, with
   `#I = N + H − 1`.

3. *Expanding the square.*  `∑_{n ∈ I} ‖B n‖² = ∑_{h₁, h₂ < H} corr z N (h₁ − h₂)`, since for
   fixed `h₁, h₂` the substitution `m = n + h₂` turns the inner sum into a correlation.  Bounding
   each of the `H²` terms by the norm of the corresponding correlation, and counting how often the
   shift `k` occurs — at most `H` times for the unweighted form, exactly `H − |k|` times for the
   weighted one — gives the two statements.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace WeylDifferencing

variable {N H : ℕ} {z : ℤ → ℂ}

/-- The block sum `B n = z n + z (n+1) + ⋯ + z (n+H−1)`. -/
def blockSum (z : ℤ → ℂ) (H : ℕ) (n : ℤ) : ℂ := ∑ h ∈ range H, z (n + h)

/-- The correlation of `z` at shift `k`, `∑_{0 ≤ n < N} z (n + k) * conj (z n)`. -/
def corr (z : ℤ → ℂ) (N : ℕ) (k : ℤ) : ℂ :=
  ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z (n + k) * (starRingEnd ℂ) (z n)

/-- A sum over any window containing `[0, N)` of a function supported in `[0, N)` is the sum
over `[0, N)` itself. -/
theorem sum_Ico_eq_of_supported {g : ℤ → ℂ} (hg : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → g n = 0)
    {a b : ℤ} (ha : a ≤ 0) (hb : (N : ℤ) ≤ b) :
    ∑ n ∈ Finset.Ico a b, g n = ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), g n := by
  refine (Finset.sum_subset (Finset.Ico_subset_Ico ha hb) ?_).symm
  intro x _ hx
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hx
  exact hg x hx

/-- The correlation at shift `k` is supported where `conj (z n)` is: the summand vanishes off
`[0, N)`. -/
theorem corr_eq_sum_Ico {k a b : ℤ} (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0)
    (ha : a ≤ 0) (hb : (N : ℤ) ≤ b) :
    ∑ n ∈ Finset.Ico a b, z (n + k) * (starRingEnd ℂ) (z n) = corr z N k :=
  sum_Ico_eq_of_supported (fun n hn => by rw [hz n hn]; simp) ha hb

/-- Step 1: averaging the block sums over the shifted windows recovers `H` copies of the sum. -/
theorem sum_blockSum (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) :
    ∑ n ∈ Finset.Ico (1 - (H : ℤ)) (N : ℤ), blockSum z H n
      = (H : ℂ) * ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n := by
  classical
  simp only [blockSum]
  rw [Finset.sum_comm]
  have key : ∀ h ∈ range H,
      (∑ n ∈ Finset.Ico (1 - (H : ℤ)) (N : ℤ), z (n + h))
        = ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n := by
    intro h hh
    rw [Finset.mem_range] at hh
    rw [Finset.sum_Ico_add' z (1 - (H : ℤ)) (N : ℤ) (h : ℤ)]
    exact sum_Ico_eq_of_supported hz (by omega) (by omega)
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Step 3: expanding the square of a block sum produces the correlations. -/
theorem sum_normSq_blockSum (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) :
    ((∑ n ∈ Finset.Ico (1 - (H : ℤ)) (N : ℤ), ‖blockSum z H n‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ range H ×ˢ range H, corr z N ((p.1 : ℤ) - (p.2 : ℤ)) := by
  classical
  rw [Complex.ofReal_sum]
  have step : ∀ n ∈ Finset.Ico (1 - (H : ℤ)) (N : ℤ),
      ((‖blockSum z H n‖ ^ 2 : ℝ) : ℂ)
        = ∑ p ∈ range H ×ˢ range H, z (n + p.1) * (starRingEnd ℂ) (z (n + p.2)) := by
    intro n _
    have hmul : ((‖blockSum z H n‖ ^ 2 : ℝ) : ℂ)
        = blockSum z H n * (starRingEnd ℂ) (blockSum z H n) := by
      rw [Complex.ofReal_pow]
      exact (RCLike.mul_conj _).symm
    rw [hmul, Finset.sum_product]
    simp only [blockSum, map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  rintro ⟨h₁, h₂⟩ hp
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  have hidx : ∀ n : ℤ, z (n + h₁) * (starRingEnd ℂ) (z (n + h₂))
      = (fun m : ℤ => z (m + ((h₁ : ℤ) - h₂)) * (starRingEnd ℂ) (z m)) (n + h₂) := by
    intro n
    simp only
    ring_nf
  simp only [hidx]
  rw [Finset.sum_Ico_add' (fun m : ℤ => z (m + ((h₁ : ℤ) - h₂)) * (starRingEnd ℂ) (z m))
    (1 - (H : ℤ)) (N : ℤ) (h₂ : ℤ)]
  exact corr_eq_sum_Ico hz (by omega) (by omega)

/-- Counting the shifts: the pair sum is at most `H` times the sum over the shifts. -/
theorem sum_product_norm_corr_le :
    ∑ p ∈ range H ×ˢ range H, ‖corr z N ((p.1 : ℤ) - (p.2 : ℤ))‖
      ≤ (H : ℝ) * ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ‖corr z N k‖ := by
  classical
  rw [Finset.sum_product]
  have key : ∀ h₁ ∈ range H, ∑ h₂ ∈ range H, ‖corr z N ((h₁ : ℤ) - (h₂ : ℤ))‖
      ≤ ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ‖corr z N k‖ := by
    intro h₁ hh₁
    rw [Finset.mem_range] at hh₁
    have hinj : Set.InjOn (fun h₂ : ℕ => (h₁ : ℤ) - (h₂ : ℤ)) (range H) := by
      intro a _ b _ hab
      simp only at hab
      omega
    rw [← Finset.sum_image (f := fun k : ℤ => ‖corr z N k‖) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
    intro k hk
    simp only [Finset.mem_image, Finset.mem_range] at hk
    obtain ⟨h₂, hh₂, rfl⟩ := hk
    simp only [Finset.mem_Ioo]
    omega
  calc ∑ h₁ ∈ range H, ∑ h₂ ∈ range H, ‖corr z N ((h₁ : ℤ) - (h₂ : ℤ))‖
      ≤ ∑ _h₁ ∈ range H, ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ‖corr z N k‖ :=
        Finset.sum_le_sum key
    _ = (H : ℝ) * ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ‖corr z N k‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The exact count of the shifts: among the `H²` pairs `(h₁, h₂)` with `h₁, h₂ < H`, the
difference `h₁ − h₂` takes the value `k` exactly `H − |k|` times. -/
theorem card_filter_sub_eq {k : ℤ} (hk : k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ)) :
    ((range H ×ˢ range H).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = k)).card = H - k.natAbs := by
  classical
  rw [Finset.mem_Ioo] at hk
  have himg : (range H ×ˢ range H).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = k)
      = (range (H - k.natAbs)).image (fun j => (j + k.toNat, j + (-k).toNat)) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      exact ⟨min a b, by omega, by omega, by omega⟩
    · rintro ⟨j, hj, rfl, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  intro x _ y _ hxy
  simpa using congrArg Prod.fst hxy

/-- The pair sum of the correlation norms, with the Fejér weights `H − |k|` it really carries. -/
theorem sum_product_norm_corr_eq :
    ∑ p ∈ range H ×ˢ range H, ‖corr z N ((p.1 : ℤ) - (p.2 : ℤ))‖
      = ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ((H : ℝ) - |k|) * ‖corr z N k‖ := by
  classical
  have hmaps : ∀ p ∈ range H ×ˢ range H,
      ((p.1 : ℤ) - (p.2 : ℤ)) ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ) := by
    rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_Ioo]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps (fun k : ℤ => ‖corr z N k‖)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_const, card_filter_sub_eq hk, nsmul_eq_mul]
  congr 1
  rw [Finset.mem_Ioo] at hk
  have hle : k.natAbs ≤ H := by omega
  have : ((H - k.natAbs : ℕ) : ℝ) = (H : ℝ) - (k.natAbs : ℝ) := by
    rw [Nat.cast_sub hle]
  rw [this]
  congr 1
  rw [← Int.cast_natCast, Int.natCast_natAbs]

/-- **The van der Corput inequality** (the A process, Weyl differencing).  If `z` vanishes
outside `[0, N)` then for every `H ≥ 1`

`H ‖∑ z n‖² ≤ (N + H − 1) ∑_{|k| < H} ‖corr z N k‖`.

The core estimate, before the shifts are counted: Cauchy–Schwarz over the shifted windows,
followed by the expansion of the square. -/
theorem sq_mul_norm_sum_le (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) (hH : 0 < H) :
    ((H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n‖) ^ 2
      ≤ ((N : ℝ) + H - 1) * ∑ p ∈ range H ×ˢ range H, ‖corr z N ((p.1 : ℤ) - (p.2 : ℤ))‖ := by
  classical
  set I : Finset ℤ := Finset.Ico (1 - (H : ℤ)) (N : ℤ) with hI
  have hcard : (I.card : ℝ) = (N : ℝ) + H - 1 := by
    rw [hI, Int.card_Ico]
    have h : ((N : ℤ) - (1 - (H : ℤ))).toNat = N + H - 1 := by omega
    rw [h]
    have h' : 1 ≤ N + H := by omega
    push_cast [Nat.cast_sub h']
    ring
  have h1 : (H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n‖ = ‖∑ n ∈ I, blockSum z H n‖ := by
    rw [hI, sum_blockSum hz, norm_mul]
    simp
  have h4 : ∑ n ∈ I, ‖blockSum z H n‖ ^ 2
      ≤ ∑ p ∈ range H ×ˢ range H, ‖corr z N ((p.1 : ℤ) - (p.2 : ℤ))‖ := by
    calc ∑ n ∈ I, ‖blockSum z H n‖ ^ 2
        = ‖((∑ n ∈ I, ‖blockSum z H n‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ = ‖∑ p ∈ range H ×ˢ range H, corr z N ((p.1 : ℤ) - (p.2 : ℤ))‖ := by
          rw [hI, sum_normSq_blockSum hz]
      _ ≤ ∑ p ∈ range H ×ˢ range H, ‖corr z N ((p.1 : ℤ) - (p.2 : ℤ))‖ := norm_sum_le _ _
  calc ((H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n‖) ^ 2
      = ‖∑ n ∈ I, blockSum z H n‖ ^ 2 := by rw [h1]
    _ ≤ (∑ n ∈ I, ‖blockSum z H n‖) ^ 2 := by
        have hle := norm_sum_le I (blockSum z H)
        have h0 : (0 : ℝ) ≤ ‖∑ n ∈ I, blockSum z H n‖ := norm_nonneg _
        nlinarith
    _ ≤ (I.card : ℝ) * ∑ n ∈ I, ‖blockSum z H n‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ ((N : ℝ) + H - 1) * ∑ p ∈ range H ×ˢ range H, ‖corr z N ((p.1 : ℤ) - (p.2 : ℤ))‖ := by
        rw [hcard]
        have hpos : (0 : ℝ) ≤ (N : ℝ) + H - 1 := by
          have h1H : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
          have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith
        exact mul_le_mul_of_nonneg_left h4 hpos

/-- **The van der Corput inequality** (the A process, Weyl differencing).  If `z` vanishes
outside `[0, N)` then for every `H ≥ 1`

`H ‖∑ z n‖² ≤ (N + H − 1) ∑_{|k| < H} ‖corr z N k‖`. -/
theorem mul_normSq_sum_le (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) (hH : 0 < H) :
    (H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n‖ ^ 2
      ≤ ((N : ℝ) + H - 1) * ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ‖corr z N k‖ := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hpos : (0 : ℝ) ≤ (N : ℝ) + H - 1 := by
    have h1H : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hcore := sq_mul_norm_sum_le hz hH
  have hpair : ∑ p ∈ range H ×ˢ range H, ‖corr z N ((p.1 : ℤ) - (p.2 : ℤ))‖
      ≤ (H : ℝ) * ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ‖corr z N k‖ := sum_product_norm_corr_le
  nlinarith [hcore, hpair, hHpos, hpos]

/-- **The van der Corput inequality, weighted form.**  The sharper classical statement, with
the Fejér weights:

`H² ‖∑ z n‖² ≤ (N + H − 1) ∑_{|k| < H} (H − |k|) ‖corr z N k‖`. -/
theorem mul_normSq_sum_le_weighted (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n‖ ^ 2
      ≤ ((N : ℝ) + H - 1)
        * ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ((H : ℝ) - |k|) * ‖corr z N k‖ := by
  have hcore := sq_mul_norm_sum_le hz hH
  rw [sum_product_norm_corr_eq] at hcore
  calc (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n‖ ^ 2
      = ((H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n‖) ^ 2 := by ring
    _ ≤ _ := hcore

/-- Two windows both containing the support of `g` give the same sum. -/
theorem sum_eq_sum_of_supported {g : ℤ → ℂ} {s t u : Finset ℤ} (hus : u ⊆ s) (hut : u ⊆ t)
    (hg : ∀ n ∉ u, g n = 0) : ∑ n ∈ s, g n = ∑ n ∈ t, g n := by
  rw [← Finset.sum_subset hus fun x _ hx => hg x hx, ← Finset.sum_subset hut fun x _ hx => hg x hx]

/-- The correlation at the opposite shift is the conjugate: `corr (−k) = conj (corr k)`. -/
theorem corr_neg (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) (k : ℤ) :
    corr z N (-k) = (starRingEnd ℂ) (corr z N k) := by
  classical
  have hconj : (starRingEnd ℂ) (corr z N k)
      = ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
          (fun m : ℤ => z (m - k) * (starRingEnd ℂ) (z m)) (n + k) := by
    simp only [corr, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [add_sub_cancel_right]
    ring
  rw [hconj, Finset.sum_Ico_add' (fun m : ℤ => z (m - k) * (starRingEnd ℂ) (z m))
    (0 : ℤ) (N : ℤ) k]
  refine (sum_eq_sum_of_supported (u := Finset.Ico (max 0 k) (min (N : ℤ) ((N : ℤ) + k)))
    ?_ ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_Ico] at hx ⊢
    omega
  · intro x hx
    rw [Finset.mem_Ico] at hx ⊢
    omega
  · intro x hx
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hx
    rcases hx with hx | hx
    · rcases lt_or_ge x 0 with h | h
      · rw [hz x (Or.inl h)]
        simp
      · rw [hz (x + -k) (Or.inl (by omega))]
        simp
    · rcases le_or_gt (N : ℤ) x with h | h
      · rw [hz x (Or.inr h)]
        simp
      · rw [hz (x + -k) (Or.inr (by omega))]
        simp

/-- The norms of the correlations at opposite shifts agree. -/
theorem norm_corr_neg (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) (k : ℤ) :
    ‖corr z N (-k)‖ = ‖corr z N k‖ := by
  rw [corr_neg hz, RCLike.norm_conj]

/-- Folding the shifts: the two-sided sum of the correlation norms is the diagonal term plus
twice the positive shifts. -/
theorem sum_Ioo_norm_corr_eq (hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0) (hH : 0 < H) :
    ∑ k ∈ Finset.Ioo (-(H : ℤ)) (H : ℤ), ‖corr z N k‖
      = ‖corr z N 0‖ + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), ‖corr z N k‖ := by
  classical
  have hsplit : Finset.Ioo (-(H : ℤ)) (H : ℤ)
      = (Finset.Ioo (-(H : ℤ)) 0 ∪ {(0 : ℤ)}) ∪ Finset.Ioo (0 : ℤ) (H : ℤ) := by
    ext k
    simp only [Finset.mem_Ioo, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨h₁, h₂⟩
      rcases lt_trichotomy k 0 with h | h | h
      · exact Or.inl (Or.inl ⟨h₁, h⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨h, h₂⟩
    · rintro ((⟨h₁, h₂⟩ | rfl) | ⟨h₁, h₂⟩)
      · exact ⟨h₁, by omega⟩
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, h₂⟩
  have hdisj₁ : Disjoint (Finset.Ioo (-(H : ℤ)) 0) ({(0 : ℤ)} : Finset ℤ) := by
    simp [Finset.disjoint_singleton_right]
  have hdisj₂ : Disjoint (Finset.Ioo (-(H : ℤ)) 0 ∪ {(0 : ℤ)}) (Finset.Ioo (0 : ℤ) (H : ℤ)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_singleton] at ha ha'
    omega
  have hneg : ∑ k ∈ Finset.Ioo (-(H : ℤ)) 0, ‖corr z N k‖
      = ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ), ‖corr z N k‖ := by
    refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Ioo] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Ioo] at ha ⊢
      omega
    · intro a _
      simp
    · intro a _
      simp
    · intro a _
      exact (norm_corr_neg hz a).symm
  rw [hsplit, Finset.sum_union hdisj₂, Finset.sum_union hdisj₁, hneg, Finset.sum_singleton]
  ring

section Exponential

open KusminLandau

@[simp] theorem e2pi_zero : e2pi 0 = 1 := by
  simp [e2pi]

/-- The conjugate of `e(θ)` is `e(−θ)`. -/
theorem conj_e2pi (x : ℝ) : (starRingEnd ℂ) (e2pi x) = e2pi (-x) := by
  simp only [e2pi, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **The A process for an exponential sum.**  For any phase `f`, and any `H ≥ 1`,

`H ‖∑_{0 ≤ n < N} e(f n)‖² ≤ (N + H − 1) (N + 2 ∑_{0 < k < H} ‖∑_{0 ≤ n < N−k} e(f(n+k) − f(n))‖)`.

The inner sums are exponential sums with the differenced phase `f(· + k) − f(·)`. -/
theorem norm_sq_sum_e2pi_le (f : ℤ → ℝ) (N H : ℕ) (hH : 0 < H) :
    (H : ℝ) * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n)‖ ^ 2
      ≤ ((N : ℝ) + H - 1) * ((N : ℝ) + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
          ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k), e2pi (f (n + k) - f n)‖) := by
  classical
  set z : ℤ → ℂ := fun n => if 0 ≤ n ∧ n < (N : ℤ) then e2pi (f n) else 0 with hzdef
  have hz : ∀ n : ℤ, n < 0 ∨ (N : ℤ) ≤ n → z n = 0 := by
    intro n hn
    simp only [hzdef]
    rw [if_neg]
    omega
  have hS : ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z n
      = ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), e2pi (f n) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ico] at hn
    simp only [hzdef]
    rw [if_pos ⟨hn.1, hn.2⟩]
  have hcorr0 : ‖corr z N 0‖ = (N : ℝ) := by
    have : corr z N 0 = (N : ℂ) := by
      simp only [corr, add_zero]
      rw [Finset.sum_congr rfl (g := fun _ : ℤ => (1 : ℂ)) ?_]
      · simp
      · intro n hn
        rw [Finset.mem_Ico] at hn
        simp only [hzdef]
        rw [if_pos ⟨hn.1, hn.2⟩, conj_e2pi, ← e2pi_add]
        simp
    rw [this, Complex.norm_natCast]
  have hcorrk : ∀ k ∈ Finset.Ioo (0 : ℤ) (H : ℤ),
      ‖corr z N k‖ = ‖∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k), e2pi (f (n + k) - f n)‖ := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    congr 1
    have hshrink : ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), z (n + k) * (starRingEnd ℂ) (z n)
        = ∑ n ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k), z (n + k) * (starRingEnd ℂ) (z n) := by
      refine sum_eq_sum_of_supported (u := Finset.Ico (0 : ℤ) ((N : ℤ) - k)) ?_
        (Finset.Subset.refl _) ?_
      · intro x hx
        rw [Finset.mem_Ico] at hx ⊢
        omega
      · intro x hx
        rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hx
        rcases hx with hx | hx
        · rw [hz x (Or.inl hx)]
          simp
        · rw [hz (x + k) (Or.inr (by omega))]
          simp
    rw [corr, hshrink]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ico] at hn
      simp only [hzdef]
      rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨hn.1, by omega⟩, conj_e2pi, ← e2pi_add,
        ← sub_eq_add_neg]
  have hmain := mul_normSq_sum_le hz hH
  rw [hS] at hmain
  refine hmain.trans ?_
  rw [sum_Ioo_norm_corr_eq hz hH, hcorr0, Finset.sum_congr rfl hcorrk]

end Exponential

end WeylDifferencing

end RiemannHypothesis
