/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Zeta23.LinAlg
import Zeta23.ZeroSide
import RiemannHypothesis.OffLineQuadruple

/-!
# The Gram-matrix inertia certificate, in this repository's vocabulary

This module isolates the linear-algebra half of the argument behind the `2/3` of the vendored
`Zeta23` library (see `docs/zeta23-methodology.md`): the part that does not involve `ζ` at all.

## What was already available, and what is new here

The vendored library already contains, in its namespace `RHLinalg`, the positive index
`posIndex` of a Hermitian matrix, the variational (Courant–Fischer / Sylvester) description of
it, the pull-back inequality `posIndex_conj_le`, subadditivity `posIndex_add_le`, the von Neumann
trace inequality for Hermitian matrices `vonNeumann_trace_ineq`, and the rank–trace inequality
`rank_trace_ineq`; and in `Zeta23.ZeroSide` the abstract block data `ZeroBlockData` with the
bound `posIndex_blockQ_le`.  Mathlib itself only has the *existence* half of Sylvester's law
(`QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`: every real form is
equivalent to a signed sum of squares); the *invariance* of the index is not in Mathlib.

New in this module:

* **B1 — Sylvester's law of inertia (invariance).**  `posIndex_conj_eq`, `negIndex_conj_eq`,
  `rank_conj_eq`: for Hermitian `Q` and invertible `B`, the matrices `Q` and `Bᴴ Q B` have the
  same positive index, the same negative index and the same rank.  Also
  `posIndex_add_negIndex`: `n₊ + n₋ = rank`.
* **B2 — von Neumann, absolute form.**  `norm_trace_mul_le_of_posSemidef`: for positive
  semidefinite `A, B` (whose eigenvalues are their singular values),
  `‖tr(AB)‖ ≤ Σᵢ aᵢ bᵢ` with both eigenvalue lists sorted decreasingly.
* **B3 — the reflection block structure, wired to `criticalReflect`.**  A `ReflectionConfig` is a
  finite set of points of `ℂ` stable under `criticalReflect ρ = 1 − ρ̄`, with symmetric
  multiplicities; a taper is any `φ : ℂ → ℂ` with `φ(z̄) = conj φ(z)`.  The Gram matrix
  `gram C φ τ = Σ_ρ m_ρ v_ρ v_ρᵀ`, `v_ρ(k) = φ(γ_ρ − τ_k)` satisfies
  `posIndex_gram_le`: `n₊(A) ≤ #{on-line points} + #{points with Re ρ > 1/2}`, and the number of
  off-line points is twice the second term (`card_offLine_eq_two_mul`): *an off-line pair costs
  two zeros but can raise the positive index by at most one*.
* **B4 — the abstract inertia certificate.**  `inertia_certificate` (matrix level, no `ζ`):
  if `A = P + Q` with `P ⪰ 0` of rank `≤ r`, `n₊(Q) ≤ b`, `tr P ≤ N_on` and `N_on + 2b ≤ N`, then
  `4 tr A − 2N − ‖A‖_F² ≤ r`.  `inertia_certificate_ratio` feeds in the two prime-side estimates
  `tr A ≥ αN − E₁`, `‖A‖_F² ≤ βN + E₂` and returns `(4α − β − 2)N − (4E₁ + E₂) ≤ r`;
  `inertia_certificate_eventually` is the asymptotic form (errors `o(N)` give
  `r ≥ (4α − β − 2 − ε)N` eventually).  `gram_certificate` and
  `gram_certificate_eventually` are the same statements for the Gram matrix of a
  `ReflectionConfig`, with `r` the number of distinct on-line points; with `α = 1`,
  `β = 1/λ + λ/3` the constant is `Zeta23.Hfun λ = 2 − 1/λ − λ/3`, which is `2/3` at `λ = 1`
  (`gram_two_thirds_eventually`).

The prime-side inputs (the asymptotics of `tr Â` and `‖Â‖_F²` from the explicit formula) and the
Poisson-summation bound on the diagonal enter only as explicit hypotheses.  Nothing here
assumes anything about the zeros of `ζ`.
-/

noncomputable section

open Matrix Finset RHLinalg Filter Topology
open scoped ComplexOrder

namespace RiemannHypothesis

namespace GramInertia

/-! ## B1. Sylvester's law of inertia -/

section Sylvester

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

/-- The positive index only depends on the matrix, not on the Hermitian-ness proof. -/
lemma posIndex_eq_of_eq {A B : Matrix m m 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : posIndex hA = posIndex hB := by
  subst h; rfl

/-- The negative index only depends on the matrix, not on the Hermitian-ness proof. -/
lemma negIndex_eq_of_eq {A B : Matrix m m 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : negIndex hA = negIndex hB := by
  subst h; rfl

/-- `n₊(A) + n₋(A) = rank A` for Hermitian `A`: the nonzero eigenvalues split into the
positive and the negative ones. -/
theorem posIndex_add_negIndex {A : Matrix m m 𝕜} (hA : A.IsHermitian) :
    posIndex hA + negIndex hA = A.rank := by
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  unfold posIndex negIndex
  rw [← card_union_of_disjoint]
  · congr 1
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and, ne_eq]
    constructor
    · rintro (h | h) <;> [exact h.ne'; exact h.ne]
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
  · rw [disjoint_filter]
    intro i _ h1 h2
    linarith

/-- Undoing a congruence: `(B⁻¹)ᴴ (Bᴴ Q B) B⁻¹ = Q` for invertible `B`. -/
lemma conj_inv_conj {Q B : Matrix m m 𝕜} (hB : IsUnit B) :
    (B⁻¹)ᴴ * (Bᴴ * Q * B) * B⁻¹ = Q := by
  have hdet : IsUnit B.det := (isUnit_iff_isUnit_det B).mp hB
  have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hdet
  have h2 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  calc (B⁻¹)ᴴ * (Bᴴ * Q * B) * B⁻¹ = ((B⁻¹)ᴴ * Bᴴ) * Q * (B * B⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = Q := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/-- **Sylvester's law of inertia, positive index.**  For Hermitian `Q` and invertible `B`,
`n₊(Bᴴ Q B) = n₊(Q)`. -/
theorem posIndex_conj_eq {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) {B : Matrix m m 𝕜}
    (hB : IsUnit B) :
    posIndex (isHermitian_conjTranspose_mul_mul B hQ) = posIndex hQ := by
  refine le_antisymm (posIndex_conj_le hQ B) ?_
  have hM := isHermitian_conjTranspose_mul_mul B hQ
  calc posIndex hQ = posIndex (isHermitian_conjTranspose_mul_mul B⁻¹ hM) :=
        posIndex_eq_of_eq _ _ (conj_inv_conj hB).symm
    _ ≤ posIndex hM := posIndex_conj_le hM B⁻¹

/-- Rank is invariant under congruence by an invertible matrix. -/
theorem rank_conj_eq (Q : Matrix m m 𝕜) {B : Matrix m m 𝕜} (hB : IsUnit B) :
    (Bᴴ * Q * B).rank = Q.rank := by
  have hdet : IsUnit B.det := (isUnit_iff_isUnit_det B).mp hB
  have hdet' : IsUnit Bᴴ.det := by
    rw [det_conjTranspose]; exact hdet.star
  rw [rank_mul_eq_left_of_isUnit_det B _ hdet, rank_mul_eq_right_of_isUnit_det Bᴴ _ hdet']

/-- **Sylvester's law of inertia, negative index.**  For Hermitian `Q` and invertible `B`,
`n₋(Bᴴ Q B) = n₋(Q)`. -/
theorem negIndex_conj_eq {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) {B : Matrix m m 𝕜}
    (hB : IsUnit B) :
    negIndex (isHermitian_conjTranspose_mul_mul B hQ) = negIndex hQ := by
  have h1 := posIndex_add_negIndex (isHermitian_conjTranspose_mul_mul B hQ)
  have h2 := posIndex_add_negIndex hQ
  rw [posIndex_conj_eq hQ hB, rank_conj_eq Q hB] at h1
  omega

end Sylvester

/-! ## B2. von Neumann's trace inequality, absolute form for positive semidefinite matrices -/

section VonNeumann

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The trace of a product of two Hermitian matrices is real. -/
lemma im_trace_mul_eq_zero {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.im (A * B).trace = 0 := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hA.eq, hB.eq, trace_mul_comm]
  have := congrArg RCLike.im h
  rw [RCLike.star_def, RCLike.conj_im] at this
  linarith

/-- **von Neumann's trace inequality, absolute form.**  For positive semidefinite `A` and `B`
(whose decreasingly sorted eigenvalues are their singular values),
`‖tr(AB)‖ ≤ Σᵢ aᵢ bᵢ`. -/
theorem norm_trace_mul_le_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    ‖(A * B).trace‖ ≤ ∑ i, hA.isHermitian.eigenvalues₀ i * hB.isHermitian.eigenvalues₀ i := by
  have hre : 0 ≤ RCLike.re (A * B).trace := trace_mul_nonneg_of_posSemidef hA hB
  have him := im_trace_mul_eq_zero hA.isHermitian hB.isHermitian
  have hnorm : ‖(A * B).trace‖ = RCLike.re (A * B).trace := by
    rw [← RCLike.re_add_im (A * B).trace, him]
    simp [abs_of_nonneg hre]
  rw [hnorm]
  exact vonNeumann_trace_ineq hA.isHermitian hB.isHermitian

end VonNeumann

/-! ## B4. The abstract inertia certificate -/

section Certificate

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The inertia certificate (matrix level, no `ζ`).**  Let `A = P + Q` with `P ⪰ 0` of rank at
most `r`, `Q` Hermitian with positive index at most `b`, `tr P ≤ N_on` and `N_on + 2b ≤ N`.
Then `4 tr A − 2N − ‖A‖_F² ≤ r`. -/
theorem inertia_certificate {A P Q : Matrix n n 𝕜}
    (hA : A = P + Q) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {Non N : ℝ} (htrP : rtrace P ≤ Non) (hN : Non + 2 * b ≤ N) :
    4 * rtrace A - 2 * N - frobSq A ≤ r := by
  have h := rank_trace_ineq_two hP hQ hr hb
  subst hA
  rw [rtrace_add]
  linarith

/-- **The inertia certificate with the prime-side inputs.**  If moreover `tr A ≥ αN − E₁` and
`‖A‖_F² ≤ βN + E₂`, then `(4α − β − 2) N − (4E₁ + E₂) ≤ r`. -/
theorem inertia_certificate_ratio {A P Q : Matrix n n 𝕜}
    (hA : A = P + Q) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {Non N : ℝ} (htrP : rtrace P ≤ Non) (hN : Non + 2 * b ≤ N)
    {α β E₁ E₂ : ℝ} (htr : α * N - E₁ ≤ rtrace A) (hfr : frobSq A ≤ β * N + E₂) :
    (4 * α - β - 2) * N - (4 * E₁ + E₂) ≤ r := by
  have h := inertia_certificate hA hP hQ hr hb htrP hN
  linarith

/-- **Asymptotic form of the certificate, purely numerical.**  If along a filter
`r ≥ 4 tr − 2N − frob`, `tr ≥ αN − E₁`, `frob ≤ βN + E₂` with `E₁/N → 0`, `E₂/N → 0` and
`N > 0` eventually, then for every `ε > 0` eventually `(4α − β − 2 − ε) N ≤ r`. -/
theorem certificate_eventually_of_bounds {ι : Type*} {l : Filter ι}
    {r N tr fr E₁ E₂ : ι → ℝ} {α β : ℝ}
    (hcore : ∀ᶠ t in l, 4 * tr t - 2 * N t - fr t ≤ r t)
    (htr : ∀ᶠ t in l, α * N t - E₁ t ≤ tr t) (hfr : ∀ᶠ t in l, fr t ≤ β * N t + E₂ t)
    (hNpos : ∀ᶠ t in l, 0 < N t)
    (hE₁ : Tendsto (fun t => E₁ t / N t) l (𝓝 0)) (hE₂ : Tendsto (fun t => E₂ t / N t) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, (4 * α - β - 2 - ε) * N t ≤ r t := by
  have hsum : Tendsto (fun t => 4 * (E₁ t / N t) + E₂ t / N t) l (𝓝 0) := by
    simpa using (hE₁.const_mul 4).add hE₂
  have hsmall : ∀ᶠ t in l, 4 * (E₁ t / N t) + E₂ t / N t < ε :=
    hsum.eventually (gt_mem_nhds hε)
  filter_upwards [hcore, htr, hfr, hNpos, hsmall] with t hc ht hf hN hs
  have hs' : 4 * E₁ t + E₂ t < ε * N t := by
    have : (4 * E₁ t + E₂ t) / N t < ε := by
      rw [add_div, mul_div_assoc]; exact hs
    rwa [div_lt_iff₀ hN] at this
  nlinarith

end Certificate

/-! ## B3. Reflection-symmetric configurations and their Gram matrices -/

/-- A finite configuration of points of `ℂ` (for instance the distinct zeros of `ζ` in a window)
that is stable under the reflection `criticalReflect ρ = 1 − ρ̄`, with multiplicities `≥ 1`
that are invariant under the reflection. -/
structure ReflectionConfig where
  /-- the distinct points -/
  S : Finset ℂ
  /-- their multiplicities -/
  mult : ℂ → ℕ
  one_le_mult : ∀ ρ ∈ S, 1 ≤ mult ρ
  reflect_mem : ∀ ρ ∈ S, criticalReflect ρ ∈ S
  mult_reflect : ∀ ρ ∈ S, mult (criticalReflect ρ) = mult ρ

namespace ReflectionConfig

variable (C : ReflectionConfig)

/-- The distinct points on the critical line. -/
def onLine : Finset ℂ := C.S.filter fun ρ => ρ.re = 1 / 2

/-- The distinct points off the critical line. -/
def offLine : Finset ℂ := C.S.filter fun ρ => ρ.re ≠ 1 / 2

/-- The distinct points strictly to the right of the critical line (one from each off-line
pair `{ρ, 1 − ρ̄}`). -/
def rightOf : Finset ℂ := C.S.filter fun ρ => 1 / 2 < ρ.re

/-- The number of points counted with multiplicity. -/
def count : ℕ := ∑ ρ ∈ C.S, C.mult ρ

lemma criticalReflect_eq_self_iff (ρ : ℂ) : criticalReflect ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    rw [criticalReflect_re] at this
    linarith
  · intro h
    apply Complex.ext
    · rw [criticalReflect_re, h]; norm_num
    · rw [criticalReflect_im]

/-- Off-line points come in pairs: their number is twice the number of points to the right of
the line. -/
theorem card_offLine_eq_two_mul : C.offLine.card = 2 * C.rightOf.card := by
  classical
  have hsplit : C.offLine = C.rightOf ∪ C.S.filter (fun ρ => ρ.re < 1 / 2) := by
    ext ρ
    simp only [offLine, rightOf, mem_filter, mem_union]
    constructor
    · rintro ⟨h, hne⟩
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact Or.inr ⟨h, h'⟩
      · exact Or.inl ⟨h, h'⟩
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact ⟨h, h'.ne'⟩
      · exact ⟨h, h'.ne⟩
  have hdisj : Disjoint C.rightOf (C.S.filter (fun ρ => ρ.re < 1 / 2)) := by
    rw [rightOf, disjoint_filter]
    intro ρ _ h1 h2
    linarith
  have himage : (C.S.filter (fun ρ => ρ.re < 1 / 2)) = C.rightOf.image criticalReflect := by
    ext ρ
    simp only [rightOf, mem_filter, mem_image]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨criticalReflect ρ, ⟨C.reflect_mem ρ h, ?_⟩, criticalReflect_criticalReflect ρ⟩
      rw [criticalReflect_re]; linarith
    · rintro ⟨σ, ⟨h, h'⟩, rfl⟩
      exact ⟨C.reflect_mem σ h, by rw [criticalReflect_re]; linarith⟩
  rw [hsplit, card_union_of_disjoint hdisj, himage,
    card_image_of_injective _ criticalReflect_injective]
  ring

/-- The distinct points split into on-line points and off-line pairs. -/
theorem card_eq : C.S.card = C.onLine.card + 2 * C.rightOf.card := by
  rw [← card_offLine_eq_two_mul, onLine, offLine]
  exact (card_filter_add_card_filter_not _).symm

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The evaluation vector `v_ρ(k) = φ(γ_ρ − τ_k)`, `γ_ρ = (ρ − 1/2)/i`. -/
def evalVec (φ : ℂ → ℂ) (τ : d → ℝ) (ρ : ℂ) : d → ℂ :=
  fun k => φ (Zeta23.gammaOf ρ - τ k)

/-- **The Gram matrix** `A = Σ_ρ m_ρ v_ρ v_ρᵀ` of the configuration, sampled at the nodes `τ`. -/
def gram (φ : ℂ → ℂ) (τ : d → ℝ) : Matrix d d ℂ :=
  ∑ ρ ∈ C.S, (C.mult ρ : ℂ) • vecMulVec (evalVec φ τ ρ) (evalVec φ τ ρ)

lemma criticalReflect_eq_reflect (ρ : ℂ) : criticalReflect ρ = Zeta23.reflect ρ := rfl

omit [Fintype d] [DecidableEq d] in
/-- For a taper with `φ(z̄) = conj φ(z)`, the evaluation vector of the reflected point is the
conjugate of the evaluation vector. -/
lemma star_evalVec {φ : ℂ → ℂ} (hφ : ∀ z, φ (starRingEnd ℂ z) = starRingEnd ℂ (φ z))
    (τ : d → ℝ) (ρ : ℂ) : evalVec φ τ (criticalReflect ρ) = star (evalVec φ τ ρ) := by
  funext k
  simp only [evalVec, Pi.star_apply, RCLike.star_def]
  rw [criticalReflect_eq_reflect, Zeta23.ZeroSide.gammaOf_reflect, ← hφ]
  congr 1
  simp

/-- The configuration as abstract block data (`Zeta23.ZeroSide.ZeroBlockData`), for a taper
satisfying the reality condition `φ(z̄) = conj φ(z)`. -/
def blockData (φ : ℂ → ℂ) (hφ : ∀ z, φ (starRingEnd ℂ z) = starRingEnd ℂ (φ z)) (τ : d → ℝ) :
    Zeta23.ZeroSide.ZeroBlockData C.S d where
  m z := C.mult z
  one_le_m z := C.one_le_mult z z.2
  v z := evalVec φ τ z
  σ z := ⟨criticalReflect z, C.reflect_mem z z.2⟩
  σ_invol z := Subtype.ext (criticalReflect_criticalReflect z)
  m_σ z := C.mult_reflect z z.2
  v_σ z := star_evalVec hφ τ z

variable (φ : ℂ → ℂ) (hφ : ∀ z, φ (starRingEnd ℂ z) = starRingEnd ℂ (φ z)) (τ : d → ℝ)

omit [Fintype d] [DecidableEq d] in
lemma blockA_blockData : (C.blockData φ hφ τ).blockA = C.gram φ τ := by
  unfold Zeta23.ZeroSide.ZeroBlockData.blockA gram
  exact Finset.sum_coe_sort C.S
    (fun ρ => (C.mult ρ : ℂ) • vecMulVec (evalVec φ τ ρ) (evalVec φ τ ρ))

/-- The representatives `Re ρ > 1/2` of the off-line pairs. -/
def pairReps : (C.blockData φ hφ τ).PairReps where
  R := Finset.univ.filter fun z : C.S => 1 / 2 < (z : ℂ).re
  off z hz := by
    simp only [mem_filter, mem_univ, true_and] at hz
    intro h
    have h' := congrArg (fun w : C.S => (w : ℂ).re) h
    simp only [blockData, criticalReflect_re] at h'
    linarith
  σ_not_mem z hz := by
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    simp only [blockData, criticalReflect_re]
    linarith
  cover z hz := by
    simp only [mem_filter, mem_univ, true_and]
    simp only [blockData, criticalReflect_re]
    have hne : (z : ℂ).re ≠ 1 / 2 := by
      intro h
      apply hz
      exact Subtype.ext ((criticalReflect_eq_self_iff _).mpr h)
    rcases lt_or_gt_of_ne hne with h | h
    · right; linarith
    · left; exact h

omit [Fintype d] [DecidableEq d] in
lemma pairReps_p : (C.pairReps φ hφ τ).p = C.rightOf.card := by
  unfold Zeta23.ZeroSide.ZeroBlockData.PairReps.p pairReps rightOf
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext ρ
  simp only [Finset.mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z.2, hz⟩
  · rintro ⟨h, h'⟩; exact ⟨⟨ρ, h⟩, h', rfl⟩

omit [Fintype d] [DecidableEq d] in
lemma onLine_blockData_card :
    (C.blockData φ hφ τ).onLine.card = C.onLine.card := by
  unfold Zeta23.ZeroSide.ZeroBlockData.onLine onLine
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext ρ
  simp only [Finset.mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, (criticalReflect_eq_self_iff _).mp ?_⟩
    exact congrArg Subtype.val hz
  · rintro ⟨h, h'⟩
    exact ⟨⟨ρ, h⟩, Subtype.ext ((criticalReflect_eq_self_iff _).mpr h'), rfl⟩

omit [Fintype d] [DecidableEq d] in
lemma Ncount_blockData : (C.blockData φ hφ τ).Ncount = C.count := by
  unfold Zeta23.ZeroSide.ZeroBlockData.Ncount count
  exact Finset.sum_coe_sort C.S C.mult

omit [Fintype d] [DecidableEq d] in
include hφ in
/-- The Gram matrix is Hermitian. -/
theorem gram_isHermitian : (C.gram φ τ).IsHermitian := by
  unfold gram IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_nbij' criticalReflect criticalReflect (fun ρ h => C.reflect_mem ρ h)
    (fun ρ h => C.reflect_mem ρ h) (fun ρ _ => criticalReflect_criticalReflect ρ)
    (fun ρ _ => criticalReflect_criticalReflect ρ) ?_
  intro ρ hρ
  rw [conjTranspose_smul, conjTranspose_vecMulVec, C.mult_reflect ρ hρ, star_evalVec hφ τ]
  simp

/-- **The reflection block bound.**  The positive index of the Gram matrix is at most the number
of distinct on-line points plus the number of off-line *pairs*: each pair `{ρ, 1 − ρ̄}`
contributes a hyperbolic `2 × 2` block, which raises `n₊` by at most one. -/
theorem posIndex_gram_le :
    posIndex (C.gram_isHermitian φ hφ τ) ≤ C.onLine.card + C.rightOf.card := by
  have h := (C.blockData φ hφ τ).posIndex_blockA_le (C.pairReps φ hφ τ)
  rw [posIndex_eq_of_eq _ _ (C.blockA_blockData φ hφ τ),
    ← Zeta23.ZeroSide.ZeroBlockData.card_onLine, onLine_blockData_card, pairReps_p] at h
  exact h

/-- The same bound in the form "on-line points plus half the off-line points". -/
theorem two_mul_posIndex_gram_le :
    2 * posIndex (C.gram_isHermitian φ hφ τ) ≤ 2 * C.onLine.card + C.offLine.card := by
  have := C.posIndex_gram_le φ hφ τ
  rw [card_offLine_eq_two_mul]
  omega

omit [DecidableEq d] in
/-- The rank of the Gram matrix is at most the number of distinct points. -/
theorem rank_gram_le : (C.gram φ τ).rank ≤ C.S.card := by
  unfold gram
  refine (Zeta23.ZeroSide.rank_sum_le _ _ (fun _ => 1)
    fun ρ _ => Zeta23.ZeroSide.rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

/-- The normalised Gram matrix `Â = c⁻¹ A` (the paper's "hat units", `c = aL²`). -/
def gramHat (c : ℝ) : Matrix d d ℂ := ((c⁻¹ : ℝ) : ℂ) • C.gram φ τ

omit [DecidableEq d] in
include hφ in
/-- **The inertia certificate for a reflection-symmetric configuration.**  If the diagonal
("Poisson") bound `Σ_k |φ(γ_ρ − τ_k)|² ≤ c` holds at every on-line point, then the number of
distinct on-line points is at least `4 tr Â − 2N − ‖Â‖_F²`, where `N` counts all points with
multiplicity. -/
theorem gram_certificate {c : ℝ} (hc : 0 < c)
    (hPois : ∀ ρ ∈ C.onLine, ∑ k, ‖evalVec φ τ ρ k‖ ^ 2 ≤ c) :
    4 * rtrace (C.gramHat φ τ c) - 2 * (C.count : ℝ) - frobSq (C.gramHat φ τ c)
      ≤ C.onLine.card := by
  classical
  set D := C.blockData φ hφ τ
  set P := C.pairReps φ hφ τ
  have hdec : C.gramHat φ τ c = D.blockP c + D.blockQ c := by
    rw [D.blockP_add_blockQ, C.blockA_blockData φ hφ τ]; rfl
  have hPois' : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c := by
    intro z hz
    apply hPois
    simp only [onLine, mem_filter]
    refine ⟨z.2, (criticalReflect_eq_self_iff _).mp ?_⟩
    exact congrArg Subtype.val ((D.mem_onLine).mp hz)
  have hcount : (D.Non : ℝ) + 2 * (P.p : ℝ) ≤ C.count := by
    have := D.Non_add_two_p_le_Ncount P
    rw [Ncount_blockData] at this
    exact_mod_cast this
  have h := inertia_certificate hdec (D.blockP_posSemidef hc) (D.blockQ_isHermitian c)
    (D.rank_blockP_le hc) (D.posIndex_blockQ_le P hc) (D.rtrace_blockP_le hc hPois') hcount
  rw [← Zeta23.ZeroSide.ZeroBlockData.card_onLine, onLine_blockData_card] at h
  exact_mod_cast h

omit [DecidableEq d] in
include hφ in
/-- **The certificate with the prime-side inputs.**  If `tr Â ≥ αN − E₁` and
`‖Â‖_F² ≤ βN + E₂`, then `#{on-line points} ≥ (4α − β − 2)N − (4E₁ + E₂)`. -/
theorem gram_certificate_ratio {c : ℝ} (hc : 0 < c)
    (hPois : ∀ ρ ∈ C.onLine, ∑ k, ‖evalVec φ τ ρ k‖ ^ 2 ≤ c)
    {α β E₁ E₂ : ℝ} (htr : α * C.count - E₁ ≤ rtrace (C.gramHat φ τ c))
    (hfr : frobSq (C.gramHat φ τ c) ≤ β * C.count + E₂) :
    (4 * α - β - 2) * C.count - (4 * E₁ + E₂) ≤ C.onLine.card := by
  have h := C.gram_certificate φ hφ τ hc hPois
  linarith

end ReflectionConfig

/-! ### The asymptotic certificate for a family of configurations -/

/-- A family of reflection-symmetric configurations with tapers and sampling nodes, indexed by a
parameter `t` (in the application: the height `T`, with `d_t` nodes in the window). -/
structure GramFamily (ι : Type*) where
  /-- the configurations -/
  C : ι → ReflectionConfig
  /-- the number of nodes -/
  d : ι → ℕ
  /-- the tapers -/
  φ : ι → ℂ → ℂ
  hφ : ∀ t z, φ t (starRingEnd ℂ z) = starRingEnd ℂ (φ t z)
  /-- the nodes -/
  τ : ∀ t, Fin (d t) → ℝ
  /-- the normalisation `c_t = a L²` -/
  c : ι → ℝ
  c_pos : ∀ t, 0 < c t
  /-- the diagonal (Poisson) bound at on-line points -/
  poisson : ∀ t, ∀ ρ ∈ (C t).onLine,
    ∑ k, ‖ReflectionConfig.evalVec (φ t) (τ t) ρ k‖ ^ 2 ≤ c t

namespace GramFamily

variable {ι : Type*} (G : GramFamily ι)

/-- The normalised Gram matrix of the `t`-th configuration. -/
def gramHat (t : ι) : Matrix (Fin (G.d t)) (Fin (G.d t)) ℂ :=
  (G.C t).gramHat (G.φ t) (G.τ t) (G.c t)

/-- **The asymptotic inertia certificate.**  If the prime side gives
`tr Â_t ≥ α N_t − E₁(t)` and `‖Â_t‖_F² ≤ β N_t + E₂(t)` with `E₁, E₂ = o(N_t)`, then for every
`ε > 0`, eventually `#{on-line points} ≥ (4α − β − 2 − ε) N_t`. -/
theorem certificate_eventually {l : Filter ι} {α β : ℝ} {E₁ E₂ : ι → ℝ}
    (htr : ∀ᶠ t in l, α * (G.C t).count - E₁ t ≤ rtrace (G.gramHat t))
    (hfr : ∀ᶠ t in l, frobSq (G.gramHat t) ≤ β * (G.C t).count + E₂ t)
    (hNpos : ∀ᶠ t in l, 0 < (G.C t).count)
    (hE₁ : Tendsto (fun t => E₁ t / (G.C t).count) l (𝓝 0))
    (hE₂ : Tendsto (fun t => E₂ t / (G.C t).count) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, (4 * α - β - 2 - ε) * (G.C t).count ≤ (G.C t).onLine.card := by
  refine certificate_eventually_of_bounds (tr := fun t => rtrace (G.gramHat t))
    (fr := fun t => frobSq (G.gramHat t)) (Eventually.of_forall fun t => ?_) htr hfr
    (hNpos.mono fun t h => by exact_mod_cast h) hE₁ hE₂ hε
  exact (G.C t).gram_certificate (G.φ t) (G.hφ t) (G.τ t) (G.c_pos t) (G.poisson t)

/-- **The shape of the `2/3`.**  With `tr Â_t = N_t(1 + o(1))` and
`‖Â_t‖_F² ≤ (1/λ + λ/3) N_t (1 + o(1))`, the proportion of distinct on-line points is
eventually at least `Hfun λ − ε = 2 − 1/λ − λ/3 − ε`. -/
theorem certificate_Hfun_eventually {l : Filter ι} {lam : ℝ} {E₁ E₂ : ι → ℝ}
    (htr : ∀ᶠ t in l, (G.C t).count - E₁ t ≤ rtrace (G.gramHat t))
    (hfr : ∀ᶠ t in l, frobSq (G.gramHat t) ≤ (1 / lam + lam / 3) * (G.C t).count + E₂ t)
    (hNpos : ∀ᶠ t in l, 0 < (G.C t).count)
    (hE₁ : Tendsto (fun t => E₁ t / (G.C t).count) l (𝓝 0))
    (hE₂ : Tendsto (fun t => E₂ t / (G.C t).count) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, (Zeta23.Hfun lam - ε) * (G.C t).count ≤ (G.C t).onLine.card := by
  have h := G.certificate_eventually (α := 1) (β := 1 / lam + lam / 3)
    (htr.mono fun t h => by simpa using h) hfr hNpos hE₁ hE₂ hε
  filter_upwards [h] with t ht
  have : Zeta23.Hfun lam - ε = 4 * 1 - (1 / lam + lam / 3) - 2 - ε := by
    simp only [Zeta23.Hfun]; ring
  rw [this]; exact ht

/-- **`2/3` from the two prime-side asymptotics.**  If `tr Â_t = N_t(1 + o(1))` and
`‖Â_t‖_F² ≤ (4/3) N_t (1 + o(1))` (the case `λ = 1`), then for every `ε > 0` eventually at least
`(2/3 − ε) N_t` of the points — counted with multiplicity in `N_t` — are distinct on-line
points. -/
theorem two_thirds_eventually {l : Filter ι} {E₁ E₂ : ι → ℝ}
    (htr : ∀ᶠ t in l, (G.C t).count - E₁ t ≤ rtrace (G.gramHat t))
    (hfr : ∀ᶠ t in l, frobSq (G.gramHat t) ≤ 4 / 3 * (G.C t).count + E₂ t)
    (hNpos : ∀ᶠ t in l, 0 < (G.C t).count)
    (hE₁ : Tendsto (fun t => E₁ t / (G.C t).count) l (𝓝 0))
    (hE₂ : Tendsto (fun t => E₂ t / (G.C t).count) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, (2 / 3 - ε) * (G.C t).count ≤ (G.C t).onLine.card := by
  have h := G.certificate_Hfun_eventually (lam := 1) htr
    (hfr.mono fun t h => by norm_num at h ⊢; linarith) hNpos hE₁ hE₂ hε
  filter_upwards [h] with t ht
  have : Zeta23.Hfun 1 = 2 / 3 := by norm_num [Zeta23.Hfun]
  rwa [this] at ht

end GramFamily

end GramInertia

end RiemannHypothesis
