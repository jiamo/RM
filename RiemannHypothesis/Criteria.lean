/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Symmetry
import RiemannHypothesis.Partial
import RiemannHypothesis.ZeroCount
import RiemannHypothesis.ZeroExists
import RiemannHypothesis.HalfPlaneLog
import Mathlib.Analysis.Convex.Contractible

/-!
# Further equivalent formulations of the Riemann hypothesis

This file adds four more reformulations of the Riemann hypothesis to the ones already proved
equivalent in `RiemannHypothesis.Main` (the eta form), `RiemannHypothesis.Symmetry` (the
upper-strip, right-strip, nonvanishing and self-reflective forms) and `RiemannHypothesis.Xi`
(the `ξ` form).  Each is proved equivalent to `ZetaStripForm`, hence to `ZetaForm`.

* `ZetaReciprocalForm` — `1/ζ` extends to a holomorphic function on the half-plane
  `re s > 1/2` punctured at `s = 1`: there is a holomorphic `g` there with `ζ · g = 1`.
  This is the "analytic reciprocal" reading of the hypothesis.

* `ZetaLogBranchForm` — the function `(s - 1) ζ(s)` admits a continuous logarithm on the
  half-plane `re s > 1/2` punctured at `s = 1`; equivalently, `log ζ` has a single-valued
  branch there.  The factor `s - 1` removes the pole of `ζ`.  The hard direction fills in the
  removable singularity at `s = 1` (the residue is `1`, so the filled-in value is nonzero)
  and then uses that a convex open set is simply connected, so a nonvanishing continuous
  function on it has a continuous logarithm.

* `ZetaCountingForm` — for every height `T`, all the zeros of height in `(0, T)` are on the
  critical line *in the sense of counting*: `N₀(T) = N(T)`, with the counting functions of
  `RiemannHypothesis.Partial`.  The nontrivial direction uses the finiteness of the zero set
  in a horizontal strip (`RiemannHypothesis.ZeroCount`).

* `ZetaSupForm` — the supremum of the real parts of the zeros in the critical strip is `1/2`.
  Here the existence of at least one zero (`RiemannHypothesis.ZeroExists`) is what makes the
  statement equivalent rather than merely implied by the hypothesis.

None of these is proved: as everywhere in this repository, what is proved is an equivalence.
-/

noncomputable section

open Complex Set

namespace RiemannHypothesis

/-! ## The analytic reciprocal form -/

/-- The Riemann hypothesis as the existence of a holomorphic reciprocal of `ζ` on the
half-plane `re s > 1/2` punctured at the pole `s = 1`. -/
def ZetaReciprocalForm : Prop :=
  ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s * g s = 1

/-- The Riemann hypothesis as the existence of a continuous branch of the logarithm of
`(s - 1) ζ(s)` on the half-plane `re s > 1/2`, punctured at the pole `s = 1`. -/
def ZetaLogBranchForm : Prop :=
  ∃ f : ℂ → ℂ, ContinuousOn f {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → Complex.exp (f s) = (s - 1) * riemannZeta s

/-- The Riemann hypothesis in counting form: for every `T`, the number of zeros of height in
`(0, T)` on the critical line equals the total number of zeros of height in `(0, T)`. -/
def ZetaCountingForm : Prop :=
  ∀ T : ℝ, criticalZeroCount T = zeroCount T

/-- The set of real parts of the zeros of `ζ` in the critical strip. -/
def stripZeroRealParts : Set ℝ :=
  {x : ℝ | ∃ s : ℂ, riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re = x}

/-- The Riemann hypothesis in supremum form: the real parts of the zeros in the critical
strip have supremum `1/2`. -/
def ZetaSupForm : Prop :=
  sSup stripZeroRealParts = 1 / 2

/-! ## The equivalences -/

theorem zeta_strip_iff_reciprocal : ZetaStripForm ↔ ZetaReciprocalForm := by
  constructor
  · intro h
    have hne : ZetaNonvanishingRightForm := zeta_strip_iff_nonvanishing_right.mp h
    refine ⟨fun s => (riemannZeta s)⁻¹, ?_, ?_⟩
    · intro s hs
      exact ((differentiableAt_riemannZeta hs.2).differentiableWithinAt).inv
        (hne s hs.1 hs.2)
    · intro s hs hs1
      exact mul_inv_cancel₀ (hne s hs hs1)
  · rintro ⟨g, -, hg⟩
    refine zeta_strip_iff_nonvanishing_right.mpr ?_
    intro s hs hs1 hz
    have := hg s hs hs1
    rw [hz, zero_mul] at this
    exact zero_ne_one this

theorem zeta_iff_reciprocal : ZetaForm ↔ ZetaReciprocalForm :=
  zeta_iff_zeta_strip.trans zeta_strip_iff_reciprocal

/-- The function `(s - 1) ζ(s)`, with the removable singularity at `s = 1` filled in with the
value `1` (the residue of `ζ` at its pole). -/
def zetaPoleFree : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1

lemma zetaPoleFree_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    zetaPoleFree s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

lemma continuous_zetaPoleFree : Continuous zetaPoleFree := by
  rw [continuous_iff_continuousAt]
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · have : ContinuousAt zetaPoleFree 1 := by
      rw [zetaPoleFree, continuousAt_update_same]
      exact riemannZeta_residue_one
    exact this
  · have hcont : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta s) s :=
      (continuous_id.sub continuous_const).continuousAt.mul
        (differentiableAt_riemannZeta hs).continuousAt
    refine hcont.congr ?_
    have hmem : {z : ℂ | z ≠ 1} ∈ nhds s := (isOpen_ne).mem_nhds hs
    filter_upwards [hmem] with z hz using (zetaPoleFree_of_ne_one hz).symm

/-- `(s - 1) ζ(s)`, with the removable singularity filled in, is entire. -/
lemma differentiable_zetaPoleFree : Differentiable ℂ zetaPoleFree := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · have hd : ∀ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, DifferentiableAt ℂ zetaPoleFree z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz1 : z ≠ 1 := hz
      have hdz : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) z :=
        ((differentiable_id.sub_const 1).differentiableAt).mul (differentiableAt_riemannZeta hz1)
      refine hdz.congr_of_eventuallyEq ?_
      have hmem : {w : ℂ | w ≠ 1} ∈ nhds z := (isOpen_ne).mem_nhds hz1
      filter_upwards [hmem] with w hw using zetaPoleFree_of_ne_one hw
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd
      continuous_zetaPoleFree.continuousAt).differentiableAt
  · have hdz : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) s :=
      ((differentiable_id.sub_const 1).differentiableAt).mul (differentiableAt_riemannZeta hs)
    refine hdz.congr_of_eventuallyEq ?_
    have hmem : {w : ℂ | w ≠ 1} ∈ nhds s := (isOpen_ne).mem_nhds hs
    filter_upwards [hmem] with w hw using zetaPoleFree_of_ne_one hw

theorem zeta_strip_iff_logBranch : ZetaStripForm ↔ ZetaLogBranchForm := by
  constructor
  · intro h
    have hne : ZetaNonvanishingRightForm := zeta_strip_iff_nonvanishing_right.mp h
    have hzero : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → zetaPoleFree s ≠ 0 := by
      intro s hs hs0
      rcases eq_or_ne s 1 with rfl | hs1
      · rw [zetaPoleFree, Function.update_self] at hs0
        exact one_ne_zero hs0
      · rw [zetaPoleFree_of_ne_one hs1] at hs0
        rcases mul_eq_zero.mp hs0 with h1 | h2
        · exact hs1 (by linear_combination h1)
        · exact hne s (by simpa using hs) hs1 h2
    obtain ⟨F, hFderiv, hFexp⟩ :=
      exists_holomorphic_log_halfPlane differentiable_zetaPoleFree hzero
    refine ⟨F, ?_, ?_⟩
    · intro s hs
      exact ((hFderiv s (by simpa using hs.1)).continuousAt).continuousWithinAt
    · intro s hs hs1
      rw [hFexp s (by simpa using hs), zetaPoleFree_of_ne_one hs1]
  · rintro ⟨f, -, hf⟩
    refine zeta_strip_iff_nonvanishing_right.mpr ?_
    intro s hs hs1 hz
    have := hf s hs hs1
    rw [hz, mul_zero] at this
    exact Complex.exp_ne_zero (f s) this

theorem zeta_iff_logBranch : ZetaForm ↔ ZetaLogBranchForm :=
  zeta_iff_zeta_strip.trans zeta_strip_iff_logBranch

/-- The zeros of `ζ` with imaginary part in `(0, T)` form a finite set: they are nontrivial
zeros of height at most `T`. -/
lemma finite_zeros_im_mem_Ioo (T : ℝ) :
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im < T}.Finite := by
  refine (finite_nontrivialZeros T).subset ?_
  rintro s ⟨hz, him0, himT⟩
  have htriv : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
    rintro ⟨n, rfl⟩
    simp at him0
  obtain ⟨h0, h1⟩ := zero_of_nontrivial_mem_strip hz htriv
  refine ⟨hz, h0, h1, ?_⟩
  rw [abs_of_pos him0]
  exact himT.le

theorem zeta_strip_iff_counting : ZetaStripForm ↔ ZetaCountingForm := by
  constructor
  · intro h T
    unfold criticalZeroCount zeroCount
    congr 1
    ext s
    constructor
    · rintro ⟨hz, -, him0, himT⟩
      exact ⟨hz, him0, himT⟩
    · rintro ⟨hz, him0, himT⟩
      have htriv : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
        rintro ⟨n, rfl⟩
        simp at him0
      obtain ⟨h0, h1⟩ := zero_of_nontrivial_mem_strip hz htriv
      exact ⟨hz, h s h0 h1 hz, him0, himT⟩
  · intro h
    refine zeta_strip_iff_upper_strip.mpr ?_
    intro s _ _ him hz
    set T := s.im + 1 with hT
    have hsub : {t : ℂ | riemannZeta t = 0 ∧ t.re = 1 / 2 ∧ 0 < t.im ∧ t.im < T} ⊆
        {t : ℂ | riemannZeta t = 0 ∧ 0 < t.im ∧ t.im < T} := by
      rintro t ⟨hz, -, h1, h2⟩
      exact ⟨hz, h1, h2⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (le_of_eq (h T).symm)
      (finite_zeros_im_mem_Ioo T)
    have hmem : s ∈ {t : ℂ | riemannZeta t = 0 ∧ 0 < t.im ∧ t.im < T} :=
      ⟨hz, him, by simp [hT]⟩
    exact ((heq ▸ hmem : s ∈ {t : ℂ | riemannZeta t = 0 ∧ t.re = 1 / 2 ∧ 0 < t.im ∧ t.im < T})).2.1

theorem zeta_iff_counting : ZetaForm ↔ ZetaCountingForm :=
  zeta_iff_zeta_strip.trans zeta_strip_iff_counting

lemma bddAbove_stripZeroRealParts : BddAbove stripZeroRealParts := by
  refine ⟨1, ?_⟩
  rintro x ⟨s, -, -, h1, rfl⟩
  exact h1.le

lemma stripZeroRealParts_nonempty : stripZeroRealParts.Nonempty := by
  obtain ⟨s, hz, h0, h1⟩ := nontrivialZeroSet_nonempty
  exact ⟨s.re, s, hz, h0, h1, rfl⟩

theorem zeta_strip_iff_sup : ZetaStripForm ↔ ZetaSupForm := by
  constructor
  · intro h
    have hset : stripZeroRealParts = {1 / 2} := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨?_, ?_⟩
      · obtain ⟨s, hz, h0, h1⟩ := nontrivialZeroSet_nonempty
        exact ⟨s, hz, h0, h1, h s h0 h1 hz⟩
      · rintro x ⟨s, hz, h0, h1, rfl⟩
        exact h s h0 h1 hz
    rw [ZetaSupForm, hset, csSup_singleton]
  · intro h s h0 h1 hz
    have h' : sSup stripZeroRealParts = 1 / 2 := h
    have hle : s.re ≤ 1 / 2 := by
      have hmem : s.re ∈ stripZeroRealParts := ⟨s, hz, h0, h1, rfl⟩
      have := le_csSup bddAbove_stripZeroRealParts hmem
      rwa [h'] at this
    have hz' : riemannZeta (1 - s) = 0 := riemannZeta_one_sub_eq_zero_of_mem_strip h0 h1 hz
    have hge : (1 - s).re ≤ 1 / 2 := by
      have hmem : (1 - s).re ∈ stripZeroRealParts := by
        refine ⟨1 - s, hz', ?_, ?_, rfl⟩ <;> simp <;> linarith
      have := le_csSup bddAbove_stripZeroRealParts hmem
      rwa [h'] at this
    simp only [Complex.sub_re, Complex.one_re] at hge
    linarith

theorem zeta_iff_sup : ZetaForm ↔ ZetaSupForm :=
  zeta_iff_zeta_strip.trans zeta_strip_iff_sup

end RiemannHypothesis

end
