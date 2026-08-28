/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.EightyPercentSimple

/-!
# A route towards eighty per cent *on the critical line*, through the zeroes of `ξ′`

The unconditional proportion of nontrivial zeroes of `ζ` proved to lie on the critical line is
`2/3` (`RiemannHypothesis.two_thirds_on_critical_line`), and `2 − 1/c₁* = 0.67250…` with the
optimal window (`RiemannHypothesis.montgomery_taylor_on_critical_line`).  Raising it to `80 %`
is an open research problem.

This file records a *route* to a proportion beyond `80 %`, and proves everything on that route
except one classical input, which is stated as an explicit hypothesis and is **not** proved
here.  The route is:

* the zeroes of `ξ′` (the derivative of the completed zeta function) are known
  unconditionally to be `86.864 %` simple and on the critical line
  (`Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std`, restated in
  `RiemannHypothesis.EightyPercent`);
* the Riemann–von Mangoldt formula holds, with the *same* main term `(T/2π)·ℓ₁(T)`, for the
  zeroes of `ζ` and for the zeroes of `ξ′`.  Hence the two counting functions differ by
  `O(log T)` (`abs_xiDerivWindowCount_sub_windowCount_le`) and, since `N(T,2T)/log T → ∞`
  (`exists_le_windowCount_mul_log`), agree to within any `ε` proportion
  (`xiDerivWindowCount_le_one_add_mul`).  Both of these are *proved* here, from the two
  Riemann–von Mangoldt theorems of the vendored `Zeta23` library;
* **the missing input**, `SpeiserTransfer`: the counting form of Speiser's theorem — the number
  of zeroes of `ζ` off the critical line is at most the number of zeroes of `ξ′` that are off
  the line or multiple, up to `O(log T)`.  It is a `def … : Prop` here: a statement, not a
  theorem.  Proving it needs the argument principle for `ξ′/ξ` on the left half of the critical
  strip, which is not in this repository.  It should **not** be read as "the Levinson–Montgomery
  form of Speiser's theorem": Levinson–Montgomery counts zeroes of `ζ′`, not of `ξ′`, and does
  not prove this statement.  With multiplicity the analogous hypothesis is in fact equivalent to
  a reverse comparison of the *on-line* counts and already implies `86.864 %` on the critical
  line; see `RiemannHypothesis.SpeiserEquivalence` and the caveat on `SpeiserTransfer` below.

What the route then gives, all proved here:

* `offLine_le_of_speiserTransfer` — at most `13.136 %` of the zeroes lie off the critical line;
* `eighty_four_percent_distinct_on_critical_line_of_speiserTransfer` — **at least `84 %` of the
  *distinct* nontrivial zeroes of `ζ` lie on the critical line**, and hence
  `eightyPercentOnCriticalLineDistinct_of_speiserTransfer`: the `80 %` target for the distinct
  zeroes;
* `seventy_percent_on_critical_line_of_speiserTransfer` — at least `70 %` of the zeroes counted
  *with multiplicity* lie on the critical line, improving on the unconditional `2/3` — again,
  only under `SpeiserTransfer`.

The `80 %` target with multiplicity, `EightyPercentOnCriticalLine` of
`RiemannHypothesis.EightyPercentSimple`, is **not** reached even on this route: the loss comes
from the multiplicity budget `N_d ≥ (5/6)·N`.

Nothing here proves the Riemann hypothesis, and nothing here proves `SpeiserTransfer`.
-/

noncomputable section

open Complex Filter Set

namespace RiemannHypothesis

/-! ## The counting functions of `ζ` and of `ξ′` differ by `O(log T)`

Both `Zeta23.riemannVonMangoldt_zeta` and `Zeta23.XiPrime.xiDerivZeros₀_rvm` give the same main
term `(T/2π)·ℓ₁(T)` for the number of zeroes in the dyadic window `(T, 2T]`, so the difference
of the two counting functions is `O(log T)`. -/

lemma windowCount_rvm :
    ∃ C S : ℝ, ∀ T ≥ S,
      |(windowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T| ≤ C * Real.log T := by
  obtain ⟨C, S, h⟩ := Zeta23.riemannVonMangoldt_zeta.main
  refine ⟨C, S, fun T hT => ?_⟩
  have hmain := h T hT
  rwa [Zeta23.zetaZeroConfig_N, ← windowCount_eq] at hmain

lemma xiDerivWindowCount_rvm :
    ∃ C S : ℝ, ∀ T ≥ S,
      |(xiDerivWindowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T| ≤
        C * Real.log T := by
  obtain ⟨C, S, h⟩ := Zeta23.XiPrime.xiDerivZeros₀_rvm.main
  refine ⟨C, S, fun T hT => ?_⟩
  have hmain := h T hT
  have hN : Zeta23.XiPrime.xiDerivZeros₀.N T (2 * T) = Zeta23.XiPrime.Ncount T (2 * T) := by
    simp [Zeta23.XiPrime.xiDerivZeros₀]
  rwa [hN, ← xiDerivWindowCount_eq] at hmain

/-- The two counting functions differ by `O(log T)`. -/
lemma abs_xiDerivWindowCount_sub_windowCount_le :
    ∃ C S : ℝ, 0 ≤ C ∧ 1 ≤ S ∧ ∀ T ≥ S,
      |(xiDerivWindowCount T (2 * T) : ℝ) - (windowCount T (2 * T) : ℝ)| ≤ C * Real.log T := by
  obtain ⟨C₁, S₁, h₁⟩ := windowCount_rvm
  obtain ⟨C₂, S₂, h₂⟩ := xiDerivWindowCount_rvm
  refine ⟨|C₁| + |C₂|, max 1 (max S₁ S₂), by positivity, le_max_left _ _, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hs1 : S₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hT
  have hs2 : S₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hT
  have e1 : |(windowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T| ≤
      |C₁| * Real.log T :=
    (h₁ T hs1).trans (by nlinarith [le_abs_self C₁])
  have e2 : |(xiDerivWindowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T| ≤
      |C₂| * Real.log T :=
    (h₂ T hs2).trans (by nlinarith [le_abs_self C₂])
  have hsplit : (xiDerivWindowCount T (2 * T) : ℝ) - (windowCount T (2 * T) : ℝ) =
      ((xiDerivWindowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T) -
        ((windowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T) := by ring
  calc |(xiDerivWindowCount T (2 * T) : ℝ) - (windowCount T (2 * T) : ℝ)|
      = |((xiDerivWindowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T) -
          ((windowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T)| := by
        rw [hsplit]
    _ ≤ |(xiDerivWindowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T| +
          |(windowCount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T| := abs_sub _ _
    _ ≤ |C₂| * Real.log T + |C₁| * Real.log T := add_le_add e2 e1
    _ = (|C₁| + |C₂|) * Real.log T := by ring

/-! ## `N(T,2T)` grows faster than `log T` -/

/-- `e² ≥ 7`, an elementary bound used to compare `log (2π)` with `2`. -/
private lemma seven_le_exp_two : (7 : ℝ) ≤ Real.exp 2 := by
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]

/-- `log (2π) ≤ 2`. -/
private lemma log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have h1 : (2 : ℝ) * Real.pi ≤ Real.exp 2 := by linarith [seven_le_exp_two]
  have h2 := Real.log_le_log (by positivity) h1
  rwa [Real.log_exp] at h2

/-- `N(T, 2T)/log T → ∞`: for every `K` one has `K·log T ≤ N(T,2T)` for all large `T`.  A
consequence of the Riemann–von Mangoldt formula, whose main term is `≍ T log T`. -/
lemma exists_le_windowCount_mul_log (K : ℝ) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ T ≥ S, K * Real.log T ≤ (windowCount T (2 * T) : ℝ) := by
  obtain ⟨C, S, h⟩ := windowCount_rvm
  refine ⟨max (Real.exp 4) (max S (14 * (K + |C|) + 14)), ?_, fun T hT => ?_⟩
  · have h1 : (1 : ℝ) ≤ Real.exp 4 := Real.one_le_exp_iff.2 (by norm_num)
    exact le_trans h1 (le_max_left _ _)
  have hexp : Real.exp 4 ≤ T := le_trans (le_max_left _ _) hT
  have hS : S ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hbig : 14 * (K + |C|) + 14 ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 4) hexp
  have hlog4 : (4 : ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 4) hexp
    rwa [Real.log_exp] at this
  have hlog0 : (0 : ℝ) ≤ Real.log T := by linarith
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hell : Real.log T - 2 ≤ Zeta23.ell1 T := by
    have hdiv : Real.log (T / (2 * Real.pi)) = Real.log T - Real.log (2 * Real.pi) :=
      Real.log_div (ne_of_gt hT0) (by positivity)
    have hlog2 : (0 : ℝ) ≤ 2 * Real.log 2 - 1 := by
      nlinarith [Real.log_two_gt_d9]
    simp only [Zeta23.ell1, Zeta23.l, hdiv]
    linarith [log_two_pi_le_two]
  have hell0 : Real.log T / 2 ≤ Zeta23.ell1 T := by linarith
  have hmain : T / 14 * Real.log T ≤ T / (2 * Real.pi) * Zeta23.ell1 T := by
    have h7 : 2 * Real.pi ≤ 7 := by linarith
    have h1 : T / 7 ≤ T / (2 * Real.pi) :=
      div_le_div_of_nonneg_left hT0.le (by positivity) h7
    have h2 : T / 14 * Real.log T ≤ T / 7 * Zeta23.ell1 T := by
      have : T / 7 * (Real.log T / 2) ≤ T / 7 * Zeta23.ell1 T :=
        mul_le_mul_of_nonneg_left hell0 (by positivity)
      linarith [this]
    have h3 : T / 7 * Zeta23.ell1 T ≤ T / (2 * Real.pi) * Zeta23.ell1 T := by
      have hpos : 0 ≤ Zeta23.ell1 T := by linarith
      exact mul_le_mul_of_nonneg_right h1 hpos
    linarith
  have hbound := abs_le.1 (h T hS)
  have hlow : T / (2 * Real.pi) * Zeta23.ell1 T - C * Real.log T ≤
      (windowCount T (2 * T) : ℝ) := by linarith [hbound.1]
  have habs : C ≤ |C| := le_abs_self C
  have hstep : K * Real.log T ≤ T / 14 * Real.log T - |C| * Real.log T := by
    have hKC : K + |C| ≤ T / 14 := by linarith
    nlinarith [hlog0]
  nlinarith [hlog0, habs]

/-- The two counting functions agree to within any prescribed proportion. -/
lemma xiDerivWindowCount_le_one_add_mul {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ T ≥ S,
      (xiDerivWindowCount T (2 * T) : ℝ) ≤ (1 + ε) * (windowCount T (2 * T) : ℝ) := by
  obtain ⟨C, S₁, hC0, hS₁, hC⟩ := abs_xiDerivWindowCount_sub_windowCount_le
  obtain ⟨S₂, hS₂, hgrow⟩ := exists_le_windowCount_mul_log (C / ε)
  refine ⟨max S₁ S₂, le_trans hS₁ (le_max_left _ _), fun T hT => ?_⟩
  have h1 := hC T (le_trans (le_max_left _ _) hT)
  have h2 := hgrow T (le_trans (le_max_right _ _) hT)
  have hlogle : C * Real.log T ≤ ε * (windowCount T (2 * T) : ℝ) := by
    have hmul : ε * (C / ε * Real.log T) ≤ ε * (windowCount T (2 * T) : ℝ) :=
      mul_le_mul_of_nonneg_left h2 hε.le
    have heq : ε * (C / ε * Real.log T) = C * Real.log T := by
      field_simp
    linarith [hmul, heq.symm.le, heq.le]
  linarith [(abs_le.1 h1).2]

/-! ## The unconditional bound on the `ξ′` side -/

/-- The zeroes of `ξ′` in the window that are **not** simple-and-on-the-critical-line, counted
with multiplicity: `N_{ξ′} − N₀ˢ_{ξ′}`.  The unconditional `ξ′` theorem bounds this by
`0.13136·N_{ξ′}`. -/
def xiDerivWindowCountBad (T₁ T₂ : ℝ) : ℝ :=
  (xiDerivWindowCount T₁ T₂ : ℝ) - (xiDerivWindowCountSimpleOnLine T₁ T₂ : ℝ)

/-- **Unconditionally**, the `ξ′` bad count is at most `(0.13136 + ε)·N(T,2T)`: the `ξ′`
theorem bounds it by `0.13136·N_{ξ′}`, and `N_{ξ′} ≤ (1+ε)·N`. -/
theorem xiDerivWindowCountBad_le {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ T ≥ S,
      xiDerivWindowCountBad T (2 * T) ≤ (0.13136 + ε) * (windowCount T (2 * T) : ℝ) := by
  obtain ⟨S₁, h₁⟩ := Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std
  obtain ⟨S₂, -, h₂⟩ := xiDerivWindowCount_le_one_add_mul (ε := ε) hε
  refine ⟨max S₁ S₂, fun T hT => ?_⟩
  have hquartic := (h₁ T (le_trans (le_max_left _ _) hT)).1
  have hcomp := h₂ T (le_trans (le_max_right _ _) hT)
  have hN0 : (0 : ℝ) ≤ (windowCount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hbad : xiDerivWindowCountBad T (2 * T) ≤
      0.13136 * (xiDerivWindowCount T (2 * T) : ℝ) := by
    rw [xiDerivWindowCountBad, xiDerivWindowCount_eq, xiDerivWindowCountSimpleOnLine_eq]
    linarith
  nlinarith [hbad, hcomp, hN0, mul_nonneg hε.le hN0]

/-! ## The missing input: the counting form of Speiser's theorem -/

/-- **A counting form of Speiser's theorem**, as a `Prop` (no classical theorem is being
attributed here; see the caveat below): the number of
distinct zeroes of `ζ` off the critical line in a dyadic window is at most the number of zeroes
of `ξ′` there that are off the line or multiple, up to `O(log T)`.

This is a *statement*, in the style of `RiemannHypothesis.Partial`: it is **not** proved in this
repository, and it is the only unproved input of the theorems below.  Its motivation is
Speiser's theorem ("RH is equivalent to `ξ′` having no zero to the left of the critical line").

**Caveat on the strength of this hypothesis** (added after the analysis in
`RiemannHypothesis.SpeiserEquivalence`; the earlier attribution of this exact statement to
Levinson–Montgomery was misleading and has been removed).  Levinson–Montgomery is a theorem
about the zeroes of `ζ′`, not about those of `ξ′`, and it is *not* a proof of this `Prop`.
Moreover, counted with multiplicity the corresponding hypothesis is not a weak one:
`RiemannHypothesis.speiserOffLineTransfer_iff_xiDerivOnLineDominates` shows that it is
*equivalent* to the reverse comparison of the on-line counts, whose easy half
(`RiemannHypothesis.xiDerivWindowCountOffLineMult_le_windowCountOffLineMult`, from Rolle's
theorem for Hardy's `Ξ`) is all that is unconditional, and
`RiemannHypothesis.eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer` shows
that it already implies `86.864 %` of the zeroes of `ζ` on the critical line — more than the
`80 %` target of this file.  The unconditional proportion in this repository remains `2/3`
(`RiemannHypothesis.two_thirds_on_critical_line`). -/
def SpeiserTransfer : Prop :=
  ∃ C S : ℝ, ∀ T ≥ S,
    (windowCountOffLine T (2 * T) : ℝ) ≤
      xiDerivWindowCountBad T (2 * T) + C * Real.log T

/-! ## What the route gives -/

/-- Under `SpeiserTransfer`: at most `13.136 %` of the nontrivial zeroes of `ζ` lie off the
critical line. -/
theorem offLine_le_of_speiserTransfer (h : SpeiserTransfer) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ T ≥ S,
      (windowCountOffLine T (2 * T) : ℝ) ≤ (0.13136 + ε) * (windowCount T (2 * T) : ℝ) := by
  obtain ⟨C, S₀, hS₀⟩ := h
  obtain ⟨S₁, h₁⟩ := xiDerivWindowCountBad_le (ε := ε / 2) (by positivity)
  obtain ⟨S₂, hS₂, h₂⟩ := exists_le_windowCount_mul_log (2 * |C| / ε)
  refine ⟨max S₀ (max S₁ S₂), fun T hT => ?_⟩
  have hs0 : S₀ ≤ T := le_trans (le_max_left _ _) hT
  have hs1 : S₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hs2 : S₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT1 : (1 : ℝ) ≤ T := le_trans hS₂ hs2
  have hlog0 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT1
  have hspeiser := hS₀ T hs0
  have hbad := h₁ T hs1
  have hgrow := h₂ T hs2
  -- the `O(log T)` term is absorbed into `ε/2 · N`
  have hCabs : C * Real.log T ≤ ε / 2 * (windowCount T (2 * T) : ℝ) := by
    have hle : C * Real.log T ≤ |C| * Real.log T := by
      nlinarith [le_abs_self C]
    have hmul : ε / 2 * (2 * |C| / ε * Real.log T) ≤ ε / 2 * (windowCount T (2 * T) : ℝ) :=
      mul_le_mul_of_nonneg_left hgrow (by positivity)
    have heq : ε / 2 * (2 * |C| / ε * Real.log T) = |C| * Real.log T := by
      field_simp
    linarith [hle, hmul, heq.symm.le, heq.le]
  linarith [hspeiser, hbad, hCabs]

/-- **Under `SpeiserTransfer`: at least `84 %` of the *distinct* nontrivial zeroes of `ζ` lie on
the critical line.**  (Unconditionally the repository proves `2/3`.) -/
theorem eighty_four_percent_distinct_on_critical_line_of_speiserTransfer (h : SpeiserTransfer) :
    ∃ S : ℝ, ∀ T ≥ S,
      (0.84 : ℝ) * (windowCountDistinct T (2 * T) : ℝ) ≤ (windowCountOnLine T (2 * T) : ℝ) := by
  obtain ⟨S₁, h₁⟩ := offLine_le_of_speiserTransfer h (ε := 1 / 10000) (by norm_num)
  obtain ⟨S₂, h₂⟩ := five_sixths_distinct (1 / 10000) (by norm_num)
  refine ⟨max S₁ S₂, fun T hT => ?_⟩
  have hoff := h₁ T (le_trans (le_max_left _ _) hT)
  have hdist := h₂ T (le_trans (le_max_right _ _) hT)
  have hsplit : (windowCountOffLine T (2 * T) : ℝ) + (windowCountOnLine T (2 * T) : ℝ)
      = (windowCountDistinct T (2 * T) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (windowCountOffLine_add_windowCountOnLine T (2 * T))
  linarith

/-- **Under `SpeiserTransfer`: at least `70 %` of the nontrivial zeroes of `ζ`, counted with
multiplicity, lie on the critical line** — improving on the unconditional `2/3`. -/
theorem seventy_percent_on_critical_line_of_speiserTransfer (h : SpeiserTransfer) :
    ∃ S : ℝ, ∀ T ≥ S,
      (0.7 : ℝ) * (windowCount T (2 * T) : ℝ) ≤ (windowCountOnLine T (2 * T) : ℝ) := by
  obtain ⟨S₁, h₁⟩ := offLine_le_of_speiserTransfer h (ε := 1 / 10000) (by norm_num)
  obtain ⟨S₂, h₂⟩ := five_sixths_distinct (1 / 10000) (by norm_num)
  refine ⟨max S₁ S₂, fun T hT => ?_⟩
  have hoff := h₁ T (le_trans (le_max_left _ _) hT)
  have hdist := h₂ T (le_trans (le_max_right _ _) hT)
  have hsplit : (windowCountOffLine T (2 * T) : ℝ) + (windowCountOnLine T (2 * T) : ℝ)
      = (windowCountDistinct T (2 * T) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (windowCountOffLine_add_windowCountOnLine T (2 * T))
  linarith

/-! ## The eighty per cent target for the distinct zeroes -/

/-- **The eighty per cent statement for the critical line, distinct zeroes**, as a `Prop`:
`liminf N₀*(T,2T)/N_d(T,2T) ≥ 4/5`, i.e. at least `80 %` of the *distinct* nontrivial zeroes of
`ζ` lie on the critical line.  Compare `EightyPercentOnCriticalLine`, whose denominator is the
count with multiplicity. -/
def EightyPercentOnCriticalLineDistinct : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (4 / 5 - ε) * (windowCountDistinct T (2 * T) : ℝ) ≤ (windowCountOnLine T (2 * T) : ℝ)

/-- Under `SpeiserTransfer`, the eighty per cent target for the distinct zeroes holds (with
`0.84` to spare).  `SpeiserTransfer` is **not** proved here. -/
theorem eightyPercentOnCriticalLineDistinct_of_speiserTransfer (h : SpeiserTransfer) :
    EightyPercentOnCriticalLineDistinct := by
  intro ε hε
  obtain ⟨S, hS⟩ := eighty_four_percent_distinct_on_critical_line_of_speiserTransfer h
  refine ⟨S, fun T hT => ?_⟩
  have hd : (0 : ℝ) ≤ (windowCountDistinct T (2 * T) : ℝ) := Nat.cast_nonneg _
  nlinarith [hS T hT, mul_nonneg hε.le hd]

end RiemannHypothesis

end
