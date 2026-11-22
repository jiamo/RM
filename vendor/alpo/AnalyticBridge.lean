import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
import Formalism.GammaFactorNonvanishing.RhOfRight
import RiemannHypothesis.Main
import RiemannHypothesis.Symmetry
import RiemannHypothesis.ZeroExists

/-!
# AnalyticBridge: the analytic half of the alpo.ge proof, against this repository's statements

The alpo.ge development proves RH in two halves (see `riemann_hypothesis.pdf`, Sections 2
and 10–11):

* **analytic half** (Theorem 2.2 / Corollary 2.5 of the paper): a one-sided bound
  `G(y) ≤ C y^θ` for a positive combination of smoothed prime sums, on arbitrarily distant
  windows `[Y, Y^{1+δ}]`, excludes every zero with `re s > θ`.  It is proved in the tree by 31
  modules that import only Mathlib (`Deduction.zeroFree_of_rpow_window`,
  `Formalism.VW.rh_of_right`); `tools/analytic.sh` compiles them, and this file, in minutes.
* **arithmetic half**: the bound itself, `H_ψ(y) ≤ y^{1/2+9ε}` on such windows (paper (1.3)),
  built from theta towers, arithmetic slopes, Galois representations and Selmer bounds: the
  remaining 175,000 modules.  It is checked only through the full build (`Bridge.lean`,
  `Verify.lean`) and the independent verification reported in `README.md`.

This file states the interface between the halves for `ζ` alone in Mathlib's vocabulary
(`smoothedChebyshevError`, `WindowBound`) and proves `WindowBound → ZetaForm` with the tree's
analytic theorems, then `ZetaStripForm` and `EtaForm` through this repository's own
equivalences.  Everything a reader must trust about the arithmetic half is therefore the single
statement `WindowBound` (the `ψ = 1` case of (1.3); the tree proves the general `ψ` version).

The same analytic theorem also runs the other way, and then needs nothing from the arithmetic
half.  `ζ` has a zero with `re ρ ≥ 1/2` (this repository proves a zero in the critical strip,
`RiemannHypothesis.exists_riemannZeta_eq_zero_of_mem_strip`, and `s ↦ 1 - s` reflects it), so by
contraposition no bound `G₁(y) ≤ C y^θ` with `θ < 1/2` can hold on arbitrarily distant windows:
every window `[Y, Y^{1+δ}]` far enough out contains a point with `G₁(y) > C y^θ`
(`exists_gt_rpow_mem_window`).  These theorems are unconditional.  They show that the range
`θ > 1/2` in `WindowBound` cannot be extended below `1/2` (`not_windowBound_of_lt_half`).  They
also give `G₁(y) = Ω₊(y^θ)` for every `θ < 1/2` (`frequently_gt_rpow`).  The classical
statements are stronger: E. Schmidt (1903) proved `ψ(x) − x = Ω±(x^{1/2})`, two-sided and
without the loss of an `ε`, and Landau's theorem on Dirichlet series with nonnegative
coefficients (1905) gives `Ω±(x^{β−ε})` for every zero `β + iγ`.  The version here is
one-sided, for the smoothed sum, and loses the `ε`, but it is localized to windows.

Hypothesis hygiene (`AGENTS.md`), for `WindowBound`:
1. *Direction.*  `WindowBound → RH` is the theorem below.  The converse also holds (under RH,
   `|G₁(y)| ≪ y^{1/2} log² y` by the explicit formula; not formalized here), so `WindowBound`
   is equivalent to RH: it is an interface, not a weaker hypothesis.
2. *Strength.*  Exactly RH-strength, by 1.
3. *Non-triviality.*  The only proof of `WindowBound` available is the tree's arithmetic half.
   This file does not make RH more plausible by itself; it isolates what the tree must supply.
4. *Attribution.*  Landau, *Über einen Satz von Tschebyschef*, Math. Ann. 61 (1905): positivity
   of the coefficients of `-ζ'/ζ` lets a one-sided bound locate the first singularity.  The
   window formulation is the alpo.ge development's (paper, Theorem 2.2).

Not a theorem of this repository: it lives in `vendor/alpo` and is compiled only by
`vendor/alpo/tools/analytic.sh`, together with the 31 tree modules and the 23 modules of this
repository it imports.  The `#print axioms` lines must show only `propext`,
`Classical.choice`, `Quot.sound`.
-/

open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace AlpoAnalytic

/-- `Σ_{n ≤ y} Λ(n) (y/n − 1)₊ − y log y + (1 + γ) y`: the smoothed Chebyshev sum with its
main terms removed (`G₁` in the paper, (1.1)).  Mathlib notions only. -/
def smoothedChebyshevError (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * max (y / n - 1) 0) - y * Real.log y +
    (1 + Real.eulerMascheroniConstant) * y

/-- For every exponent `θ ∈ (1/2, 1)`: `smoothedChebyshevError y ≤ y^θ` on some window
`[Y, Y^{3/2}]` beyond any prescribed `Y₀`.  One-sided, and only on windows: the shape of the
paper's (1.3) for the character of conductor 1. -/
def WindowBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
    ∀ y ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)), smoothedChebyshevError y ≤ y ^ θ

/-- `ζ` as a one-member family of the tree's analytic engine: the character mod 1, weight 1. -/
def zetaFamily : Deduction.CharFamily where
  ι := Unit
  N := fun _ => 1
  χ := fun _ => 1
  a := fun _ => 1
  a_pos := fun _ => one_pos
  adm := fun _ => Or.inl rfl

theorem one_apply_modOne (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
  rw [Subsingleton.elim (n : ZMod 1) 1, map_one]

/-- The tree's weighted sum for this family is exactly `smoothedChebyshevError`. -/
theorem gm_zetaFamily (y : ℝ) : Deduction.Gm zetaFamily y = smoothedChebyshevError y := by
  change ∑ _i : Unit, (1 : ℝ) * (Deduction.Gchi (1 : DirichletCharacter ℂ 1) y).re = _
  rw [Fintype.sum_unique, one_mul, Deduction.Gchi, if_pos rfl, smoothedChebyshevError,
    Deduction.ramp]
  simp [one_apply_modOne, Complex.re_sum]

/-- **The analytic half, for `ζ`.**  A one-sided window bound on the smoothed prime sum gives
this repository's statement of record. -/
theorem zetaForm_of_windowBound (h : WindowBound) : RiemannHypothesis.ZetaForm := by
  refine Formalism.VW.rh_of_right fun s hs _ => ?_
  set θ : ℝ := min ((1 / 2 + s.re) / 2) (3 / 4) with hθdef
  have hθ0 : 1 / 2 < θ := lt_min (by linarith) (by norm_num)
  have hθ1 : θ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθs : θ < s.re := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have e : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  have hz := Deduction.zeroFree_of_rpow_window zetaFamily (θ := θ) (δ := 1 / 2) (C := 1)
    (by linarith) hθ1 (by norm_num) (fun Y₀ => by
      obtain ⟨Y, hY, hb⟩ := h θ hθ0 hθ1 Y₀
      refine ⟨Y, hY, fun y hy => ?_⟩
      rw [e] at hy
      rw [gm_zetaFamily, one_mul]
      exact hb y hy) () s hθs
  have hz' : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 := hz
  rwa [DirichletCharacter.LFunction_modOne_eq] at hz'

theorem zetaStripForm_of_windowBound (h : WindowBound) : RiemannHypothesis.ZetaStripForm :=
  RiemannHypothesis.zeta_iff_zeta_strip.mp (zetaForm_of_windowBound h)

/-- The elementary form: no analytic continuation in the statement (`dirichletEta` is a paired
series, `RiemannHypothesis/Defs.lean`). -/
theorem etaForm_of_windowBound (h : WindowBound) : RiemannHypothesis.EtaForm :=
  RiemannHypothesis.zeta_iff_eta.mp (zetaForm_of_windowBound h)

/-! ## The converse direction: oscillation, unconditionally -/

/-- `ζ` has a zero on or to the right of the critical line: a zero in the critical strip,
reflected by `s ↦ 1 - s` if it lies to the left. -/
theorem exists_riemannZeta_eq_zero_half_le_re : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re := by
  obtain ⟨s, hz, h0, h1⟩ := RiemannHypothesis.exists_riemannZeta_eq_zero_of_mem_strip
  rcases le_or_gt (1 / 2) s.re with hs | hs
  · exact ⟨s, hz, hs⟩
  · refine ⟨1 - s, RiemannHypothesis.riemannZeta_one_sub_eq_zero_of_mem_strip h0 h1 hz, ?_⟩
    rw [Complex.sub_re, Complex.one_re]
    linarith

/-- **Oscillation in every window.**  For `0 < θ < 1/2`, `δ > 0` and any constant `C`, every
window `[Y, Y^{1+δ}]` far enough out contains a point where the smoothed Chebyshev error
exceeds `C y^θ`.  The contrapositive of the tree's analytic theorem, applied to a zero of `ζ`
with `re ρ ≥ 1/2`. -/
theorem exists_gt_rpow_mem_window {θ δ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hδ : 0 < δ)
    (C : ℝ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∃ y ∈ Set.Icc Y (Y ^ (1 + δ)),
      C * y ^ θ < smoothedChebyshevError y := by
  by_contra H
  push Not at H
  obtain ⟨ρ, hρ, hre⟩ := exists_riemannZeta_eq_zero_half_le_re
  have hz := Deduction.zeroFree_of_rpow_window zetaFamily (θ := θ) (δ := δ) (C := C) hθ0
    (by linarith) hδ (fun Y₀ => by
      obtain ⟨Y, hY, hb⟩ := H Y₀
      refine ⟨Y, hY, fun y hy => ?_⟩
      rw [gm_zetaFamily]
      exact hb y hy) () ρ (by linarith)
  have hz' : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ ≠ 0 := hz
  rw [DirichletCharacter.LFunction_modOne_eq] at hz'
  exact hz' hρ

/-- **`G₁(y) = Ω₊(y^θ)` for every `θ < 1/2`**: `smoothedChebyshevError y > C y^θ` for
arbitrarily large `y`, whatever the constant `C`. -/
theorem frequently_gt_rpow {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (C : ℝ) :
    ∃ᶠ y in Filter.atTop, C * y ^ θ < smoothedChebyshevError y := by
  obtain ⟨Y₀, hY₀⟩ := exists_gt_rpow_mem_window (δ := 1) hθ0 hθ one_pos C
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨y, hy, hgt⟩ := hY₀ (max a Y₀) (le_max_right a Y₀)
  exact ⟨y, (le_max_left a Y₀).trans hy.1, hgt⟩

/-- **The exponent `1/2` of `WindowBound` is sharp**: for `θ < 1/2` the window bound that
`WindowBound` asserts for `θ > 1/2` is false. -/
theorem not_windowBound_of_lt_half {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ¬ ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)), smoothedChebyshevError y ≤ y ^ θ := by
  intro H
  obtain ⟨Y₀, hY₀⟩ := exists_gt_rpow_mem_window (δ := 1 / 2) hθ0 hθ (by norm_num) 1
  obtain ⟨Y, hY, hb⟩ := H Y₀
  obtain ⟨y, hy, hgt⟩ := hY₀ Y hY
  have e : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [e] at hy
  have hle := hb y hy
  rw [one_mul] at hgt
  linarith

end AlpoAnalytic

end

-- The general engine, as proved in the tree (paper, Corollary 2.5): any finite family of
-- characters with positive weights.
#check @Deduction.zeroFree_of_rpow_window

#print axioms Deduction.zeroFree_of_rpow_window
#print axioms Formalism.VW.rh_of_right
#print axioms AlpoAnalytic.zetaForm_of_windowBound
#print axioms AlpoAnalytic.zetaStripForm_of_windowBound
#print axioms AlpoAnalytic.etaForm_of_windowBound
#print axioms AlpoAnalytic.exists_riemannZeta_eq_zero_half_le_re
#print axioms AlpoAnalytic.exists_gt_rpow_mem_window
#print axioms AlpoAnalytic.frequently_gt_rpow
#print axioms AlpoAnalytic.not_windowBound_of_lt_half
