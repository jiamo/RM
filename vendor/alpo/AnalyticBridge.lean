import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
import Formalism.GammaFactorNonvanishing.RhOfRight
import RiemannHypothesis.Main

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
`vendor/alpo/tools/analytic.sh`.  The `#print axioms` lines must show only `propext`,
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
