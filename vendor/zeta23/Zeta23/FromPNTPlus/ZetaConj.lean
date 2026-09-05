/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaConj.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Zeta23.ZetaReflect

open scoped Complex ComplexConjugate

theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  by_cases hf : DifferentiableAt ℂ f p
  · have h := hf.hasDerivAt.conj_conj
    simpa [Function.comp_def] using h.deriv
  · have h2 : ¬ DifferentiableAt ℂ (fun z ↦ conj (f (conj z))) (conj p) := by
      intro hd
      exact hf (by simpa [Function.comp_def] using hd.conj_conj)
    rw [deriv_zero_of_not_differentiableAt h2, deriv_zero_of_not_differentiableAt hf,
      map_zero]

/- **Schwarz reflection for ζ**, in the unconditional form.  This statement is now provided
verbatim by mathlib as `riemannZeta_conj` (`Mathlib.NumberTheory.Harmonic.ZetaAsymp`, imported
above), so re-declaring it here is a name clash; the original port is kept for the record.

/-- **Schwarz reflection for ζ**, in the unconditional form: away from `s = 1` this is
`Zeta23.riemannZeta_conj`, and at `s = 1` Mathlib's value of `ζ` is real. -/
theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  rcases eq_or_ne s 1 with rfl | hs
  · rw [map_one, riemannZeta_one,
      show ((4 : ℂ) * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity),
      show ((Real.eulerMascheroniConstant : ℂ) - ((Real.log (4 * Real.pi) : ℝ) : ℂ)) / 2
        = (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 : ℝ) : ℂ) by
          push_cast; ring,
      Complex.conj_ofReal]
  · exact Zeta23.riemannZeta_conj hs
-/

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  rw [← deriv_conj_conj' riemannZeta s]
  congr 1
  funext z
  rw [← riemannZeta_conj (conj z), Complex.conj_conj]

theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s

theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]
