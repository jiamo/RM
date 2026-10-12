/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Hecke/SignalBounds.lean
  Original module: OAI.NumberTheory.DirichletL.Hecke.SignalBounds
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.SignalShift
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.ReciprocalGrowth

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Topology
open MeasureTheory Set Filter Asymptotics
namespace SevenEighths.HeckeSignalBounds
open HeckeFamily HeckeSignal Continuation

theorem contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (7/8 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) {x : ℝ} (hx : 1≤x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*Complex.I) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact HeckeSignalShift.contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

theorem signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (7/8 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact HeckeSignalShift.signal_isBigO_atTop χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs)

end SevenEighths.HeckeSignalBounds

end

end RiemannHypothesis.Family003
