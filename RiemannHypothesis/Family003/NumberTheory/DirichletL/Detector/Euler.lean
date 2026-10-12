/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/Euler.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.Euler
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - proof tweak: after convert, close residual instance-equality goals with 'with_reducible_and_instances rfl' (host instances are not reducibly defeq)
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace RiemannHypothesis.Family003

noncomputable section
namespace SevenEighths.ProbeEuler

def markedFactor (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ((R * (1 - qInv) - K * V ^ a) / (1 - V) + J) / (1 - R)

def markedTableSeries (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ∑' r : ℕ, R ^ r *
    ((∑' m : ℕ, (R * (1 - qInv) * V ^ m - K * V ^ (m + a))) + J)

theorem marked_table_resummation (R V qInv K J : ℂ) (a : ℕ)
    (hR : ‖R‖ < 1) (hV : ‖V‖ < 1) :
    markedTableSeries R V qInv K J a = markedFactor R V qInv K J a := by
  have hgeo := hasSum_geometric_of_norm_lt_one hV
  have hfirst := hgeo.mul_left (R * (1 - qInv))
  have hsecond : HasSum (fun m : ℕ => K * V ^ (m + a))
      (K * V ^ a * (1 - V)⁻¹) := by
    convert hgeo.mul_left (K * V ^ a) using 1
    all_goals try with_reducible_and_instances rfl
    funext m
    rw [pow_add]
    ring
  have hin := (hfirst.sub hsecond).tsum_eq
  unfold markedTableSeries
  rw [hin, tsum_mul_right, tsum_geometric_of_norm_lt_one hR]
  unfold markedFactor
  simp only [div_eq_mul_inv]
  ring

theorem unramified_marked_error (R V qInv K W D : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * ((1 - qInv) + (1 - V) * (W - D)) - K * V) /
        ((1 - R) * (1 - V)) := by
  unfold markedFactor
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end RiemannHypothesis.Family003
