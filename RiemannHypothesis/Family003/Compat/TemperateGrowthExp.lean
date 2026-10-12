/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

The absorbed proofs were written against Lean v4.34.1 and Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612.  At the host pin (Lean v4.33.0, Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d) the lemma below does not exist.

  * `Complex.hasTemperateGrowth_exp_mul_I`: the character `x ↦ exp (x i)` on `ℝ` has
    temperate growth (Mathlib d13f23b7, `Mathlib/Analysis/Distribution/TemperateGrowth.lean`;
    Mathlib is Apache 2.0, copyright of the respective Mathlib authors).  The statement is the
    one used by the absorbed sources; the proof here is new: every iterated derivative is
    `iⁿ exp (x i)`, of norm `1`.

Proof status: NEWLY PROVED FOR COMPATIBILITY.
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace RiemannHypothesis.Family003.Compat

open Complex in
/-- The iterated derivatives of `x ↦ exp (x i)` on `ℝ`. -/
theorem iteratedDeriv_exp_ofReal_mul_I (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Complex.exp (x * I)) =
      fun x : ℝ => I ^ n * Complex.exp (x * I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h : HasDerivAt (fun x : ℝ => Complex.exp (x * I)) (Complex.exp (x * I) * I) x :=
      ((hasDerivAt_id x).ofReal_comp.mul_const I).cexp.congr_deriv (by simp)
    rw [(h.const_mul (I ^ n)).deriv]
    ring

end RiemannHypothesis.Family003.Compat

/-- The character `x ↦ exp (x i)` on `ℝ` has temperate growth. -/
theorem Complex.hasTemperateGrowth_exp_mul_I :
    (fun x : ℝ => Complex.exp (x * Complex.I)).HasTemperateGrowth := by
  refine ⟨?_, fun n => ⟨0, 1, fun x => ?_⟩⟩
  · exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    RiemannHypothesis.Family003.Compat.iteratedDeriv_exp_ofReal_mul_I]
  simp [Complex.norm_exp_ofReal_mul_I]
