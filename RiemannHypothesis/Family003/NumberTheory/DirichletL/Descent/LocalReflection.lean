/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.LocalReflection
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseMoment

open scoped BigOperators Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

def zeroMark (x : F) : ℂ := if x = 0 then 1 else 0

def localFourier (f : F → ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ t : F, f t * ψ (-(h * t))

theorem localFourier_zeroMark (ψ : AddChar F ℂ) (h : F) :
    localFourier zeroMark ψ h = 1 := by
  simp [localFourier, zeroMark]

theorem localFourier_trivial_nonzero (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (h : F) (hh : h ≠ 0) :
    localFourier (fun t => (1 : MulChar F ℂ) t) ψ h = -1 := by
  have he := gaussSum_one_left (hψ (neg_ne_zero.mpr hh))
  simpa only [gaussSum, AddChar.mulShift_apply, neg_mul, localFourier] using he

omit [Fintype F] in
theorem zeroMark_complement (x : F) :
    zeroMark x = 1 - (1 : MulChar F ℂ) x := by
  by_cases hx : x = 0
  · simp [zeroMark, hx, MulChar.map_zero]
  · rw [zeroMark, ite_eq_right hx, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    ring

def localReflectionActive (f : F → ℂ) (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ h : Fˣ,
    localFourier f ψ h * ((χ⁻¹) ^ 2) (σ * h) *
      ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))

theorem marked_active_eq_neg_trivial (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      -localReflectionActive (fun t => (1 : MulChar F ℂ) t) χ ψ σ ε x := by
  unfold localReflectionActive
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [localFourier_zeroMark, localFourier_trivial_nonzero ψ hψ h (Units.ne_zero h)]
  ring

theorem marked_inactive_coefficient (ψ : AddChar F ℂ) :
    (Fintype.card F : ℂ)⁻¹ * localFourier zeroMark ψ 0 =
      (Fintype.card F : ℂ)⁻¹ := by
  rw [localFourier_zeroMark, mul_one]

end

end SevenEighths.InverseMoment

end RiemannHypothesis.Family003
