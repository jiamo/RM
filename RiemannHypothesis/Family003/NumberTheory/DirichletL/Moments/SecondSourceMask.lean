/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/SecondSourceMask.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.SecondSourceMask
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.SecondSectorColumns
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.AmplificationLiveMask
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSourceMask
open CanonicalQuadraticSieve CenteredMomentSecondSectorColumns CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem divisor_dvd_common (C D a b s : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hsI : s∣C*a) (hsJ : s∣D*b) : s∣C ∧ s∣D := by
  have hDa := (coprime_of_same_support C D a hC hD ha hCD).mp hCa
  have hDb := (coprime_of_same_support C D b hC hD hb hCD).mp hCb
  have hsa : IsCoprime s a := ((hDa.symm.mul_right hab).of_isCoprime_of_dvd_right hsJ).symm
  have hsb : IsCoprime s b := ((hCb.symm.mul_right hab.symm).of_isCoprime_of_dvd_right hsI).symm
  exact ⟨hsa.dvd_mul_right_iff.mp hsI,hsb.dvd_mul_right_iff.mp hsJ⟩

variable {ι : Type*} [Fintype ι]

theorem column_nonzero_divisor (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O)
    (h : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) : s∣I := by
  rw [column_mask] at h
  by_contra hn
  exact h (by rw [ite_eq_right hn,mul_zero])

theorem source_pair_divisor_common (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hleft : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)≠0)
    (hright : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (D*b)≠0) : s∣C ∧ s∣D :=
  divisor_dvd_common C D a b s hC hD ha hb hCD hCa hCb hab
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hleft)
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hright)

end SevenEighths.CenteredMomentSecondSourceMask

end

end RiemannHypothesis.Family003
