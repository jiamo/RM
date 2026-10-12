/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/GramWindowMobius.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.GramWindowMobius
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramMobiusPool
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramMobiusLattice
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.GramShell

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_norm (I : SupportedIdeal) :
    ‖eisEmbedding (primaryGenerator I.val)‖^2=(Ideal.absNorm I.val:ℝ) := by
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1]

lemma shell_dilated_column (D I : SupportedIdeal) (N : ℝ) :
    (Ideal.absNorm (supportedIdealProduct D I).val:ℝ)/N=
      ‖eisEmbedding (primaryGenerator I.val)‖^2/(N/Ideal.absNorm D.val) := by
  rw [primary_norm,supported_dilation_norm,Nat.cast_mul]
  rw [div_div_eq_mul_div]
  ring

lemma shell_window_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (I J : SupportedIdeal)
    (h : I∉lowGaussColumns W hW N hN ∨ J∉lowGaussColumns W hW N hN) :
    shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [lowGaussColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [lowGaussColumns_mem,not_not] using h

theorem original_window_mobius_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : λ₀^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) :
    (∑I∈lowGaussColumns W hW N hN,∑J∈lowGaussColumns W hW N hN,
      if IsCoprime I.val J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
          shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N) else 0)=
      ∑D∈divisorPool (lowGaussColumns W hW N hN) Subtype.val,(moebius D:ℂ)*
        ∑'n : O,∑'m : O,
          jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator D*n) (primaryGenerator D*m)*
            shellProfile W v U T (‖eisEmbedding n‖^2/(N/Ideal.absNorm D))
              (‖eisEmbedding m‖^2/(N/Ideal.absNorm D)) := by
  let F := lowGaussColumns W hW N hN
  let f := fun I J : SupportedIdeal=>jointExtension S hS σ C k u a b r hr P hg c
    (primaryGenerator I.val) (primaryGenerator J.val)*
      shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)
  have hf : ∀I J,I∉F ∨ J∉F→f I J=0 := by
    intro I J h
    dsimp [f]
    rw [shell_window_support W hW N hN U v T I J h,mul_zero]
  change (∑I∈F,∑J∈F,if IsCoprime I.val J.val then f I J else 0)=_
  rw [finite_pair_mobius_dilation F F f hf]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  let D₀ := poolDivisor F D
  have hd : D₀.val=D := poolDivisor_val F D hD
  have hdp : λ₀^2∣primaryGenerator D₀.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ D₀.property)).2
  have he := jointExtension_ideal_lattice S hS hbad σ C k (primaryGenerator D₀.val)
    (primary_product C _ hC hdp) u a b r hr P hg c
    (fun n m=>shellProfile W v U T (‖eisEmbedding n‖^2/(N/Ideal.absNorm D₀.val))
      (‖eisEmbedding m‖^2/(N/Ideal.absNorm D₀.val)))
  dsimp only [f]
  simp only [supported_dilation_generator,shell_dilated_column]
  convert (preTransparency := .instances) he using 1
  rw [hd]

end SevenEighths.ProbeGramCommon
end

end RiemannHypothesis.Family003
