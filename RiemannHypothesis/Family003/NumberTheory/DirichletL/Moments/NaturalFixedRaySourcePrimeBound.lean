/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourcePrimeBound.lean
  Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePrimeBound
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePrimeGate
import RiemannHypothesis.Family003.Compat.NormNumIntToNat
import RiemannHypothesis.Family003.Compat.FilterUpwardsSetMem
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot HeckeZeroSupremum
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : Parameters.HighData Δ}

theorem source_physical_slot_bound (F : ProbeFinalAssembly.SourceData D)
    (loss lo hi κ : ℝ) (hloss : 0<loss) (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d : ℝ,d≤1 →
      ∀u : FreeRow,Z^(1/100:ℝ)≤rowNorm u → rowNorm u≤Z^(d-D.t) →
      ∀P t : ℝ,1≤P → P≤Z → ∀z : ℂ,lo≤1-z.re → 1-z.re≤hi →
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ‖normalizedSlot η₀ fixedBadMask 1 u.val (primePool F.modulus ⊤ 2 P)
        (physicalSlotCoefficient η₀ F.W P z) t P‖^2≤
        C*(1+|t|+|z.im|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    F.modulus ⊤ le_top F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    1 1 loss lo hi κ (by norm_num) (by norm_num) hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η
  filter_upwards [eventually_source_relativeBase_gate F η,eventually_ge_atTop Z₀,
    eventually_ge_atTop (1:ℝ)] with Z hgate hZ0 hZ
  intro label d hd u hlo hhi P t hP hPZ z hzlo hzhi
  let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
  obtain ⟨hc,hn⟩:=hgate label d u hlo hhi
  have hc' : ((relativeBase η₀ u).modulus.absNorm:ℝ)≤Z^(1:ℝ) :=
    hc.trans (Real.rpow_le_rpow_of_exponent_le hZ hd)
  have hb:=hbound Z P hZ0 hP (by simpa only [Real.rpow_one] using hPZ)
    (relativeBase η₀ u) hc' hn (1-z.re) (t-z.im) hzlo hzhi
  have hconj : (fun y=>conj (F.W y))=(F.W:ℝ→ℂ) := by
    funext y
    rw [F.complex_eq]
    simp
  dsimp only
  rw [physicalSlot_eq_relativeRay F.modulus ⊤ η₀ (naturalRow η₀ u.val u.property.1).character
    fixedBadMask 1 u.val (by simpa only [one_mul] using (naturalRow η₀ u.val u.property.1).element)
    F.W 2 P t z (zero_lt_one.trans_le hP),hconj,norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  have habs : |t-z.im|≤|t|+|z.im| := by simpa using (abs_sub_le t 0 z.im)
  exact pow_le_pow_left₀ (by positivity) (by linarith) degree

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end RiemannHypothesis.Family003
