/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/PrimeRows/ZGrowth.lean
  Original module: OAI.NumberTheory.DirichletL.PrimeRows.ZGrowth
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrimeRows.FirstWGrowth
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Hecke.StripActual
import RiemannHypothesis.Family003.Compat.Backports
import RiemannHypothesis.Family003.Compat.NormNumIntToNat

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalRow_first_z_bounded (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) :
    ∃C : ℝ,0≤C ∧ ∀z : ℂ,(17/50:ℝ)≤z.re →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤C := by
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm x.re
  let L : ℝ := HeckeReciprocalBound.bound 2*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  have hLb : 0≤HeckeReciprocalBound.bound 2 := by unfold HeckeReciprocalBound.bound; positivity
  have hL : 0≤L := by dsimp [L];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro z hz
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤HeckeReciprocalBound.bound 2 :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z hx hw hz hxw
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x.re x w z hx le_rfl
      hw hz (by linarith [hfirst.positive])
  unfold physicalCompensatedRow continuedCompensatedRow
  simp only [norm_mul]
  rw [mul_assoc L]
  apply mul_le_mul _ (mul_le_mul hh' hg (norm_nonneg _) (by dsimp [N];positivity))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hL
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl (norm_nonneg _)) (norm_nonneg _)

end SevenEighths.ProbeHighRowFamily

end

end RiemannHypothesis.Family003
