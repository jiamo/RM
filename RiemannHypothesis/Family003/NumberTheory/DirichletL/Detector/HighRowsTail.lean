/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/HighRowsTail.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsTail
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
    - proof tweak: after convert, close residual instance-equality goals with 'with_reducible_and_instances rfl' (host instances are not reducibly defeq)
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Detector.HighRowsFamilies
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma gaussValuationTable_above (Q G : ℂ) (r n j : ℕ) (hj : n+1≤j) :
    gaussValuationTable Q G r n j=if 6∣r then Q^(n+1)-Q^n else 0 := by
  unfold gaussValuationTable
  by_cases hd : 6∣r
  · rw [ite_eq_left hd,ite_eq_left hd,ite_eq_left hj,ite_eq_left (by omega)]
  · rw [ite_eq_right hd,ite_eq_right hd,ite_eq_right (by omega)]

theorem positiveScalar_stable_large (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (n k j j' : ℕ)
    (hj : n+1<j) (hj' : n+1<j') :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j' := by
  simp only [positiveScalar_actual_table p hp hg hc,
    show 1≤j by omega,show 1≤j' by omega,and_true,
    gaussValuationTable_above _ _ _ n j (by omega),
    gaussValuationTable_above _ _ _ n j' (by omega),
    gaussValuationTable_above _ _ _ n (j-1) (by omega),
    gaussValuationTable_above _ _ _ n (j'-1) (by omega)]

end SevenEighths.ProbePrimePower
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc

theorem rowMarkedTerm_base_tail (eta a X W V rho : ℂ)
    (j e l k m : ℕ) (ht : 0<e+3*l) (ht6 : e+3*l≤6) :
    rowMarkedTerm p hp hg eta a X W V rho j e l k (m+2)=
      rowMarkedTerm p hp hg eta a X W V rho j e l k 2*V^m := by
  unfold rowMarkedTerm
  rw [ite_eq_right (by omega),ite_eq_right (by omega),
    SevenEighths.ProbePrimePower.positiveScalar_stable_large p hp hg hc (e+3*l-1) k (j+6*(m+2)) (j+6*2) (by omega) (by omega)]
  unfold rowWeightedScalar weightedScalar
  rw [pow_add V m 2]
  ring

theorem rowInner_base_rational (eta a X W V rho : ℂ) (hV : ‖V‖<1)
    (j e l : ℕ) (ht : 0<e+3*l) (ht6 : e+3*l≤6) :
    rowInner p hp hg eta a X W V rho j e l=
      ∑ k : Fin 2,
        (rowMarkedTerm p hp hg eta a X W V rho j e l k.val 0+
         rowMarkedTerm p hp hg eta a X W V rho j e l k.val 1+
         rowMarkedTerm p hp hg eta a X W V rho j e l k.val 2/(1-V)) := by
  have hsum (k : ℕ) : (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m)=
      rowMarkedTerm p hp hg eta a X W V rho j e l k 0+
      rowMarkedTerm p hp hg eta a X W V rho j e l k 1+
      rowMarkedTerm p hp hg eta a X W V rho j e l k 2/(1-V) := by
    have ht' : HasSum (fun m=>rowMarkedTerm p hp hg eta a X W V rho j e l k (m+2))
        (rowMarkedTerm p hp hg eta a X W V rho j e l k 2/(1-V)) := by
      have hgeo := (hasSum_geometric_of_norm_lt_one hV).mul_left (rowMarkedTerm p hp hg eta a X W V rho j e l k 2)
      rw [←div_eq_mul_inv] at hgeo
      convert (preTransparency := .instances) hgeo using 1
      all_goals try with_reducible_and_instances rfl
      funext m
      exact rowMarkedTerm_base_tail p hp hg hc eta a X W V rho j e l k m ht ht6
    have h := ht'.sum_range_add (f:=fun m=>rowMarkedTerm p hp hg eta a X W V rho j e l k m) (k:=2)
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] using h.tsum_eq
  rw [rowInner_two,hsum 0,hsum 1]
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]

end SevenEighths.ProbeEuler
end

end RiemannHypothesis.Family003
