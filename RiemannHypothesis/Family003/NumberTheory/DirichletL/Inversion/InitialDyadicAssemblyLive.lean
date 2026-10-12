/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Inversion/InitialDyadicAssemblyLive.lean
  Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyLive
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyBounds
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def cappedSource (S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>∀i,sourceNorms p x i∈Set.Icc (a i) (b i))

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_cap_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (cappedSource p S a b))
      (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,cappedSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    simp only [Function.comp_apply,erase_sourcePoint]
    by_contra hn
    exact hb (hcap x hx N hN M hM ρ hn)

theorem physicalBlock_live_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_window_partition p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ

theorem physicalBlock_live_norm
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (E:ℝ)(he:∀k:Windows a b,‖windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)‖≤E) :
    ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m‖≤(Fintype.card (Windows a b):ℝ)*E := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_norm_le_windows p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ E he

end SevenEighths.InverseInitialDyadicAssembly

end

end RiemannHypothesis.Family003
