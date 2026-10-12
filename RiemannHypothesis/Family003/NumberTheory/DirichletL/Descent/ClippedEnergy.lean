/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/ClippedEnergy.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.ClippedEnergy
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.ClippedFourier
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
import RiemannHypothesis.Family003.Compat.FilterUpwardsSetMem
import RiemannHypothesis.Family003.Compat.ContDiffOrderSimp
import RiemannHypothesis.Family003.Compat.IntegrableOnRCLike

namespace RiemannHypothesis.Family003

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns InverseInitialOverlapFourier CompletedGauss
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem normalized_energy_vector
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(X Z F:ℝ):
    (∑v:labels×rows,‖(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a W X‖^2)=
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F:=by
  unfold normalizedColumnEnergy
  rw [Fintype.sum_prod_type,←Finset.sum_coe_sort labels]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←Finset.sum_coe_sort rows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_assoc,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hD f f.property)]

theorem canonical_clipped_energy
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(lo hi:ℝ)(hlo:0<lo)(hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ X Z F E:ℝ)(J:ℕ)(hc:0<c)(hX:0<X)(hE:0≤E)
    (hw:∀y,0<y→wFresh y*W (c*y)=W (c*y))
    (he:∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest wFresh s) X Z F≤E*(1+‖s‖)^(2*J)):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest W c θ) X Z F≤
      E*(1+‖θ‖)^(2*J)*(∫t:ℝ,(1+‖t‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) t‖)^2:=by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  let b:=density g (Real.log c)
  let phi:labels×rows→ℝ→ℂ:=fun v t=>(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
      (childLogTest wFresh (θ+t)) X
  have hint(v:labels×rows):Integrable (fun t:ℝ=>b t*phi v t):=by
    convert (preTransparency := .instances) (canonical_clipped_mode_integrable p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a g wFresh c θ X).const_mul ((Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)) using 1
    funext t
    dsimp [b,phi]
    ring
  have hbound(t:ℝ):(∑v:labels×rows,‖phi v t‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖t‖)^J)^2:=by
    dsimp only [phi]
    rw [normalized_energy_vector p hp hcop hg pool Ψ m slots lists a labels rows D hD]
    apply (he (θ+t)).trans
    have hb:1+‖θ+t‖≤(1+‖θ‖)*(1+‖t‖):=by
      have hh:=norm_add_le θ t
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg t)]
    calc
      _≤E*((1+‖θ‖)*(1+‖t‖))^(2*J):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden:Integrable (fun t:ℝ=>(1+‖t‖)^J*‖b t‖):=by
    simpa only [b,density_norm] using AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hh:=CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy b phi
    (fun t:ℝ=>(1+‖t‖)^J) (by intro t;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq(v:labels×rows): (∫t:ℝ,b t*phi v t)=
      (Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
        (clippedTest W c θ) X:=by
    rw [canonical_clipped_fourier p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a W lo hi hlo hs hW wFresh c θ X hc hX hw,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [b,phi,g]
    ring
  simp_rw [heq] at hh
  rw [normalized_energy_vector p hp hcop hg pool Ψ m slots lists a labels rows D hD] at hh
  simpa only [b,density_norm,g] using hh

end SevenEighths.InverseMoment

end

end RiemannHypothesis.Family003
