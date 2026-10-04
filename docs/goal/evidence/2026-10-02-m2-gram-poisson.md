# 2026-10-02 — M2-GRAM-INERTIA: the `poisson` field of `GramFamily`, discharged for a concrete taper

Row: `M2-GRAM-INERTIA` (status stays `DONE_WEAK`; see "What is still open").
Module: `RiemannHypothesis/GramPoisson.lean` (imported by the root `RiemannHypothesis.lean`).

## The input that was discharged

`GramInertia.GramFamily` has one analytic field,

```
poisson : ∀ t, ∀ ρ ∈ (C t).onLine,
  ∑ k, ‖ReflectionConfig.evalVec (φ t) (τ t) ρ k‖ ^ 2 ≤ c t
```

i.e. `Σ_k |φ(γ_ρ − τ_k)|² ≤ c` at every on-line point. Before this round no `GramFamily` had ever
been constructed, so `GramFamily.two_thirds_eventually` was a statement about a structure with no
known inhabitant carrying a real taper. That is now fixed.

## Statements (namespace `RiemannHypothesis.GramInertia`)

* `taperHat ϱ L w := Zeta23.Taper.phiHat ϱ L w` — the Fourier transform (paper convention,
  `∫ φ(u) e^{izu} du`) of `φ(u) = ϱ((L/2 − |u|)/w)`, supported in `[−L/2, L/2]`.
* `gridNodes T L d k := T + k·(2π/L)`, `k < d`.
* `taperHat_conj` — `φ̂(z̄) = conj φ̂(z)` (the field `hφ`).
* `aConst_mul_sq_pos` — `0 < a L²` when `2w < L` (the field `c_pos`), via
  `1 − 2w/L ≤ b ≤ a`.
* `taperHat_poisson` — `Σ_{k<d} ‖φ̂(γ − τ_k)‖² ≤ a L²` for every real `γ`.
* `taperHat_poisson_onLine` — the same, in exactly the form of the `poisson` field.
* `params_poisson_onLine` — the same for the paper's own data `Zeta23.Params`
  (`P.phiHat T`, nodes `P.tau T k`, `d = P.d T`, constant `P.a T * P.L T ^ 2`)
  (with `TaperProfile P.ϱ`, `0 < w`, `2w ≤ L`); `taperHat_params`, `gridNodes_params` show these are literally the same objects.
* `stdTaper_poisson_onLine` — the fully concrete instance `ϱ = Real.smoothTransition`
  (`Zeta23.stdProfile`), `w = 1`, any `L ≥ 2`.
* `GramFamily.ofTaper`, `GramFamily.ofStdTaper` — constructors of `GramFamily` for an arbitrary
  family of reflection-symmetric configurations, with the `poisson` field filled by the theorem
  above (no analytic assumption); `ofStdTaper_data` records the taper/nodes/constant.
* `GramFamily.ofStdTaper_two_thirds_eventually` — `two_thirds_eventually` for `ofStdTaper`; its
  only hypotheses are `htr`, `hfr` (and `N_t > 0`, `E_i = o(N_t)`).

## Proof

On the critical line `γ_ρ = Im ρ` is real (`Zeta23.ZeroSide.gammaOf_of_re_eq_half`); `φ̂` is
real on `ℝ` (`Zeta23.Taper.phiHat_ofReal`), so `‖φ̂(γ − τ_k)‖² = φ̂_R(γ − τ_k)²`. The vendored
Poisson-summation theorem `Zeta23.Taper.hasSum_phiHatR_sq` gives
`HasSum (k ↦ φ̂_R(γ − T − 2πk/L)²) (a L²)` over `k ∈ ℤ`; the finite sum over `k < d` is the
sum over the image of the embedding `Fin d ↪ ℤ`, and all terms are `≥ 0`, so
`sum_le_hasSum` gives the bound.

## Checks

* `lake build RiemannHypothesis.GramPoisson`: success, no warnings from the module.
* `#print axioms` for every theorem listed above: `[propext, Classical.choice, Quot.sound]`.
* No `sorry` in the module.

## Adversarial revalidation

* *Is the field vacuous?* No: the bound is for every on-line point of an **arbitrary**
  `ReflectionConfig`, and the constant `a L²` is the exact value of the infinite Poisson sum
  (`tsum_phiHatR_sq`), not an inflated constant. `c` is not chosen to make the field trivial:
  it is the normalisation `c = a L²` that defines `Â = (aL²)⁻¹ A`, the same as the vendored
  `Params.hat`.
* *Is the taper the one used by the `2/3`?* Yes for the paper's data: `params_poisson_onLine`
  is stated with `P.phiHat T`, `P.tau T`, `P.d T`, `P.a T`, and `taperHat_params` /
  `gridNodes_params` are `rfl`.
* *Was a hypothesis smuggled in?* The only side conditions are `TaperProfile ϱ`, `0 < w`,
  `2w ≤ L` (and `2w < L` for `c > 0`) — conditions on the taper parameters, not on `ζ`.

## What is still open (open boundary of M2-GRAM-INERTIA)

1. `htr`: `tr Â_t ≥ N_t − o(N_t)` for the Gram matrix of the zeros of `ζ` in the window.
2. `hfr`: `‖Â_t‖_F² ≤ (4/3) N_t + o(N_t)` (general `λ`: `(1/λ + λ/3) N_t`).

Both are prime-side (explicit-formula) estimates. The vendored library proves them for its
own matrix `Az`; transporting them requires D3 — a `ReflectionConfig` built from the zeros of
`ζ` in the window, with its `gram` identified with the vendored `Az` — which has not been done.
