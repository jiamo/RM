/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Zeta23.Poisson
import Zeta23.Taper.Norms
import Zeta23.Defs.Profile
import RiemannHypothesis.GramInertia

/-!
# The `poisson` field of `GramFamily`, discharged for a concrete taper

`GramInertia.GramFamily` carries, besides the configurations, tapers and nodes, one analytic
field: the diagonal ("Poisson") bound

  `∀ ρ on the critical line,  Σ_k ‖φ(γ_ρ − τ_k)‖² ≤ c`.

This module proves that field for the taper of the vendored `Zeta23` library, so that a
`GramFamily` can be built with **no** analytic hypothesis left in it.

* The taper is `taperHat ϱ L w = φ̂`, the paper-convention Fourier transform of the compactly
  supported even bump `φ(u) = ϱ((L/2 − |u|)/w)` (`Zeta23.Taper.phiHat`), for any taper profile
  `ϱ` (in particular the concrete one, `Zeta23.stdProfile = Real.smoothTransition`).
* The nodes are the grid `gridNodes T L d k = T + k·(2π/L)`, `k = 0, …, d − 1`.
* The constant is `c = a L²` with `a = L⁻¹ ∫ φ²`, which is positive as soon as `2w < L`.

The proof: on the critical line `γ_ρ` is real, `φ̂` is real on `ℝ`, and the vendored Poisson
summation theorem (`Zeta23.Taper.hasSum_phiHatR_sq`) gives `Σ_{k∈ℤ} φ̂(γ − τ_k)² = a L²`
exactly; the finite sum over `k < d` is a sub-sum of non-negative terms.

Main results:
* `GramInertia.taperHat_poisson` — the bound for an arbitrary real `γ`;
* `GramInertia.taperHat_poisson_onLine` — the bound in exactly the form of the `poisson` field;
* `GramInertia.GramFamily.ofTaper` — a `GramFamily` built from any family of configurations
  with this taper, its `poisson` field proved;
* `GramInertia.stdTaper_poisson_onLine`, `GramInertia.GramFamily.ofStdTaper` — the same for the
  fully concrete choice `ϱ = Real.smoothTransition`, `w = 1`, any `L > 2`.
-/

noncomputable section

open Finset Real RHLinalg

namespace RiemannHypothesis

namespace GramInertia

/-- The concrete taper: `φ̂(z) = ∫ φ(u) e^{izu} du` with `φ(u) = ϱ((L/2 − |u|)/w)`. -/
def taperHat (ϱ : ℝ → ℝ) (L w : ℝ) : ℂ → ℂ := Zeta23.Taper.phiHat ϱ L w

/-- The grid of sampling nodes `τ_k = T + k·(2π/L)`, `k = 0, …, d − 1`. -/
def gridNodes (T L : ℝ) (d : ℕ) : Fin d → ℝ :=
  fun k => T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / L)

/-- The taper satisfies the reality condition `φ̂(z̄) = conj φ̂(z)` required by `GramFamily`. -/
theorem taperHat_conj (ϱ : ℝ → ℝ) (L w : ℝ) (z : ℂ) :
    taperHat ϱ L w (starRingEnd ℂ z) = starRingEnd ℂ (taperHat ϱ L w z) :=
  Zeta23.Taper.phiHat_conj z

/-- The normalisation `c = a L²` is positive when `2w < L`. -/
theorem aConst_mul_sq_pos {ϱ : ℝ → ℝ} (hϱ : Zeta23.TaperProfile ϱ) {L w : ℝ} (hw : 0 < w)
    (hwL : 2 * w < L) : 0 < Zeta23.Taper.aConst ϱ L w * L ^ 2 := by
  have hL : 0 < L := by linarith
  have hb := Zeta23.Taper.one_sub_le_bConst hϱ hw hwL.le
  have hba := Zeta23.Taper.bConst_le_aConst hϱ hw hwL.le
  have h1 : 0 < 1 - 2 * w / L := by
    rw [sub_pos, div_lt_one hL]; exact hwL
  have : 0 < Zeta23.Taper.aConst ϱ L w := by linarith
  positivity

/-- **The Poisson diagonal bound for the concrete taper, at an arbitrary real ordinate.**
`Σ_{k<d} ‖φ̂(γ − τ_k)‖² ≤ a L²`. -/
theorem taperHat_poisson {ϱ : ℝ → ℝ} (hϱ : Zeta23.TaperProfile ϱ) {L w : ℝ} (hw : 0 < w)
    (hwL : 2 * w ≤ L) (T : ℝ) (d : ℕ) (γ : ℝ) :
    ∑ k : Fin d, ‖taperHat ϱ L w ((γ : ℂ) - (gridNodes T L d k : ℂ))‖ ^ 2
      ≤ Zeta23.Taper.aConst ϱ L w * L ^ 2 := by
  have hv : ∀ k : Fin d, ‖taperHat ϱ L w ((γ : ℂ) - (gridNodes T L d k : ℂ))‖ ^ 2
      = Zeta23.Taper.phiHatR ϱ L w (γ - (T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / L))) ^ 2 := by
    intro k
    rw [taperHat, gridNodes, ← Complex.ofReal_sub, Zeta23.Taper.phiHat_ofReal, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  simp_rw [hv]
  let e : Fin d ↪ ℤ := ⟨fun k => ((k : ℕ) : ℤ), fun a b h => Fin.ext (by
    have h' : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := h
    exact_mod_cast h')⟩
  have h := sum_le_hasSum (Finset.univ.map e) (fun i _ => sq_nonneg _)
    (Zeta23.Taper.hasSum_phiHatR_sq hϱ hw hwL T γ)
  rwa [sum_map] at h

/-- **The `poisson` field, in exactly the form `GramFamily` requires**: for every point `ρ` of a
reflection-symmetric configuration lying on the critical line,
`Σ_k ‖φ̂(γ_ρ − τ_k)‖² ≤ a L²`. -/
theorem taperHat_poisson_onLine {ϱ : ℝ → ℝ} (hϱ : Zeta23.TaperProfile ϱ) {L w : ℝ} (hw : 0 < w)
    (hwL : 2 * w ≤ L) (T : ℝ) (d : ℕ) (C : ReflectionConfig) :
    ∀ ρ ∈ C.onLine, ∑ k, ‖ReflectionConfig.evalVec (taperHat ϱ L w) (gridNodes T L d) ρ k‖ ^ 2
      ≤ Zeta23.Taper.aConst ϱ L w * L ^ 2 := by
  intro ρ hρ
  have hre : ρ.re = 1 / 2 := (Finset.mem_filter.mp hρ).2
  simp only [ReflectionConfig.evalVec]
  rw [Zeta23.ZeroSide.gammaOf_of_re_eq_half hre]
  exact taperHat_poisson hϱ hw hwL T d ρ.im

namespace GramFamily

/-- **A `GramFamily` with the concrete taper.**  Any family of reflection-symmetric configurations
`C t`, with the taper `φ̂` of profile `ϱ`, length `L t`, ramp width `w t` (`0 < w t`,
`2 w t < L t`), grid nodes `τ_k = T t + k·2π/L t` (`k < d t`) and normalisation `c t = a L²`.
The `poisson` field is the theorem `taperHat_poisson_onLine`; nothing is assumed. -/
def ofTaper {ι : Type*} (C : ι → ReflectionConfig) (d : ι → ℕ) {ϱ : ℝ → ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (L w T : ι → ℝ) (hw : ∀ t, 0 < w t)
    (hwL : ∀ t, 2 * w t < L t) : GramFamily ι where
  C := C
  d := d
  φ t := taperHat ϱ (L t) (w t)
  hφ t z := taperHat_conj ϱ (L t) (w t) z
  τ t := gridNodes (T t) (L t) (d t)
  c t := Zeta23.Taper.aConst ϱ (L t) (w t) * L t ^ 2
  c_pos t := aConst_mul_sq_pos hϱ (hw t) (hwL t)
  poisson t := taperHat_poisson_onLine hϱ (hw t) (hwL t).le (T t) (d t) (C t)

end GramFamily

/-! ### The paper's data (`Zeta23.Params`): same taper, same grid, same constant -/

/-- The taper of the paper's parameters is `taperHat`. -/
theorem taperHat_params (P : Zeta23.Params) (T : ℝ) :
    taperHat P.ϱ (P.L T) P.w = P.phiHat T := rfl

/-- The paper's grid `τ_k = P.tau T k` is `gridNodes`. -/
theorem gridNodes_params (P : Zeta23.Params) (T : ℝ) (k : Fin (P.d T)) :
    gridNodes T (P.L T) (P.d T) k = P.tau T ((k : ℕ) : ℤ) := rfl

/-- **The `poisson` field for the paper's taper and grid** (`d = ⌊LT/2π⌋` nodes
`τ_k = T + 2πk/L`, constant `a L²`), whenever the profile is a taper profile, `0 < w` and
`2w ≤ L` (weaker than the paper's standing assumptions `P.Valid`, `8w ≤ L`). -/
theorem params_poisson_onLine {P : Zeta23.Params} (hϱ : Zeta23.TaperProfile P.ϱ) (hw : 0 < P.w)
    {T : ℝ} (hwL : 2 * P.w ≤ P.L T) (C : ReflectionConfig) :
    ∀ ρ ∈ C.onLine,
      ∑ k, ‖ReflectionConfig.evalVec (P.phiHat T) (fun k : Fin (P.d T) => P.tau T ((k : ℕ) : ℤ))
        ρ k‖ ^ 2 ≤ P.a T * P.L T ^ 2 :=
  taperHat_poisson_onLine hϱ hw hwL T (P.d T) C

/-! ### The fully concrete choice `ϱ = Real.smoothTransition`, `w = 1` -/

/-- **The `poisson` field for the fully concrete taper** `ϱ = Real.smoothTransition`, `w = 1`,
any `L ≥ 2`: for every on-line point `ρ` of any reflection-symmetric configuration,
`Σ_{k<d} ‖φ̂(γ_ρ − T − k·2π/L)‖² ≤ a L²`. -/
theorem stdTaper_poisson_onLine {L : ℝ} (hL : 2 ≤ L) (T : ℝ) (d : ℕ) (C : ReflectionConfig) :
    ∀ ρ ∈ C.onLine,
      ∑ k, ‖ReflectionConfig.evalVec (taperHat Zeta23.stdProfile L 1) (gridNodes T L d) ρ k‖ ^ 2
        ≤ Zeta23.Taper.aConst Zeta23.stdProfile L 1 * L ^ 2 :=
  taperHat_poisson_onLine Zeta23.taperProfile_stdProfile one_pos (by linarith) T d C

namespace GramFamily

/-- **A `GramFamily` with the fully concrete taper** `ϱ = Real.smoothTransition`, `w = 1`, for
lengths `L t > 2`; the `poisson` field is `stdTaper_poisson_onLine`. -/
def ofStdTaper {ι : Type*} (C : ι → ReflectionConfig) (d : ι → ℕ) (L T : ι → ℝ)
    (hL : ∀ t, 2 < L t) : GramFamily ι :=
  ofTaper C d Zeta23.taperProfile_stdProfile L (fun _ => 1) T (fun _ => one_pos)
    (fun t => by linarith [hL t])

/-- The taper, nodes and normalisation of `ofStdTaper` are the concrete ones. -/
theorem ofStdTaper_data {ι : Type*} (C : ι → ReflectionConfig) (d : ι → ℕ) (L T : ι → ℝ)
    (hL : ∀ t, 2 < L t) (t : ι) :
    (ofStdTaper C d L T hL).φ t = taperHat Zeta23.stdProfile (L t) 1 ∧
    (ofStdTaper C d L T hL).τ t = gridNodes (T t) (L t) (d t) ∧
    (ofStdTaper C d L T hL).c t = Zeta23.Taper.aConst Zeta23.stdProfile (L t) 1 * L t ^ 2 :=
  ⟨rfl, rfl, rfl⟩

/-- **`2/3` for the concrete taper, with the Poisson input discharged.**  For the family
`ofStdTaper`, the only remaining inputs are the two prime-side estimates on `tr Â_t` and
`‖Â_t‖_F²` (and `N_t > 0`); the diagonal bound is no longer a hypothesis. -/
theorem ofStdTaper_two_thirds_eventually {ι : Type*} (C : ι → ReflectionConfig) (d : ι → ℕ)
    (L T : ι → ℝ) (hL : ∀ t, 2 < L t) {l : Filter ι} {E₁ E₂ : ι → ℝ}
    (htr : ∀ᶠ t in l, (C t).count - E₁ t ≤ rtrace ((ofStdTaper C d L T hL).gramHat t))
    (hfr : ∀ᶠ t in l, frobSq ((ofStdTaper C d L T hL).gramHat t) ≤ 4 / 3 * (C t).count + E₂ t)
    (hNpos : ∀ᶠ t in l, 0 < (C t).count)
    (hE₁ : Filter.Tendsto (fun t => E₁ t / (C t).count) l (nhds 0))
    (hE₂ : Filter.Tendsto (fun t => E₂ t / (C t).count) l (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, (2 / 3 - ε) * (C t).count ≤ (C t).onLine.card :=
  (ofStdTaper C d L T hL).two_thirds_eventually htr hfr hNpos hE₁ hE₂ hε

end GramFamily

end GramInertia

end RiemannHypothesis
