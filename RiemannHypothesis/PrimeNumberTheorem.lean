/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.PrimeCounting
import Zeta23.FromPNTPlus.MediumPNT

/-!
# The prime number theorem

`RiemannHypothesis.PrimeCounting` reduced the prime number theorem to the single analytic
input `ψ(x)/x → 1`.  That input is now available: the vendored `Zeta23` library contains
(ported, with attribution, from the *PrimeNumberTheoremAnd* project) the prime number theorem
with a de la Vallée Poussin–type error term,

`ψ(x) − x = O(x · exp(−c (log x)^{1/10}))`.

This file records it in this repository's vocabulary and completes the reduction:

* `chebyshev_psi_sub_id_isBigO` — the error-term form;
* `chebyshev_psi_sub_id_isLittleO` — `ψ(x) − x = o(x)`;
* `chebyshev_psi_div_tendsto_one` — `ψ(x)/x → 1`;
* `chebyshev_theta_div_tendsto_one` — `θ(x)/x → 1`;
* `prime_number_theorem` — `π(x) / (x / log x) → 1`.
-/

noncomputable section

open Filter Topology Asymptotics

namespace RiemannHypothesis

/-- **The prime number theorem with error term**: there is `c > 0` with
`ψ(x) − x = O(x · exp(−c (log x)^{1/10}))` as `x → ∞`. -/
theorem chebyshev_psi_sub_id_isBigO :
    ∃ c > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  exact ⟨c, hc, hO⟩

/-- `exp(−c (log x)^{1/10}) → 0` for `c > 0`. -/
private lemma tendsto_exp_neg_log_rpow {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have h2 : Tendsto (fun x : ℝ => -c * Real.log x ^ ((1 : ℝ) / 10)) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -c < 0) h1
  exact Real.tendsto_exp_atBot.comp h2

/-- **`ψ(x) − x = o(x)`**. -/
theorem chebyshev_psi_sub_id_isLittleO :
    (fun x : ℝ => Chebyshev.psi x - x) =o[atTop] fun x : ℝ => x := by
  obtain ⟨c, hc, hO⟩ := chebyshev_psi_sub_id_isBigO
  refine hO.trans_isLittleO ?_
  have h := ((isLittleO_one_iff ℝ).mpr (tendsto_exp_neg_log_rpow hc)).mul_isBigO
    (isBigO_refl (fun x : ℝ => x) atTop)
  refine (h.congr' ?_ ?_).congr' (.of_forall fun x => rfl) (.of_forall fun x => rfl)
  · exact .of_forall fun x => mul_comm _ _
  · exact .of_forall fun x => one_mul _

/-- **`ψ(x)/x → 1`**. -/
theorem chebyshev_psi_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  have h := chebyshev_psi_sub_id_isLittleO.tendsto_div_nhds_zero
  have h' : Tendsto (fun x : ℝ => Chebyshev.psi x / x - 1) atTop (𝓝 0) := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  simpa using h'.add (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ)))

/-- **`θ(x)/x → 1`** for the first Chebyshev function. -/
theorem chebyshev_theta_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  chebyshev_theta_tendsto_of_psi chebyshev_psi_div_tendsto_one

/-- **The prime number theorem**: `π(x) / (x / log x) → 1`. -/
theorem prime_number_theorem :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) :=
  primeCounting_tendsto_of_chebyshev_psi chebyshev_psi_div_tendsto_one

end RiemannHypothesis

end
