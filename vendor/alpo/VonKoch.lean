import Formalism.PeriodIntegrals.ExplicitFormulaCounts.ExplicitFormula
import RiemannHypothesis.ChebyshevCriterion

/-!
# von Koch's theorem: the Riemann hypothesis implies `ψ(x) − x = O(x^{1/2+ε})`

von Koch (1901) proved that the Riemann hypothesis gives `ψ(x) − x = O(x^{1/2} log² x)`.  This
file proves it for `ζ`, in this repository's form `ChebyshevBoundForm`:
`ZetaForm → ChebyshevBoundForm`.  With `RiemannHypothesis.zeta_of_chebyshevBound` (the converse,
proved in the library) this gives `ChebyshevBoundForm ↔ ZetaForm`.

## The route

The alpo.ge tree proves two unconditional theorems for every primitive Dirichlet character, from
Mathlib alone (87 modules):

* `explicitFormula_closed : PI.ExplicitFormula`: the truncated explicit formula, for
  `2 ≤ T ≤ u`,
  `‖ψ₀(u) + ∑_{|γ|<T} m_ρ u^ρ/ρ‖ ≤ C (u log²(NuT)/T + log(Nu) + ∑_{|γ|<1} m_ρ/‖ρ‖)`;
* `zerosWindow_closed : PI.ZerosWindow`: at most `C log(N(|t|+2))` zeroes, with multiplicity, in
  the window `|γ − t| ≤ 1` of the critical strip.

For the character mod 1, `L(s, χ₁) = ζ(s)` and `ψ₀(n) = ψ(n) − n` (`psi0_natCast`).  Under RH
every zero below height `T` has `re ρ = 1/2`, so `‖u^ρ‖ = u^{1/2}` and `‖ρ‖ ≥ max(1/2, |γ|)`.
Sorting the zeroes by `⌊|γ|⌋₊ = j` and counting each fibre with two windows gives
`∑_{|γ|<T} m_ρ/‖ρ‖ ≤ 4C log(⌈T⌉₊+2)(1 + log⌈T⌉₊)` (`sum_mult_div_norm_le`; the harmonic sum
is Mathlib's `harmonic_le_one_add_log`).  Taking `T = u = n` (`abs_chebyshevPsi_sub_le`):
`|ψ(n) − n| ≤ √n · 4C log(n+2)(1+log n) + C'(4 log² n + log n + K₁) = O(√n log² n)`.

## Hypothesis hygiene (`AGENTS.md`), for the hypothesis `ZetaForm`

1. *Direction.*  `ChebyshevBoundForm → ZetaForm` is proved in the library
   (`zeta_of_chebyshevBound`); this file is the converse.
2. *Strength.*  Exactly RH: the two together are an equivalence.
3. *Non-triviality.*  `ZetaForm` has an external machine-checked proof (the alpo.ge tree, row
   `M3-ALPO-VERIFICATION`); this file does not use it.
4. *Attribution.*  H. von Koch, *Sur la distribution des nombres premiers*, Acta Math. 24
   (1901), 159–182.

Not a theorem of this repository: it lives in `vendor/alpo` (the tree has no licence) and is
compiled only by `vendor/alpo/tools/analytic.sh`.  The `#print axioms` lines must show only
`propext`, `Classical.choice`, `Quot.sound`.  Task-board row `M2-VON-KOCH`.
-/

open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace AlpoVonKoch

/-- The trivial character modulo `1`; its `L`-function is `ζ`. -/
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-- The multiplicity of a zero of `L(s, χ₁) = ζ(s)`, as the tree counts it. -/
local notation "𝔪" => analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))

theorem one_apply_modOne (n : ℕ) : χ₁ (n : ZMod 1) = 1 := by
  rw [Subsingleton.elim (n : ZMod 1) 1, map_one]

/-- The tree's `ψ₀` for the character mod 1, at an integer, is `ψ(n) − n`. -/
theorem psi0_natCast (n : ℕ) :
    PI.psi0 χ₁ (n : ℝ) = ((RiemannHypothesis.chebyshevPsi n : ℝ) : ℂ) - (n : ℂ) := by
  rw [PI.psi0, if_pos rfl, Nat.floor_natCast, RiemannHypothesis.chebyshevPsi, Complex.ofReal_sum,
    Complex.ofReal_natCast]
  simp only [one_apply_modOne, mul_one]

/-- Under RH, every zero the tree counts below a height lies on the critical line. -/
theorem re_eq_half (h : RiemannHypothesis.ZetaForm) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ PI.ZerosBelow χ₁ T) : ρ.re = 1 / 2 := by
  simp only [PI.ZerosBelow, Set.mem_setOf_eq] at hρ
  obtain ⟨h0, h1, -, hz⟩ := hρ
  rw [DirichletCharacter.LFunction_modOne_eq] at hz
  exact RiemannHypothesis.zeta_iff_zeta_strip.mp h ρ h0 h1 hz

/-- The tree's window count for `ζ`, as a finite sum. -/
theorem sum_mult_window_le {Cw : ℝ} (hW : PI.ZerosWindowWith Cw) (t : ℝ)
    (hfin : (PI.ZerosNear χ₁ t).Finite) :
    ∑ ρ ∈ hfin.toFinset, (𝔪 ρ : ℝ) ≤ Cw * Real.log (|t| + 2) := by
  have h2 := (hW 1 χ₁ DirichletCharacter.isPrimitive_one_level_one t).2
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_one, one_mul] at h2
  exact h2

/-- **The sum over the zeroes, under RH**:
`∑_{|γ| < T} m_ρ/‖ρ‖ ≤ 4 C log(⌈T⌉₊ + 2) (1 + log ⌈T⌉₊)`. -/
theorem sum_mult_div_norm_le (h : RiemannHypothesis.ZetaForm) {Cw : ℝ} (hCw : 0 < Cw)
    (hW : PI.ZerosWindowWith Cw) {T : ℝ} (hfin : (PI.ZerosBelow χ₁ T).Finite) :
    ∑ ρ ∈ hfin.toFinset, (𝔪 ρ : ℝ) / ‖ρ‖ ≤
      4 * Cw * Real.log ((⌈T⌉₊ : ℝ) + 2) * (1 + Real.log (⌈T⌉₊ : ℝ)) := by
  classical
  -- every zero below `T` has `⌊|γ|⌋₊ < ⌈T⌉₊`
  have hmaps : ∀ ρ ∈ hfin.toFinset, ⌊|ρ.im|⌋₊ ∈ Finset.range ⌈T⌉₊ := by
    intro ρ hρ
    have hρ' := hfin.mem_toFinset.mp hρ
    simp only [PI.ZerosBelow, Set.mem_setOf_eq] at hρ'
    rw [Finset.mem_range, Nat.floor_lt (abs_nonneg _)]
    exact lt_of_lt_of_le hρ'.2.2.1 (Nat.le_ceil T)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hM0 : (0 : ℝ) ≤ (⌈T⌉₊ : ℝ) := Nat.cast_nonneg _
  -- one fibre `⌊|γ|⌋₊ = j`
  have hfib : ∀ j ∈ Finset.range ⌈T⌉₊,
      ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im|⌋₊ = j), (𝔪 ρ : ℝ) / ‖ρ‖ ≤
        4 * Cw * Real.log ((⌈T⌉₊ : ℝ) + 2) * (1 / ((j : ℝ) + 1)) := by
    intro j hj
    have hjM : (j : ℝ) < (⌈T⌉₊ : ℝ) := by exact_mod_cast Finset.mem_range.mp hj
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hfA : (PI.ZerosNear χ₁ (j : ℝ)).Finite :=
      (hW 1 χ₁ DirichletCharacter.isPrimitive_one_level_one _).1
    have hfB : (PI.ZerosNear χ₁ (-(j : ℝ))).Finite :=
      (hW 1 χ₁ DirichletCharacter.isPrimitive_one_level_one _).1
    -- each zero of the fibre has norm at least `(j + 1)/2`
    have hterm : ∀ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im|⌋₊ = j),
        (𝔪 ρ : ℝ) / ‖ρ‖ ≤ (𝔪 ρ : ℝ) * (2 / ((j : ℝ) + 1)) := by
      intro ρ hρ
      obtain ⟨hρs, hρj⟩ := Finset.mem_filter.mp hρ
      have hre := re_eq_half h (hfin.mem_toFinset.mp hρs)
      have hlo : (j : ℝ) ≤ |ρ.im| := by rw [← hρj]; exact Nat.floor_le (abs_nonneg _)
      have h1 : (1 : ℝ) / 2 ≤ ‖ρ‖ := by linarith [Complex.re_le_norm ρ]
      have h2 : (j : ℝ) ≤ ‖ρ‖ := hlo.trans (Complex.abs_im_le_norm ρ)
      have hnorm : ((j : ℝ) + 1) / 2 ≤ ‖ρ‖ := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · have : (j : ℝ) = 0 := by exact_mod_cast h0
          linarith
        · have : (1 : ℝ) ≤ j := by exact_mod_cast h0
          linarith
      have hpos : (0 : ℝ) < ((j : ℝ) + 1) / 2 := by positivity
      calc (𝔪 ρ : ℝ) / ‖ρ‖ ≤ (𝔪 ρ : ℝ) / (((j : ℝ) + 1) / 2) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos hnorm
        _ = (𝔪 ρ : ℝ) * (2 / ((j : ℝ) + 1)) := by rw [div_div_eq_mul_div, mul_div_assoc]
    -- the fibre lies in the two windows centred at `j` and `-j`
    have hsub : hfin.toFinset.filter (fun ρ => ⌊|ρ.im|⌋₊ = j) ⊆ hfA.toFinset ∪ hfB.toFinset := by
      intro ρ hρ
      obtain ⟨hρs, hρj⟩ := Finset.mem_filter.mp hρ
      have hρ' := hfin.mem_toFinset.mp hρs
      simp only [PI.ZerosBelow, Set.mem_setOf_eq] at hρ'
      obtain ⟨h0, h1, -, hz⟩ := hρ'
      have hlo : (j : ℝ) ≤ |ρ.im| := by rw [← hρj]; exact Nat.floor_le (abs_nonneg _)
      have hhi : |ρ.im| < (j : ℝ) + 1 := by rw [← hρj]; exact Nat.lt_floor_add_one _
      rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      simp only [PI.ZerosNear, Set.mem_setOf_eq]
      rcases le_or_gt 0 ρ.im with hp | hn
      · left
        rw [abs_of_nonneg hp] at hlo hhi
        exact ⟨h0, h1, abs_le.mpr ⟨by linarith, by linarith⟩, hz⟩
      · right
        rw [abs_of_neg hn] at hlo hhi
        exact ⟨h0, h1, abs_le.mpr ⟨by linarith, by linarith⟩, hz⟩
    -- the fibre carries at most `2 C log(⌈T⌉₊ + 2)` zeroes with multiplicity
    have hFm : ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im|⌋₊ = j), (𝔪 ρ : ℝ) ≤
        2 * (Cw * Real.log ((⌈T⌉₊ : ℝ) + 2)) := by
      have hAB : ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im|⌋₊ = j), (𝔪 ρ : ℝ) ≤
          ∑ ρ ∈ hfA.toFinset ∪ hfB.toFinset, (𝔪 ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      have hUI := Finset.sum_union_inter (s₁ := hfA.toFinset) (s₂ := hfB.toFinset)
        (f := fun ρ => (𝔪 ρ : ℝ))
      have hI : 0 ≤ ∑ ρ ∈ hfA.toFinset ∩ hfB.toFinset, (𝔪 ρ : ℝ) :=
        Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      have hA' : ∑ ρ ∈ hfA.toFinset, (𝔪 ρ : ℝ) ≤ Cw * Real.log ((j : ℝ) + 2) := by
        have := sum_mult_window_le hW (j : ℝ) hfA
        rwa [Nat.abs_cast] at this
      have hB' : ∑ ρ ∈ hfB.toFinset, (𝔪 ρ : ℝ) ≤ Cw * Real.log ((j : ℝ) + 2) := by
        have := sum_mult_window_le hW (-(j : ℝ)) hfB
        rwa [abs_neg, Nat.abs_cast] at this
      have hlog : Real.log ((j : ℝ) + 2) ≤ Real.log ((⌈T⌉₊ : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hCl : Cw * Real.log ((j : ℝ) + 2) ≤ Cw * Real.log ((⌈T⌉₊ : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hlog hCw.le
      linarith
    calc ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im|⌋₊ = j), (𝔪 ρ : ℝ) / ‖ρ‖
        ≤ ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im|⌋₊ = j),
            (𝔪 ρ : ℝ) * (2 / ((j : ℝ) + 1)) := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im|⌋₊ = j), (𝔪 ρ : ℝ)) *
            (2 / ((j : ℝ) + 1)) := by rw [Finset.sum_mul]
      _ ≤ (2 * (Cw * Real.log ((⌈T⌉₊ : ℝ) + 2))) * (2 / ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hFm (by positivity)
      _ = 4 * Cw * Real.log ((⌈T⌉₊ : ℝ) + 2) * (1 / ((j : ℝ) + 1)) := by ring
  have hlogM : 0 ≤ Real.log ((⌈T⌉₊ : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 4 * Cw * Real.log ((⌈T⌉₊ : ℝ) + 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hCw.le) hlogM
  have hH : ∑ j ∈ Finset.range ⌈T⌉₊, 1 / ((j : ℝ) + 1) = (harmonic ⌈T⌉₊ : ℝ) := by
    simp [harmonic, one_div]
  calc ∑ j ∈ Finset.range ⌈T⌉₊,
        ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im|⌋₊ = j), (𝔪 ρ : ℝ) / ‖ρ‖
      ≤ ∑ j ∈ Finset.range ⌈T⌉₊, 4 * Cw * Real.log ((⌈T⌉₊ : ℝ) + 2) * (1 / ((j : ℝ) + 1)) :=
        Finset.sum_le_sum hfib
    _ = 4 * Cw * Real.log ((⌈T⌉₊ : ℝ) + 2) * ∑ j ∈ Finset.range ⌈T⌉₊, 1 / ((j : ℝ) + 1) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * Cw * Real.log ((⌈T⌉₊ : ℝ) + 2) * (1 + Real.log (⌈T⌉₊ : ℝ)) := by
        rw [hH]
        exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) hcoef

/-- **The explicit formula at an integer, under RH**: for `n ≥ 2`, with `T = n`,
`|ψ(n) − n| ≤ √n · 4 C_w log(n+2)(1 + log n) + C (n log²(n²)/n + log n + K₁)`. -/
theorem abs_chebyshevPsi_sub_le (h : RiemannHypothesis.ZetaForm) {C : ℝ}
    (hC : PI.ExplicitFormulaWith C) {Cw : ℝ} (hCw : 0 < Cw) (hW : PI.ZerosWindowWith Cw)
    {n : ℕ} (hn : 2 ≤ n) :
    |RiemannHypothesis.chebyshevPsi n - n| ≤
      (n : ℝ) ^ (1 / 2 : ℝ) * (4 * Cw * Real.log ((n : ℝ) + 2) * (1 + Real.log (n : ℝ))) +
        C * ((n : ℝ) * Real.log (1 * (n : ℝ) * n) ^ 2 / n + Real.log (1 * (n : ℝ)) +
          ∑ᶠ ρ ∈ PI.ZerosBelow χ₁ 1, (𝔪 ρ : ℝ) / ‖ρ‖) := by
  have hu2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hu0 : (0 : ℝ) < n := by linarith
  obtain ⟨hfin, hbound⟩ :=
    hC 1 χ₁ DirichletCharacter.isPrimitive_one_level_one (n : ℝ) (n : ℝ) hu2 le_rfl
  rw [psi0_natCast, Nat.cast_one, finsum_mem_eq_finite_toFinset_sum _ hfin] at hbound
  set S : ℂ := ∑ ρ ∈ hfin.toFinset, ((𝔪 ρ : ℕ) : ℂ) * (((n : ℝ) : ℂ) ^ ρ / ρ) with hSdef
  -- the sum over the zeroes, under RH
  have hS : ‖S‖ ≤ (n : ℝ) ^ (1 / 2 : ℝ) * ∑ ρ ∈ hfin.toFinset, (𝔪 ρ : ℝ) / ‖ρ‖ := by
    rw [hSdef, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun ρ hρ => ?_))
    have hre := re_eq_half h (hfin.mem_toFinset.mp hρ)
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre]
    ring
  have hB := sum_mult_div_norm_le h hCw hW hfin
  rw [Nat.ceil_natCast] at hB
  have hψ : ‖((RiemannHypothesis.chebyshevPsi n : ℝ) : ℂ) - (n : ℂ)‖ =
      |RiemannHypothesis.chebyshevPsi n - n| := by
    rw [show ((RiemannHypothesis.chebyshevPsi n : ℝ) : ℂ) - (n : ℂ) =
        ((RiemannHypothesis.chebyshevPsi n - n : ℝ) : ℂ) by
          rw [Complex.ofReal_sub, Complex.ofReal_natCast],
      Complex.norm_real, Real.norm_eq_abs]
  have htri : ‖((RiemannHypothesis.chebyshevPsi n : ℝ) : ℂ) - (n : ℂ)‖ ≤
      ‖((RiemannHypothesis.chebyshevPsi n : ℝ) : ℂ) - (n : ℂ) + S‖ + ‖S‖ := by
    calc ‖((RiemannHypothesis.chebyshevPsi n : ℝ) : ℂ) - (n : ℂ)‖
        = ‖(((RiemannHypothesis.chebyshevPsi n : ℝ) : ℂ) - (n : ℂ) + S) - S‖ := by
          congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  rw [hψ] at htri
  have hQ : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc |RiemannHypothesis.chebyshevPsi n - n|
      ≤ ‖((RiemannHypothesis.chebyshevPsi n : ℝ) : ℂ) - (n : ℂ) + S‖ + ‖S‖ := htri
    _ ≤ C * ((n : ℝ) * Real.log (1 * (n : ℝ) * n) ^ 2 / n + Real.log (1 * (n : ℝ)) +
          ∑ᶠ ρ ∈ PI.ZerosBelow χ₁ 1, (𝔪 ρ : ℝ) / ‖ρ‖) +
        (n : ℝ) ^ (1 / 2 : ℝ) * (4 * Cw * Real.log ((n : ℝ) + 2) * (1 + Real.log (n : ℝ))) :=
        add_le_add hbound (hS.trans (mul_le_mul_of_nonneg_left hB hQ))
    _ = _ := by ring

/-- **von Koch's theorem.**  The Riemann hypothesis implies
`ψ(N) − N = O(N^{1/2+ε})` for every `ε > 0`: this repository's `ChebyshevBoundForm`. -/
theorem chebyshevBoundForm_of_zetaForm (h : RiemannHypothesis.ZetaForm) :
    RiemannHypothesis.ChebyshevBoundForm := by
  obtain ⟨C, hC0, hC⟩ := explicitFormula_closed
  obtain ⟨Cw, hCw0, hW⟩ := zerosWindow_closed
  obtain ⟨K₁, hK₁def⟩ :
      ∃ K : ℝ, (∑ᶠ ρ ∈ PI.ZerosBelow χ₁ 1, (𝔪 ρ : ℝ) / ‖ρ‖) = K := ⟨_, rfl⟩
  have hK₁ : 0 ≤ K₁ := by
    rw [← hK₁def]
    exact finsum_nonneg fun ρ => finsum_nonneg fun _ =>
      div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hD : 0 ≤ 4 * Cw + C * (5 + K₁) := by
    have := mul_nonneg hC0.le (by linarith : (0 : ℝ) ≤ 5 + K₁)
    linarith
  intro ε hε
  refine ⟨max 1 ((4 * Cw + C * (5 + K₁)) * (1 + 2 / ε) ^ 2), fun n => ?_⟩
  have hexp : (0 : ℝ) < 1 / 2 + ε := by linarith
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
  · have h0 : RiemannHypothesis.chebyshevPsi 0 = 0 := by
      rw [RiemannHypothesis.chebyshevPsi, Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0),
        Finset.sum_empty]
    simp only [h0, Nat.cast_zero, Real.zero_rpow hexp.ne', sub_zero, abs_zero, mul_zero, le_refl]
  · have h1 : RiemannHypothesis.chebyshevPsi 1 = 0 := by
      rw [RiemannHypothesis.chebyshevPsi, Finset.Icc_self, Finset.sum_singleton,
        ArithmeticFunction.vonMangoldt_apply_one]
    simp only [h1, Nat.cast_one, Real.one_rpow, mul_one, zero_sub, abs_neg, abs_one]
    exact le_max_left _ _
  · have hbase := abs_chebyshevPsi_sub_le h hC hCw0 hW hn
    rw [hK₁def] at hbase
    have hu2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    generalize (n : ℝ) = u at hbase hu2 ⊢
    have hu0 : (0 : ℝ) < u := by linarith
    have hu1 : (1 : ℝ) ≤ u := by linarith
    have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu1
    -- `log(u + 2) ≤ 1 + log u`
    have hlog2 : Real.log (u + 2) ≤ 1 + Real.log u := by
      have hl2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
      calc Real.log (u + 2) ≤ Real.log (2 * u) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + Real.log u := Real.log_mul (by norm_num) hu0.ne'
        _ ≤ 1 + Real.log u := by linarith
    -- the error term of the explicit formula
    have hE1 : u * Real.log (1 * u * u) ^ 2 / u = 4 * Real.log u ^ 2 := by
      rw [one_mul, Real.log_mul hu0.ne' hu0.ne', mul_div_cancel_left₀ _ hu0.ne']
      ring
    have hE : u * Real.log (1 * u * u) ^ 2 / u + Real.log (1 * u) + K₁ ≤
        (5 + K₁) * (1 + Real.log u) ^ 2 := by
      rw [hE1, one_mul]
      nlinarith [mul_nonneg hK₁ hlogu, mul_nonneg hK₁ (sq_nonneg (Real.log u)),
        sq_nonneg (Real.log u)]
    -- the sum over the zeroes
    have hB : 4 * Cw * Real.log (u + 2) * (1 + Real.log u) ≤ 4 * Cw * (1 + Real.log u) ^ 2 := by
      have h4 : 4 * Cw * Real.log (u + 2) ≤ 4 * Cw * (1 + Real.log u) :=
        mul_le_mul_of_nonneg_left hlog2 (by linarith)
      calc 4 * Cw * Real.log (u + 2) * (1 + Real.log u)
          ≤ 4 * Cw * (1 + Real.log u) * (1 + Real.log u) :=
            mul_le_mul_of_nonneg_right h4 (by linarith)
        _ = 4 * Cw * (1 + Real.log u) ^ 2 := by ring
    have hQ1 : 1 ≤ u ^ (1 / 2 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
    have hQ0 : 0 ≤ u ^ (1 / 2 : ℝ) := by linarith
    have hEnn : 0 ≤ C * ((5 + K₁) * (1 + Real.log u) ^ 2) :=
      mul_nonneg hC0.le (mul_nonneg (by linarith) (sq_nonneg _))
    have hstep : |RiemannHypothesis.chebyshevPsi n - u| ≤
        u ^ (1 / 2 : ℝ) * ((4 * Cw + C * (5 + K₁)) * (1 + Real.log u) ^ 2) := by
      have e1 := mul_le_mul_of_nonneg_left hB hQ0
      have e2 := mul_le_mul_of_nonneg_left hE hC0.le
      have e3 : C * ((5 + K₁) * (1 + Real.log u) ^ 2) ≤
          u ^ (1 / 2 : ℝ) * (C * ((5 + K₁) * (1 + Real.log u) ^ 2)) :=
        le_mul_of_one_le_left hEnn hQ1
      calc |RiemannHypothesis.chebyshevPsi n - u|
          ≤ u ^ (1 / 2 : ℝ) * (4 * Cw * Real.log (u + 2) * (1 + Real.log u)) +
              C * (u * Real.log (1 * u * u) ^ 2 / u + Real.log (1 * u) + K₁) := hbase
        _ ≤ u ^ (1 / 2 : ℝ) * (4 * Cw * (1 + Real.log u) ^ 2) +
              C * ((5 + K₁) * (1 + Real.log u) ^ 2) := add_le_add e1 e2
        _ ≤ u ^ (1 / 2 : ℝ) * (4 * Cw * (1 + Real.log u) ^ 2) +
              u ^ (1 / 2 : ℝ) * (C * ((5 + K₁) * (1 + Real.log u) ^ 2)) := by linarith
        _ = u ^ (1 / 2 : ℝ) * ((4 * Cw + C * (5 + K₁)) * (1 + Real.log u) ^ 2) := by ring
    -- `1 + log u ≤ (1 + 2/ε) u^{ε/2}`
    have hP1 : 1 ≤ u ^ (ε / 2) := Real.one_le_rpow hu1 (by linarith)
    have hlogP : Real.log u ≤ 2 / ε * u ^ (ε / 2) := by
      calc Real.log u ≤ u ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div hu0.le (by linarith)
        _ = 2 / ε * u ^ (ε / 2) := by rw [div_div_eq_mul_div]; ring
    have hLP : 1 + Real.log u ≤ (1 + 2 / ε) * u ^ (ε / 2) := by nlinarith
    have hsq : (1 + Real.log u) ^ 2 ≤ ((1 + 2 / ε) * u ^ (ε / 2)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hLP 2
    have hrp : u ^ (1 / 2 : ℝ) * (u ^ (ε / 2) * u ^ (ε / 2)) = u ^ (1 / 2 + ε) := by
      rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]
      congr 1
      ring
    calc |RiemannHypothesis.chebyshevPsi n - u|
        ≤ u ^ (1 / 2 : ℝ) * ((4 * Cw + C * (5 + K₁)) * (1 + Real.log u) ^ 2) := hstep
      _ ≤ u ^ (1 / 2 : ℝ) * ((4 * Cw + C * (5 + K₁)) * ((1 + 2 / ε) * u ^ (ε / 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hD) hQ0
      _ = (4 * Cw + C * (5 + K₁)) * (1 + 2 / ε) ^ 2 *
            (u ^ (1 / 2 : ℝ) * (u ^ (ε / 2) * u ^ (ε / 2))) := by ring
      _ = (4 * Cw + C * (5 + K₁)) * (1 + 2 / ε) ^ 2 * u ^ (1 / 2 + ε) := by rw [hrp]
      _ ≤ max 1 ((4 * Cw + C * (5 + K₁)) * (1 + 2 / ε) ^ 2) * u ^ (1 / 2 + ε) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hu0.le _)

/-- **`ChebyshevBoundForm ↔ ZetaForm`**: von Koch's theorem with its converse, which is proved
in the library. -/
theorem chebyshevBoundForm_iff_zetaForm :
    RiemannHypothesis.ChebyshevBoundForm ↔ RiemannHypothesis.ZetaForm :=
  ⟨RiemannHypothesis.zeta_of_chebyshevBound, chebyshevBoundForm_of_zetaForm⟩

end AlpoVonKoch

end

#print axioms explicitFormula_closed
#print axioms zerosWindow_closed
#print axioms AlpoVonKoch.sum_mult_div_norm_le
#print axioms AlpoVonKoch.abs_chebyshevPsi_sub_le
#print axioms AlpoVonKoch.chebyshevBoundForm_of_zetaForm
#print axioms AlpoVonKoch.chebyshevBoundForm_iff_zetaForm
