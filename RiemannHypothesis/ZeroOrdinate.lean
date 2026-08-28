/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.RvMCumulative

/-!
# The ordinate of the `n`-th zero: `γ_n ~ 2π n / log n`

`RiemannHypothesis.RvMCumulative` gives the Riemann–von Mangoldt asymptotic for the counting
function, `N(0, T) ~ (T/2π) log T`.  Inverting it gives the classical asymptotic for the ordinates
of the zeroes themselves.

The `n`-th ordinate is defined from the counting function: `γ_n` is the least height at which
`N(0, ·)` reaches `n`.  Since `N(0, ·)` counts **with multiplicity** the zeroes of `ζ` in the
critical strip with ordinate in `(0, T]`, this is the `n`-th positive ordinate listed in
increasing order and repeated according to multiplicity.

## Main results

* `nthZeroOrdinate` — the ordinate of the `n`-th zero.
* `windowCount_lt_of_lt_nthZeroOrdinate`, `le_windowCount_of_nthZeroOrdinate_lt` — the two
  defining properties: `N(0, T) < n` below `γ_n`, and `n ≤ N(0, T)` above it.
* `le_windowCount_nthZeroOrdinate` — the infimum is attained, `n ≤ N(0, γ_n)`.
* `exists_mem_nontrivialZeroSet_im_eq_nthZeroOrdinate` — for `n ≥ 1`, `γ_n` really is the
  ordinate of a zero of `ζ` in the critical strip.
* `tendsto_nthZeroOrdinate_atTop` — `γ_n → ∞`.
* `tendsto_nthZeroOrdinate_mul_log_div_nat` — `γ_n log γ_n ~ 2π n`.
* `tendsto_nthZeroOrdinate_mul_log_nat_div` — **the classical form** `γ_n ~ 2π n / log n`.

Nothing here bears on the real parts of the zeroes, and nothing on the Riemann hypothesis.
-/

noncomputable section

open Filter

open scoped Topology

namespace RiemannHypothesis

/-- The heights at which the counting function `N(0, ·)` has reached `n`. -/
def nthOrdinateSet (n : ℕ) : Set ℝ := {T : ℝ | 0 ≤ T ∧ n ≤ windowCount 0 T}

/-- **The ordinate of the `n`-th zero of `ζ`**: the least height `T` at which the counting
function `N(0, T)` — the number of zeroes of `ζ` in the critical strip with ordinate in `(0, T]`,
counted with multiplicity — reaches `n`. -/
def nthZeroOrdinate (n : ℕ) : ℝ := sInf (nthOrdinateSet n)

lemma monotone_windowCount_zero : Monotone fun T : ℝ => windowCount 0 T :=
  fun _ _ h => windowCount_mono (le_refl 0) h

lemma tendsto_windowCount_zero_atTop :
    Tendsto (fun T : ℝ => (windowCount 0 T : ℝ)) atTop atTop := by
  obtain ⟨c, hc, T₀, hcount⟩ := exists_mul_le_windowCount_zero
  have hmain : Tendsto (fun T : ℝ => c * (T * Real.log T)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc
      (Filter.Tendsto.atTop_mul_atTop₀ Filter.tendsto_id Real.tendsto_log_atTop)
  refine tendsto_atTop_mono' _ ?_ hmain
  filter_upwards [eventually_ge_atTop T₀] with T hT using hcount T hT

lemma nthOrdinateSet_nonempty (n : ℕ) : (nthOrdinateSet n).Nonempty := by
  obtain ⟨T, hT⟩ := (tendsto_windowCount_zero_atTop.eventually_ge_atTop (n : ℝ)).and
    (eventually_ge_atTop (0 : ℝ)) |>.exists
  exact ⟨T, hT.2, by exact_mod_cast hT.1⟩

lemma nthOrdinateSet_bddBelow (n : ℕ) : BddBelow (nthOrdinateSet n) :=
  ⟨0, fun _ hT => hT.1⟩

lemma nthZeroOrdinate_nonneg (n : ℕ) : 0 ≤ nthZeroOrdinate n :=
  le_csInf (nthOrdinateSet_nonempty n) fun _ hT => hT.1

/-- Above `γ_n` the counting function has reached `n`. -/
lemma le_windowCount_of_nthZeroOrdinate_lt {n : ℕ} {T : ℝ} (h : nthZeroOrdinate n < T) :
    n ≤ windowCount 0 T := by
  obtain ⟨x, hx, hxT⟩ := exists_lt_of_csInf_lt (nthOrdinateSet_nonempty n) h
  exact le_trans hx.2 (monotone_windowCount_zero hxT.le)

/-- Below `γ_n` the counting function has not yet reached `n`. -/
lemma windowCount_lt_of_lt_nthZeroOrdinate {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (h : T < nthZeroOrdinate n) : windowCount 0 T < n := by
  by_contra hcon
  exact absurd (csInf_le (nthOrdinateSet_bddBelow n) ⟨hT, not_lt.mp hcon⟩) (not_le.mpr h)

/-- If the counting function has not reached `n` by the height `M`, then `γ_n ≥ M`. -/
lemma le_nthZeroOrdinate_of_windowCount_lt {n : ℕ} {M : ℝ} (h : windowCount 0 M < n) :
    M ≤ nthZeroOrdinate n :=
  le_csInf (nthOrdinateSet_nonempty n) fun T hT => by
    by_contra hcon
    exact absurd (le_trans hT.2 (monotone_windowCount_zero (not_le.mp hcon).le)) (not_le.mpr h)

/-- The infimum is attained: the counting function has already reached `n` at `γ_n`.  (`N(0, ·)`
is right-continuous, since the window `(0, T]` is closed at `T`.) -/
lemma le_windowCount_nthZeroOrdinate (n : ℕ) : n ≤ windowCount 0 (nthZeroOrdinate n) := by
  set γ : ℝ := nthZeroOrdinate n with hγdef
  by_contra hcon
  rw [not_le] at hcon
  have hγ0 : 0 ≤ γ := nthZeroOrdinate_nonneg n
  -- pick a height `T > γ` with no zero of ordinate in `(γ, T]`
  obtain ⟨T, hγT, hempty⟩ : ∃ T : ℝ, γ < T ∧ windowZeros γ T = ∅ := by
    rcases Set.eq_empty_or_nonempty (windowZeros γ (γ + 1)) with h | h
    · exact ⟨γ + 1, by linarith, h⟩
    · obtain ⟨ρ, hρ, hmin⟩ :=
        Set.exists_min_image _ Complex.im (windowZeros_finite γ (γ + 1)) h
      refine ⟨(γ + ρ.im) / 2, by linarith [hρ.2.1], ?_⟩
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hz, hz1, hz2⟩
      have hz3 : z.im ≤ γ + 1 := by linarith [hρ.2.2]
      have := hmin z ⟨hz, hz1, hz3⟩
      linarith
  have hcount : windowCount 0 T = windowCount 0 γ := by
    have := windowCount_add (a := 0) (b := γ) (c := T) hγ0 hγT.le
    rw [show windowCount γ T = 0 by rw [windowCount, hempty, finsum_mem_empty]] at this
    omega
  have := le_windowCount_of_nthZeroOrdinate_lt (n := n) (T := T) (by rw [← hγdef]; exact hγT)
  omega

/-- For `n ≥ 1` the height `γ_n` is the ordinate of an actual zero of `ζ` in the critical
strip. -/
lemma exists_mem_nontrivialZeroSet_im_eq_nthZeroOrdinate {n : ℕ} (hn : 0 < n) :
    ∃ ρ ∈ nontrivialZeroSet, ρ.im = nthZeroOrdinate n := by
  set γ : ℝ := nthZeroOrdinate n with hγdef
  have hne : (windowZeros 0 γ).Nonempty := by
    rcases Set.eq_empty_or_nonempty (windowZeros 0 γ) with h | h
    · exfalso
      have h0 : windowCount 0 γ = 0 := by rw [windowCount, h, finsum_mem_empty]
      have h1 : n ≤ windowCount 0 γ := by rw [hγdef]; exact le_windowCount_nthZeroOrdinate n
      omega
    · exact h
  obtain ⟨ρ, hρ, hmax⟩ := Set.exists_max_image _ Complex.im (windowZeros_finite 0 γ) hne
  refine ⟨ρ, hρ.1, le_antisymm hρ.2.2 ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hset : windowZeros 0 γ = windowZeros 0 ρ.im := by
    apply Set.Subset.antisymm
    · exact fun z hz => ⟨hz.1, hz.2.1, hmax z hz⟩
    · exact fun z hz => ⟨hz.1, hz.2.1, le_trans hz.2.2 hρ.2.2⟩
  have hcount : windowCount 0 γ = windowCount 0 ρ.im := by
    rw [windowCount, windowCount, hset]
  have hlt := windowCount_lt_of_lt_nthZeroOrdinate (n := n) (T := ρ.im) (le_of_lt hρ.2.1) hcon
  have hge : n ≤ windowCount 0 γ := by rw [hγdef]; exact le_windowCount_nthZeroOrdinate n
  omega

lemma tendsto_nthZeroOrdinate_atTop : Tendsto (fun n : ℕ => nthZeroOrdinate n) atTop atTop := by
  refine tendsto_atTop.mpr fun M => ?_
  filter_upwards [eventually_ge_atTop (windowCount 0 M + 1)] with n hn
  exact le_nthZeroOrdinate_of_windowCount_lt (lt_of_lt_of_le (Nat.lt_succ_self _) hn)

/-- The two-sided squeeze on `n` in terms of `γ_n log γ_n`: for every `ε > 0`, eventually
`(1/2π − ε) γ_n log γ_n ≤ n ≤ (1/2π + ε) γ_n log γ_n`. -/
lemma eventually_nthZeroOrdinate_squeeze {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / (2 * Real.pi) - ε) * (nthZeroOrdinate n * Real.log (nthZeroOrdinate n))
          ≤ (n : ℝ) ∧
        (n : ℝ)
          ≤ (1 / (2 * Real.pi) + ε) * (nthZeroOrdinate n * Real.log (nthZeroOrdinate n)) := by
  -- the counting asymptotic, in the form of a two-sided bound above a height `T₀ ≥ 2`
  have hlim := tendsto_windowCount_zero_div
  have hev : ∀ᶠ T : ℝ in atTop,
      |(windowCount 0 T : ℝ) / (T * Real.log T) - 1 / (2 * Real.pi)| ≤ ε :=
    (Metric.tendsto_nhds.mp hlim ε hε).mono fun T hT => le_of_lt (by
      simpa [Real.dist_eq] using hT)
  obtain ⟨T₀, hT₀⟩ := (hev.and (eventually_ge_atTop (2 : ℝ))).exists_forall_of_atTop
  have hbounds : ∀ T : ℝ, T₀ ≤ T →
      (1 / (2 * Real.pi) - ε) * (T * Real.log T) ≤ (windowCount 0 T : ℝ) ∧
        (windowCount 0 T : ℝ) ≤ (1 / (2 * Real.pi) + ε) * (T * Real.log T) := by
    intro T hT
    obtain ⟨habs, hT2⟩ := hT₀ T hT
    have hT0 : (0 : ℝ) < T := by linarith
    have hlog : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
    have hpos : (0 : ℝ) < T * Real.log T := by positivity
    rw [abs_le] at habs
    obtain ⟨h1, h2⟩ := habs
    exact ⟨(le_div_iff₀ hpos).mp (by linarith), (div_le_iff₀ hpos).mp (by linarith)⟩
  have hT₀2 : (2 : ℝ) ≤ T₀ := (hT₀ T₀ le_rfl).2
  filter_upwards [tendsto_nthZeroOrdinate_atTop.eventually_ge_atTop (T₀ + 1)] with n hn
  set γ : ℝ := nthZeroOrdinate n with hγ
  have hγT₀ : T₀ + 1 ≤ γ := hn
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hcont : ContinuousAt (fun T : ℝ => T * Real.log T) γ :=
    continuousAt_id.mul (Real.continuousAt_log (ne_of_gt hγ0))
  constructor
  · -- lower bound: let `T ↑ γ`
    have htend : Tendsto (fun T : ℝ => (1 / (2 * Real.pi) - ε) * (T * Real.log T)) (𝓝[<] γ)
        (𝓝 ((1 / (2 * Real.pi) - ε) * (γ * Real.log γ))) :=
      ((hcont.const_smul (1 / (2 * Real.pi) - ε)).tendsto.mono_left nhdsWithin_le_nhds).congr
        (by intro T; simp [smul_eq_mul])
    refine le_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT (show T₀ < γ by linarith)] with T hT
    obtain ⟨hTa, hTγ⟩ := hT
    have hTT₀ : T₀ ≤ T := hTa.le
    have h1 := (hbounds T hTT₀).1
    have h2 : windowCount 0 T < n :=
      windowCount_lt_of_lt_nthZeroOrdinate (by linarith) hTγ
    have : ((windowCount 0 T : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2.le
    linarith
  · -- upper bound: let `T ↓ γ`
    have htend : Tendsto (fun T : ℝ => (1 / (2 * Real.pi) + ε) * (T * Real.log T)) (𝓝[>] γ)
        (𝓝 ((1 / (2 * Real.pi) + ε) * (γ * Real.log γ))) :=
      ((hcont.const_smul (1 / (2 * Real.pi) + ε)).tendsto.mono_left nhdsWithin_le_nhds).congr
        (by intro T; simp [smul_eq_mul])
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with T hT
    have hTγ : γ < T := hT
    have hTT₀ : T₀ ≤ T := by linarith
    have h2 := (hbounds T hTT₀).2
    have h1 : n ≤ windowCount 0 T := le_windowCount_of_nthZeroOrdinate_lt hTγ
    have : (n : ℝ) ≤ ((windowCount 0 T : ℕ) : ℝ) := by exact_mod_cast h1
    linarith

/-- `n / (γ_n log γ_n) → 1/2π`. -/
theorem tendsto_nat_div_nthZeroOrdinate_mul_log :
    Tendsto (fun n : ℕ => (n : ℝ) / (nthZeroOrdinate n * Real.log (nthZeroOrdinate n))) atTop
      (𝓝 (1 / (2 * Real.pi))) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := ((eventually_nthZeroOrdinate_squeeze (half_pos hε)).and
    (tendsto_nthZeroOrdinate_atTop.eventually_ge_atTop (3 : ℝ))).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨⟨h1, h2⟩, hγ3⟩ := hN n hn
  set γ : ℝ := nthZeroOrdinate n with hγ
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hlog : (0 : ℝ) < Real.log γ := Real.log_pos (by linarith)
  have hpos : (0 : ℝ) < γ * Real.log γ := by positivity
  rw [Real.dist_eq, abs_lt]
  constructor
  · have := (le_div_iff₀ hpos).mpr h1
    linarith [(div_le_iff₀ hpos).mpr h2, (le_div_iff₀ hpos).mpr h1]
  · linarith [(div_le_iff₀ hpos).mpr h2]

/-- **`γ_n log γ_n ~ 2π n`.** -/
theorem tendsto_nthZeroOrdinate_mul_log_div_nat :
    Tendsto (fun n : ℕ => nthZeroOrdinate n * Real.log (nthZeroOrdinate n) / n) atTop
      (𝓝 (2 * Real.pi)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h := tendsto_nat_div_nthZeroOrdinate_mul_log.inv₀ (by positivity)
  have hinv : (1 / (2 * Real.pi))⁻¹ = 2 * Real.pi := by
    field_simp
  rw [hinv] at h
  refine h.congr' ?_
  filter_upwards [tendsto_nthZeroOrdinate_atTop.eventually_ge_atTop (3 : ℝ),
    eventually_gt_atTop 0] with n hγ3 hn
  have hγ0 : (0 : ℝ) < nthZeroOrdinate n := by linarith
  have hlog : (0 : ℝ) < Real.log (nthZeroOrdinate n) := Real.log_pos (by linarith)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  field_simp

/-- `log n / log γ_n → 1`: taking logarithms in `γ_n log γ_n ~ 2π n` shows that `log γ_n` and
`log n` are asymptotically equal. -/
lemma tendsto_log_nat_div_log_nthZeroOrdinate :
    Tendsto (fun n : ℕ => Real.log n / Real.log (nthZeroOrdinate n)) atTop (𝓝 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hL : Tendsto (fun n : ℕ => Real.log (nthZeroOrdinate n)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_nthZeroOrdinate_atTop
  have hlogb : Tendsto
      (fun n : ℕ => Real.log (nthZeroOrdinate n * Real.log (nthZeroOrdinate n) / n)) atTop
      (𝓝 (Real.log (2 * Real.pi))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp tendsto_nthZeroOrdinate_mul_log_div_nat
  have hloglog : Tendsto
      (fun n : ℕ => Real.log (Real.log (nthZeroOrdinate n)) / Real.log (nthZeroOrdinate n)) atTop
      (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa [Function.comp] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    exact h0.comp hL
  have hdiv : Tendsto (fun n : ℕ =>
      Real.log (nthZeroOrdinate n * Real.log (nthZeroOrdinate n) / n)
        / Real.log (nthZeroOrdinate n)) atTop (𝓝 0) := hlogb.div_atTop hL
  have hsum : Tendsto (fun n : ℕ => 1
      + Real.log (Real.log (nthZeroOrdinate n)) / Real.log (nthZeroOrdinate n)
      - Real.log (nthZeroOrdinate n * Real.log (nthZeroOrdinate n) / n)
          / Real.log (nthZeroOrdinate n)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hloglog).sub hdiv
  refine hsum.congr' ?_
  filter_upwards [tendsto_nthZeroOrdinate_atTop.eventually_ge_atTop (3 : ℝ),
    eventually_gt_atTop 0] with n hγ3 hn
  have hγ0 : (0 : ℝ) < nthZeroOrdinate n := by linarith
  have hL0 : (0 : ℝ) < Real.log (nthZeroOrdinate n) := Real.log_pos (by linarith)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogeq : Real.log (nthZeroOrdinate n * Real.log (nthZeroOrdinate n) / n)
      = Real.log (nthZeroOrdinate n) + Real.log (Real.log (nthZeroOrdinate n)) - Real.log n := by
    rw [Real.log_div (by positivity) (ne_of_gt hn0),
      Real.log_mul (ne_of_gt hγ0) (ne_of_gt hL0)]
  rw [hlogeq]
  field_simp
  ring

/-- `log γ_n / log n → 1`. -/
lemma tendsto_log_nthZeroOrdinate_div_log_nat :
    Tendsto (fun n : ℕ => Real.log (nthZeroOrdinate n) / Real.log n) atTop (𝓝 1) := by
  have h := tendsto_log_nat_div_log_nthZeroOrdinate.inv₀ one_ne_zero
  rw [inv_one] at h
  exact h.congr fun n => by rw [inv_div]

/-- **The classical asymptotic for the ordinates of the zeroes: `γ_n ~ 2π n / log n`.**  The
ordinate of the `n`-th nontrivial zero of `ζ` in the upper half plane, counted with multiplicity,
satisfies `γ_n log n / n → 2π`. -/
theorem tendsto_nthZeroOrdinate_mul_log_nat_div :
    Tendsto (fun n : ℕ => nthZeroOrdinate n * Real.log n / n) atTop (𝓝 (2 * Real.pi)) := by
  have h := tendsto_nthZeroOrdinate_mul_log_div_nat.mul tendsto_log_nat_div_log_nthZeroOrdinate
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [tendsto_nthZeroOrdinate_atTop.eventually_ge_atTop (3 : ℝ),
    eventually_gt_atTop 0] with n hγ3 hn
  have hγ0 : (0 : ℝ) < nthZeroOrdinate n := by linarith
  have hL0 : (0 : ℝ) < Real.log (nthZeroOrdinate n) := Real.log_pos (by linarith)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  field_simp

end RiemannHypothesis
