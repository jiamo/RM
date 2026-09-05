/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The ceiling of the whole corpus

`RiemannHypothesis.MethodCeiling` turns the boundary of *one* counting route into a theorem: from
a distinctness budget `N_d ≥ c·N` and an off-line budget `N_off ≤ b·N` the best derivable
proportion on the critical line is exactly `c − b`.  This file does the same for **all** of the
repository's unconditional facts about the distribution of the zeroes at once.

The question it answers is the one that the task board's `M3-GAP` row cannot: *stack every
unconditional statement this repository has proved — the mollifier proportion, the sharp
Riemann–von Mangoldt count, the Carlson power-saving density theorem, the quadruple symmetry of
the off-line zeroes, the `O(log γ)` multiplicity bound, the classical zero-free region — and ask
what the best resulting bound on the off-line count is.*  The answer, proved below, is that it is
exactly the bound the mollifier already gives, and in particular that it is **not** the Riemann
hypothesis: there is a counting configuration satisfying every one of those facts in which a
positive proportion of the zeroes lies off the critical line.

## The constraint system

`ZeroCorpus θ` collects the counting data that the routes of this repository manipulate — the
cumulative counts over the ordinate window `(0, T]` of

* all nontrivial zeroes with multiplicity (`total`, the repository's `windowCount 0 T`),
* the distinct nontrivial zeroes (`distinct`, `windowCountDistinct 0 T`),
* the distinct zeroes on the critical line (`onLine`, `windowCountOnLine 0 T`),
* the distinct zeroes off the critical line (`off`, `windowCountOffLine 0 T`), and
* the distinct zeroes at distance at least `δ` from the critical line
  (`offAt δ`, `(zerosOffCriticalLine δ T).ncard`) —

together with one field for each unconditional fact the repository proves about them.  Each field
names the theorem it abstracts:

| field | repository theorem |
| --- | --- |
| `window_onLine` | `sixty_seven_percent_on_critical_line` (`θ = 0.33`) |
| `rvm` | `exists_abs_windowCount_zero_sub_main_le` |
| `density` | `exists_ncard_zerosOffCriticalLine_le_rpow` |
| `off_even`, `offAt_even` | `ncard_upperOffLineNontrivialZeros_eq_two_mul` |
| `mult` | `zeroMultiplicity_le_log_abs_im`, `multCount_le` |
| `zeroFree` | the classical zero-free region, `RiemannHypothesis.ZeroFreeClassical` |
| the shape fields | `windowCount_mono`, `windowCountOffLine_add_windowCountOnLine` |
| `off_attained` | `finite_nontrivialZeros`: finitely many zeroes below a height |

The Riemann hypothesis, in this vocabulary, is `RHCounts Z : ∀ T, Z.off T = 0`.

## The results

* `windowOff_le` — soundness: in a corpus the off-line count of a dyadic window is eventually at
  most `θ` times the total count of the window.  This is the direction the repository's routes
  use.
* `modelCorpus` — for every rate `r < θ` an explicit corpus in which the off-line count of a
  window is eventually at least `r` times the total count of the window, all of whose off-line
  zeroes at distance `≥ δ` from the critical line number at most `2/δ` **uniformly in `T`**.
* `corpus_window_ceiling` — the exact ceiling: a proportion `p` on the critical line is derivable
  from the corpus if and only if `p ≤ 1 − θ`.  With the repository's `θ = 0.33` that is the
  `67 %` it already proves; nothing in the corpus beyond the mollifier moves it.
* `rh_not_derivable_from_corpus`, `offLine_positive_proportion_consistent` — the corpus does not
  imply the Riemann hypothesis, and does not even imply that the off-line zeroes are a zero
  proportion of all zeroes.
* `density_not_sufficient` — the sharper statement about the density route: the model can be
  chosen so that `offAt δ` is *bounded in `T`* for every fixed `δ > 0`, which is stronger than
  any density theorem of the shape `N(σ, T) ≪ T^(1−c)` — stronger, indeed, than the density
  hypothesis and than Lindelöf-strength density bounds — and it still has infinitely many
  off-line zeroes.  The obstruction is not the strength of the density exponent; it is that every
  density statement is quantified over a *fixed* `δ`, while the Riemann hypothesis is the limit
  `δ → 0`.
* `off_le_of_uniformDensity`, `uniformDensity_not_sufficient` — what a density bound *uniform in*
  `δ` would contribute, a hypothesis strictly stronger than the density hypothesis and beyond any
  known method: it does give a power saving `N_off(T) = O(T^(1−c))` for the whole off-line count,
  and it does not give the conjecture — `constOffCorpus` satisfies it with two zeroes off the
  critical line.

## Scope

Nothing here is a statement about `ζ`; as in `RiemannHypothesis.MethodCeiling`, these are
theorems about what can and cannot be deduced from a fixed list of inequalities between counting
functions.  Their value is negative and precise: they identify which additions to the list could
possibly help.  Any route that stays inside the list stops at `1 − θ`, so progress requires a new
*fact*, not a new argument — and, by `density_not_sufficient`, that new fact cannot be a
strengthening of a density theorem at fixed `δ`.
-/

namespace RiemannHypothesis

open Real

/-- The counting data of the repository's unconditional theorems about the zeroes of `ζ`, as an
abstract constraint system.  All the counts are cumulative over the ordinate window `(0, T]`, and
all of them are real numbers: the routes only ever use them through inequalities.

The parameter `θ` is the off-line proportion of a dyadic window that the mollifier machinery
allows; the repository's value is `θ = 0.33`, from
`RiemannHypothesis.sixty_seven_percent_on_critical_line`. -/
structure ZeroCorpus (θ : ℝ) where
  /-- `N(T)`: the nontrivial zeroes of ordinate in `(0, T]`, with multiplicity. -/
  total : ℝ → ℝ
  /-- `N_d(T)`: the *distinct* nontrivial zeroes of ordinate in `(0, T]`. -/
  distinct : ℝ → ℝ
  /-- `N₀(T)`: the distinct zeroes of ordinate in `(0, T]` on the critical line. -/
  onLine : ℝ → ℝ
  /-- `N_off(T)`: the distinct zeroes of ordinate in `(0, T]` off the critical line. -/
  off : ℝ → ℝ
  /-- `N_off(δ, T)`: the distinct zeroes of ordinate in `(0, T]` at distance at least `δ` from
  the critical line. -/
  offAt : ℝ → ℝ → ℝ
  total_nonneg : ∀ T, 0 ≤ total T
  off_nonneg : ∀ T, 0 ≤ off T
  onLine_nonneg : ∀ T, 0 ≤ onLine T
  /-- a zero off the critical line is not on it, and conversely -/
  split : ∀ T, off T + onLine T = distinct T
  /-- a distinct zero is counted at least once with multiplicity -/
  distinct_le_total : ∀ T, distinct T ≤ total T
  /-- the same, in every window: the counts are additive over ordinate windows -/
  distinct_window_le : ∀ T₁ T₂, T₁ ≤ T₂ → distinct T₂ - distinct T₁ ≤ total T₂ - total T₁
  total_mono : Monotone total
  off_mono : Monotone off
  offAt_mono : ∀ δ, Monotone (offAt δ)
  offAt_nonneg : ∀ δ T, 0 ≤ offAt δ T
  offAt_le_off : ∀ δ T, offAt δ T ≤ off T
  offAt_antitone : ∀ δ δ' T, 0 < δ → δ ≤ δ' → offAt δ' T ≤ offAt δ T
  /-- **The mollifier proportion.**  At least `1 − θ` of the zeroes of a dyadic window, counted
  with multiplicity on the left, lie on the critical line.  Repository:
  `sixty_seven_percent_on_critical_line`, with `θ = 0.33`. -/
  window_onLine : ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (1 - θ) * (total (2 * T) - total T) ≤ onLine (2 * T) - onLine T
  /-- **The Riemann–von Mangoldt formula.**  `N(T) = (T/2π) log T + O(T + (log T)²)`.
  Repository: `exists_abs_windowCount_zero_sub_main_le`. -/
  rvm : ∃ A : ℝ, 0 < A ∧ ∃ T₁ : ℝ, ∀ T ≥ T₁,
    |total T - T / (2 * π) * Real.log T| ≤ A * (T + (Real.log T) ^ 2)
  /-- **The Carlson power-saving density theorem.**  For each fixed `δ ∈ (0, 1/2)` the zeroes at
  distance at least `δ` from the critical line number `O(T^(1−c))` for some `c > 0` depending on
  `δ`.  Repository: `exists_ncard_zerosOffCriticalLine_le_rpow`. -/
  density : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧
    ∀ T ≥ (1 : ℝ), offAt δ T ≤ C * T ^ (1 - c)
  /-- **The quadruple symmetry of the off-line zeroes.**  An off-line zero of positive ordinate
  comes with its reflection `1 − ρ̄` in the critical line, of the same ordinate, so the off-line
  count of the upper half plane is even (and the full count is divisible by four).  Repository:
  `ncard_upperOffLineNontrivialZeros_eq_two_mul`, `four_dvd_ncard_offLineNontrivialZeros`. -/
  off_even : ∀ T, ∃ k : ℕ, off T = 2 * k
  /-- the same for the zeroes at distance at least `δ`: the reflection preserves the distance -/
  offAt_even : ∀ δ T, ∃ k : ℕ, offAt δ T = 2 * k
  /-- **The multiplicity bound.**  A zero of ordinate `γ` has multiplicity `O(log γ)`, so the
  count with multiplicity exceeds the distinct count by at most a factor `O(log T)`.
  Repository: `zeroMultiplicity_le_log_abs_im`, `multCount_le`. -/
  mult : ∃ C : ℝ, 0 < C ∧ ∃ T₂ : ℝ, ∀ T ≥ T₂, total T ≤ C * Real.log T * distinct T
  /-- **The classical zero-free region.**  There are no zeroes with `|Re ρ − 1/2| ≥ 1/2 − c/log T`
  and `0 < Im ρ ≤ T`.  Repository: `RiemannHypothesis.ZeroFreeClassical`. -/
  zeroFree : ∃ c : ℝ, 0 < c ∧ ∃ T₃ : ℝ, ∀ T ≥ T₃, ∀ δ : ℝ,
    1 / 2 - c / Real.log T ≤ δ → offAt δ T = 0
  /-- **The off-line count is attained at some positive distance.**  There are finitely many
  zeroes of ordinate at most `T`, and an off-line zero is at a positive distance from the
  critical line, so for each `T` some `δ > 0` already counts all of them. -/
  off_attained : ∀ T, ∃ δ : ℝ, 0 < δ ∧ offAt δ T = off T

namespace ZeroCorpus

variable {θ : ℝ}

/-- The zeroes of the dyadic window `(T, 2T]`, with multiplicity. -/
def windowTotal (Z : ZeroCorpus θ) (T : ℝ) : ℝ := Z.total (2 * T) - Z.total T

/-- The distinct off-line zeroes of the dyadic window `(T, 2T]`. -/
def windowOff (Z : ZeroCorpus θ) (T : ℝ) : ℝ := Z.off (2 * T) - Z.off T

/-- The distinct on-line zeroes of the dyadic window `(T, 2T]`. -/
def windowOn (Z : ZeroCorpus θ) (T : ℝ) : ℝ := Z.onLine (2 * T) - Z.onLine T

/-- **Soundness.**  In a corpus the off-line count of a dyadic window is eventually at most `θ`
times its total count: this is the mollifier bound, transported through the splitting of the
distinct zeroes and the inequality `N_d ≤ N`. -/
theorem windowOff_le (Z : ZeroCorpus θ) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, Z.windowOff T ≤ θ * Z.windowTotal T := by
  obtain ⟨T₀, hT₀⟩ := Z.window_onLine
  refine ⟨max T₀ 0, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have h := hT₀ T (le_trans (le_max_left _ _) hT)
  have hd := Z.distinct_window_le T (2 * T) (by linarith)
  have hs2 := Z.split (2 * T)
  have hs1 := Z.split T
  simp only [windowOff, windowTotal]
  linarith

end ZeroCorpus

/-! ## The Riemann hypothesis in the vocabulary of the corpus -/

/-- The Riemann hypothesis, as a statement about the counting functions of a corpus: no zero lies
off the critical line. -/
def RHCounts {θ : ℝ} (Z : ZeroCorpus θ) : Prop := ∀ T, Z.off T = 0


/-! ## The model

The counting functions of a configuration of zeroes that satisfies every fact of the corpus and
still has a positive proportion of its zeroes off the critical line, all of them at a distance
from the critical line that shrinks as the ordinate grows.  This is the configuration that the
repository's unconditional theorems cannot exclude. -/

/-- The main term of the Riemann–von Mangoldt formula, frozen below the height `32`. -/
noncomputable def rvmModel (T : ℝ) : ℝ := max T 32 / (2 * π) * Real.log (max T 32)

lemma log_thirtyTwo_gt : (3.4 : ℝ) < Real.log 32 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h32]
  linarith

lemma two_pi_pos : (6 : ℝ) < 2 * π := by linarith [Real.pi_gt_three]

lemma two_pi_lt : 2 * π < 6.3 := by linarith [Real.pi_lt_d2]

lemma log_ge_of_ge {T : ℝ} (hT : 32 ≤ T) : (3.4 : ℝ) ≤ Real.log T :=
  le_trans (le_of_lt log_thirtyTwo_gt) (Real.log_le_log (by norm_num) hT)

lemma log_max_ge (T : ℝ) : (3.4 : ℝ) ≤ Real.log (max T 32) :=
  log_ge_of_ge (le_max_right T 32)

lemma rvmModel_nonneg (T : ℝ) : 0 ≤ rvmModel T := by
  have hlog : (0 : ℝ) ≤ Real.log (max T 32) := by linarith [log_max_ge T]
  have hpos : (0 : ℝ) < 2 * π := by linarith [two_pi_pos]
  have hm : (0 : ℝ) ≤ max T 32 := le_trans (by norm_num) (le_max_right T 32)
  exact mul_nonneg (div_nonneg hm hpos.le) hlog

lemma rvmModel_mono : Monotone rvmModel := by
  intro a b hab
  have hm : max a 32 ≤ max b 32 := max_le_max hab le_rfl
  have hpos : (0 : ℝ) < 2 * π := by linarith [two_pi_pos]
  have ha : (0 : ℝ) ≤ max a 32 := le_trans (by norm_num) (le_max_right a 32)
  have hloga : (0 : ℝ) ≤ Real.log (max a 32) := by linarith [log_max_ge a]
  have hlogb : Real.log (max a 32) ≤ Real.log (max b 32) :=
    Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_right a 32)) hm
  have h1 : max a 32 / (2 * π) ≤ max b 32 / (2 * π) := div_le_div_of_nonneg_right hm hpos.le
  exact mul_le_mul h1 hlogb hloga (div_nonneg (le_trans ha hm) hpos.le)

lemma rvmModel_eq {T : ℝ} (hT : 32 ≤ T) : rvmModel T = T / (2 * π) * Real.log T := by
  rw [rvmModel, max_eq_left hT]

/-- The model count is at least `T/2`. -/
lemma rvmModel_ge_half {T : ℝ} (hT : 32 ≤ T) : T / 2 ≤ rvmModel T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hpos : (0 : ℝ) < 2 * π := by linarith [two_pi_pos]
  have hlt : 2 * π < 6.3 := two_pi_lt
  have hlogT : (3.4 : ℝ) ≤ Real.log T := log_ge_of_ge hT
  have hrw : rvmModel T = T * Real.log T / (2 * π) := by
    rw [rvmModel_eq hT]; ring
  rw [hrw, le_div_iff₀ hpos]
  nlinarith [hT0, hlogT, hlt]

/-- The model count is at least `2` at every height. -/
lemma rvmModel_ge_two (T : ℝ) : 2 ≤ rvmModel T := by
  have hm : (32 : ℝ) ≤ max T 32 := le_max_right _ _
  have hlog : (3.4 : ℝ) ≤ Real.log (max T 32) := log_max_ge T
  have hpos : (0 : ℝ) < 2 * π := by linarith [two_pi_pos]
  have hlt : 2 * π < 6.3 := two_pi_lt
  have hrw : rvmModel T = max T 32 * Real.log (max T 32) / (2 * π) := by
    rw [rvmModel]; ring
  rw [hrw, le_div_iff₀ hpos]
  nlinarith [hm, hlog, hlt]

/-- The growth of the model count over a dyadic window: at least `T/2`. -/
lemma rvmModel_window_ge {T : ℝ} (hT : 32 ≤ T) : T / 2 ≤ rvmModel (2 * T) - rvmModel T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have h2T : (32 : ℝ) ≤ 2 * T := by linarith
  have hpos : (0 : ℝ) < 2 * π := by linarith [two_pi_pos]
  have hlt : 2 * π < 6.3 := two_pi_lt
  have hlogT : (3.4 : ℝ) ≤ Real.log T := log_ge_of_ge hT
  have hlog2 : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2T : Real.log (2 * T) = Real.log 2 + Real.log T :=
    Real.log_mul (by norm_num) (ne_of_gt hT0)
  have hkey : rvmModel (2 * T) - rvmModel T = T * (2 * Real.log 2 + Real.log T) / (2 * π) := by
    rw [rvmModel_eq h2T, rvmModel_eq hT, hlog2T]
    field_simp
    ring
  rw [hkey, le_div_iff₀ hpos]
  nlinarith [hT0, hlogT, hlt, hlog2]

/-- The off-line count of the model, at rate `r`: an even integer close to `r · N(T)`. -/
noncomputable def offModel (r T : ℝ) : ℝ := 2 * (⌊r / 2 * rvmModel T⌋₊ : ℝ)

/-- The off-line count of the model at distance at least `δ`: the model's off-line zeroes are
listed with distances `1/5, 1/6, 1/7, …` from the critical line, so at most `⌊1/δ⌋ − 4` of them
are at distance `≥ δ`, uniformly in the height. -/
noncomputable def offAtModel (r δ T : ℝ) : ℝ :=
  min (offModel r T) (2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ))

lemma offModel_nonneg (r T : ℝ) : 0 ≤ offModel r T := by
  unfold offModel; positivity

lemma offModel_le {r T : ℝ} (hr : 0 ≤ r) : offModel r T ≤ r * rvmModel T := by
  have hx : (0 : ℝ) ≤ r / 2 * rvmModel T := mul_nonneg (by linarith) (rvmModel_nonneg T)
  have h := Nat.floor_le hx
  unfold offModel
  linarith

lemma offModel_ge (r T : ℝ) : r * rvmModel T - 2 ≤ offModel r T := by
  have h := Nat.lt_floor_add_one (r / 2 * rvmModel T)
  unfold offModel
  linarith

lemma offModel_mono {r : ℝ} (hr : 0 ≤ r) : Monotone (offModel r) := by
  intro a b hab
  have h := rvmModel_mono hab
  have hle : r / 2 * rvmModel a ≤ r / 2 * rvmModel b :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have : (⌊r / 2 * rvmModel a⌋₊ : ℝ) ≤ (⌊r / 2 * rvmModel b⌋₊ : ℝ) := by
    exact_mod_cast Nat.floor_le_floor hle
  unfold offModel
  linarith

lemma offAtModel_nonneg (r δ T : ℝ) : 0 ≤ offAtModel r δ T :=
  le_min (offModel_nonneg r T) (by positivity)

lemma offAtModel_le_offModel (r δ T : ℝ) : offAtModel r δ T ≤ offModel r T := min_le_left _ _

lemma offAtModel_le_two_div {r δ T : ℝ} (hδ : 0 < δ) : offAtModel r δ T ≤ 2 / δ := by
  have h1 : ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) ≤ (⌊1 / δ⌋₊ : ℝ) := by exact_mod_cast Nat.sub_le _ _
  have h2 : (⌊1 / δ⌋₊ : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
  have h3 : offAtModel r δ T ≤ 2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) := min_le_right _ _
  have hd : 2 * (1 / δ) = 2 / δ := by ring
  linarith

/-- **The model corpus.**  For every rate `r` strictly below the mollifier proportion `θ` there is
a corpus — a counting configuration satisfying every unconditional fact of the repository — whose
off-line count is `r·N(T) + O(1)`.  Its off-line zeroes at distance at least `δ` from the critical
line number at most `2/δ`, *uniformly in the height*: they crowd towards the critical line as the
ordinate grows, which is exactly what no density theorem at a fixed `δ` can see. -/
noncomputable def modelCorpus (θ r : ℝ) (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1) :
    ZeroCorpus θ where
  total := rvmModel
  distinct := rvmModel
  onLine := fun T => rvmModel T - offModel r T
  off := offModel r
  offAt := offAtModel r
  total_nonneg := rvmModel_nonneg
  off_nonneg := offModel_nonneg r
  onLine_nonneg := by
    intro T
    have h := offModel_le (r := r) (T := T) hr.le
    have hm := rvmModel_nonneg T
    nlinarith
  split := by intro T; ring
  distinct_le_total := fun _ => le_rfl
  distinct_window_le := fun _ _ _ => le_rfl
  total_mono := rvmModel_mono
  off_mono := offModel_mono hr.le
  offAt_mono := fun _ _ _ hab => min_le_min (offModel_mono hr.le hab) le_rfl
  offAt_nonneg := offAtModel_nonneg r
  offAt_le_off := offAtModel_le_offModel r
  offAt_antitone := by
    intro δ δ' T hδ hδδ'
    refine min_le_min le_rfl ?_
    have h1 : 1 / δ' ≤ 1 / δ := one_div_le_one_div_of_le hδ hδδ'
    have h2 : (⌊1 / δ'⌋₊ - 4 : ℕ) ≤ (⌊1 / δ⌋₊ - 4 : ℕ) :=
      Nat.sub_le_sub_right (Nat.floor_le_floor h1) 4
    have h3 : ((⌊1 / δ'⌋₊ - 4 : ℕ) : ℝ) ≤ ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  window_onLine := by
    refine ⟨max 32 (4 / (θ - r)), fun T hT => ?_⟩
    have hT32 : (32 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
    have hTr : 4 / (θ - r) ≤ T := le_trans (le_max_right _ _) hT
    have hθr : 0 < θ - r := by linarith
    have hW : T / 2 ≤ rvmModel (2 * T) - rvmModel T := rvmModel_window_ge hT32
    have h4 : 4 ≤ (θ - r) * T := by
      rw [div_le_iff₀ hθr] at hTr
      linarith
    have hlo := offModel_ge r T
    have hhi := offModel_le (r := r) (T := 2 * T) hr.le
    have hmono := rvmModel_mono (show T ≤ 2 * T by linarith)
    change (1 - θ) * (rvmModel (2 * T) - rvmModel T)
      ≤ (rvmModel (2 * T) - offModel r (2 * T)) - (rvmModel T - offModel r T)
    nlinarith [hW, h4, hlo, hhi, hmono]
  rvm := by
    refine ⟨1, one_pos, 32, fun T hT => ?_⟩
    have hT0 : (0 : ℝ) < T := by linarith
    change |rvmModel T - T / (2 * π) * Real.log T| ≤ 1 * (T + (Real.log T) ^ 2)
    rw [rvmModel_eq hT, sub_self, abs_zero]
    positivity
  density := by
    intro δ hδ _
    refine ⟨1 / 2, 2 / δ + 1, by norm_num, by norm_num, by positivity, fun T hT => ?_⟩
    have h1 : offAtModel r δ T ≤ 2 / δ := offAtModel_le_two_div hδ
    have h2 : (1 : ℝ) ≤ T ^ (1 - 1 / 2 : ℝ) := Real.one_le_rpow hT (by norm_num)
    have h3 : (0 : ℝ) < 2 / δ + 1 := by positivity
    change offAtModel r δ T ≤ (2 / δ + 1) * T ^ (1 - 1 / 2 : ℝ)
    nlinarith
  off_even := fun T => ⟨⌊r / 2 * rvmModel T⌋₊, rfl⟩
  offAt_even := by
    intro δ T
    refine ⟨min ⌊r / 2 * rvmModel T⌋₊ (⌊1 / δ⌋₊ - 4 : ℕ), ?_⟩
    show offAtModel r δ T = 2 * ((min ⌊r / 2 * rvmModel T⌋₊ (⌊1 / δ⌋₊ - 4 : ℕ) : ℕ) : ℝ)
    unfold offAtModel offModel
    rcases le_total (⌊r / 2 * rvmModel T⌋₊ : ℕ) ((⌊1 / δ⌋₊ - 4 : ℕ)) with h | h
    · have hc : (⌊r / 2 * rvmModel T⌋₊ : ℝ) ≤ ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) := by exact_mod_cast h
      rw [min_eq_left h, min_eq_left (by linarith : 2 * (⌊r / 2 * rvmModel T⌋₊ : ℝ) ≤
        2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ))]
    · have hc : ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) ≤ (⌊r / 2 * rvmModel T⌋₊ : ℝ) := by exact_mod_cast h
      rw [min_eq_right h, min_eq_right (by linarith : 2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) ≤
        2 * (⌊r / 2 * rvmModel T⌋₊ : ℝ))]
  mult := by
    refine ⟨1, one_pos, 32, fun T hT => ?_⟩
    have hlogT : (3.4 : ℝ) ≤ Real.log T := log_ge_of_ge hT
    have hm := rvmModel_nonneg T
    change rvmModel T ≤ 1 * Real.log T * rvmModel T
    nlinarith
  zeroFree := by
    refine ⟨1, one_pos, 300, fun T hT δ hδ => ?_⟩
    have hlogT : (5.5 : ℝ) ≤ Real.log T := by
      have h256 : Real.log 256 = 8 * Real.log 2 := by
        rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
        push_cast; ring
      have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hle : Real.log 256 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
      rw [h256] at hle
      linarith
    have hδ' : (0.3 : ℝ) < δ := by
      have h1 : 1 / Real.log T ≤ 1 / 5.5 := one_div_le_one_div_of_le (by norm_num) hlogT
      linarith
    have h1δ : 1 / δ < 4 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have hfloor : ⌊1 / δ⌋₊ < 4 := (Nat.floor_lt (by positivity)).2 (by exact_mod_cast h1δ)
    have hsub : (⌊1 / δ⌋₊ - 4 : ℕ) = 0 := by omega
    change offAtModel r δ T = 0
    unfold offAtModel
    rw [hsub]
    simp only [Nat.cast_zero, mul_zero]
    exact min_eq_right (offModel_nonneg r T)
  off_attained := by
    intro T
    set k : ℕ := ⌊r / 2 * rvmModel T⌋₊ with hk
    refine ⟨1 / ((k : ℝ) + 5), by positivity, ?_⟩
    have hinv : 1 / (1 / ((k : ℝ) + 5)) = (k : ℝ) + 5 := one_div_one_div _
    have hcast : ((k : ℝ) + 5) = ((k + 5 : ℕ) : ℝ) := by push_cast; ring
    have hfloor : ⌊1 / (1 / ((k : ℝ) + 5))⌋₊ = k + 5 := by
      rw [hinv, hcast, Nat.floor_natCast]
    change offAtModel r (1 / ((k : ℝ) + 5)) T = offModel r T
    unfold offAtModel offModel
    rw [hfloor, show k + 5 - 4 = k + 1 by omega]
    refine min_eq_left ?_
    have : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    push_cast
    linarith

@[simp] lemma modelCorpus_total {θ r : ℝ} (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1) :
    (modelCorpus θ r hr hrθ hθ).total = rvmModel := rfl

@[simp] lemma modelCorpus_off {θ r : ℝ} (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1) :
    (modelCorpus θ r hr hrθ hθ).off = offModel r := rfl

@[simp] lemma modelCorpus_onLine {θ r : ℝ} (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1) :
    (modelCorpus θ r hr hrθ hθ).onLine = fun T => rvmModel T - offModel r T := rfl

@[simp] lemma modelCorpus_offAt {θ r : ℝ} (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1) :
    (modelCorpus θ r hr hrθ hθ).offAt = offAtModel r := rfl

/-! ## What the corpus can and cannot prove -/

/-- In the model corpus the off-line count of a dyadic window is eventually at least `r − ε` times
its total count: a positive proportion of the zeroes lies off the critical line. -/
theorem modelCorpus_windowOff_ge {θ r : ℝ} (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (r - ε) * (modelCorpus θ r hr hrθ hθ).windowTotal T
        ≤ (modelCorpus θ r hr hrθ hθ).windowOff T := by
  refine ⟨max 32 (4 / ε), fun T hT => ?_⟩
  have hT32 : (32 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hTε : 4 / ε ≤ T := le_trans (le_max_right _ _) hT
  have hW : T / 2 ≤ rvmModel (2 * T) - rvmModel T := rvmModel_window_ge hT32
  have h4 : 4 ≤ ε * T := by
    rw [div_le_iff₀ hε] at hTε
    linarith
  have hlo := offModel_ge r (2 * T)
  have hhi := offModel_le (r := r) (T := T) hr.le
  change (r - ε) * (rvmModel (2 * T) - rvmModel T) ≤ offModel r (2 * T) - offModel r T
  nlinarith [hW, h4, hlo, hhi]

/-- In the model corpus the zeroes at distance at least `δ` from the critical line number at most
`2/δ`, **uniformly in the height**.  Every density theorem — including bounds far stronger than
any that is known, and stronger than the density hypothesis — therefore holds in the model. -/
theorem modelCorpus_offAt_bounded {θ r : ℝ} (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (T : ℝ) : (modelCorpus θ r hr hrθ hθ).offAt δ T ≤ 2 / δ :=
  offAtModel_le_two_div hδ

/-- In the model corpus the off-line count is positive from a finite height on: the configuration
violates the Riemann hypothesis. -/
theorem modelCorpus_off_pos {θ r : ℝ} (hr : 0 < r) (hrθ : r < θ) (hθ : θ ≤ 1) {T : ℝ}
    (hT32 : 32 ≤ T) (hTr : 4 / r ≤ T) : 0 < (modelCorpus θ r hr hrθ hθ).off T := by
  have hTT : T / 2 ≤ rvmModel T := rvmModel_ge_half hT32
  have hTr' : 4 ≤ r * T := by
    rw [div_le_iff₀ hr] at hTr
    linarith
  have hrT : (1 : ℝ) ≤ r / 2 * rvmModel T := by nlinarith [hTT, hr]
  have hfloor : 1 ≤ ⌊r / 2 * rvmModel T⌋₊ := Nat.le_floor (by exact_mod_cast hrT)
  have hcast : (1 : ℝ) ≤ (⌊r / 2 * rvmModel T⌋₊ : ℝ) := by exact_mod_cast hfloor
  change 0 < offModel r T
  unfold offModel
  linarith

/-- **The Riemann hypothesis is not derivable from the corpus.**  With the repository's own
mollifier constant `θ = 0.33`, there is a counting configuration satisfying every unconditional
fact the repository proves in which some zeroes lie off the critical line. -/
theorem rh_not_derivable_from_corpus : ¬ ∀ Z : ZeroCorpus 0.33, RHCounts Z := by
  intro h
  have hpos := modelCorpus_off_pos (θ := 0.33) (r := 0.3) (by norm_num) (by norm_num)
    (by norm_num) (T := 32) le_rfl (by norm_num)
  rw [h (modelCorpus 0.33 0.3 (by norm_num) (by norm_num) (by norm_num)) 32] at hpos
  exact lt_irrefl 0 hpos

/-- **The corpus does not even give a zero proportion off the critical line.**  For every
`q < 0.33` there is a configuration satisfying all the facts in which the off-line zeroes are
eventually at least a proportion `q` of the zeroes of a dyadic window. -/
theorem offLine_positive_proportion_consistent {q : ℝ} (hq : 0 < q) (hq' : q < 0.33) :
    ∃ Z : ZeroCorpus 0.33, ∃ T₀ : ℝ, ∀ T ≥ T₀, q * Z.windowTotal T ≤ Z.windowOff T := by
  obtain ⟨r, hqr, hrθ⟩ := exists_between hq'
  have hr : 0 < r := lt_trans hq hqr
  refine ⟨modelCorpus 0.33 r hr hrθ (by norm_num), ?_⟩
  obtain ⟨T₀, hT₀⟩ := modelCorpus_windowOff_ge (θ := 0.33) hr hrθ (by norm_num)
    (ε := r - q) (by linarith)
  exact ⟨T₀, fun T hT => by simpa [show r - (r - q) = q by ring] using hT₀ T hT⟩

/-- **A density theorem at a fixed `δ`, however strong, cannot close the gap.**  There is a
configuration satisfying every fact of the corpus in which, for each fixed `δ > 0`, the zeroes at
distance at least `δ` from the critical line are *bounded in the height* — so every density bound
of the shape `N(σ, T) ≪ T^(1−c)`, and every strengthening of it up to a bound uniform in `T`,
holds — and which nevertheless has zeroes off the critical line.  The obstruction to the density
route is not the size of the exponent; it is the order of the quantifiers. -/
theorem density_not_sufficient :
    ∃ Z : ZeroCorpus 0.33, (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, Z.offAt δ T ≤ C) ∧ ¬ RHCounts Z := by
  refine ⟨modelCorpus 0.33 0.3 (by norm_num) (by norm_num) (by norm_num), ?_, ?_⟩
  · exact fun δ hδ => ⟨2 / δ, fun T => modelCorpus_offAt_bounded _ _ _ hδ T⟩
  · intro h
    have hpos := modelCorpus_off_pos (θ := 0.33) (r := 0.3) (by norm_num) (by norm_num)
      (by norm_num) (T := 32) le_rfl (by norm_num)
    rw [h 32] at hpos
    exact lt_irrefl 0 hpos

/-- **The exact ceiling of the corpus.**  A proportion `p` of the zeroes of a dyadic window on the
critical line is derivable from the whole corpus **if and only if** `p ≤ 1 − θ`.  At the
repository's `θ = 0.33` the ceiling is the `67 %` that `sixty_seven_percent_on_critical_line`
already proves: adding the Riemann–von Mangoldt formula, the density theorem, the quadruple
symmetry, the multiplicity bound and the zero-free region to the mollifier bound buys nothing. -/
theorem corpus_window_ceiling {θ p : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (∀ Z : ZeroCorpus θ, ∃ T₀ : ℝ, ∀ T ≥ T₀, p * Z.windowTotal T ≤ Z.windowOn T) ↔ p ≤ 1 - θ := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    set ε : ℝ := min ((p - (1 - θ)) / 3) (θ / 2) with hεdef
    have hε1 : ε ≤ (p - (1 - θ)) / 3 := min_le_left _ _
    have hε2 : ε ≤ θ / 2 := min_le_right _ _
    have hε : 0 < ε := lt_min (by linarith) (by linarith)
    have hrlt : θ - ε < θ := by linarith
    have hrpos : 0 < θ - ε := by linarith
    obtain ⟨T₀, hT₀⟩ := h (modelCorpus θ (θ - ε) hrpos hrlt hθ1)
    obtain ⟨T₁, hT₁⟩ :=
      modelCorpus_windowOff_ge (θ := θ) (r := θ - ε) hrpos hrlt hθ1 (ε := ε) hε
    set T : ℝ := max (max T₀ T₁) 32 with hTdef
    have hT32 : (32 : ℝ) ≤ T := le_max_right _ _
    have h1 := hT₀ T (le_trans (le_max_left _ _) (le_max_left _ _))
    have h2 := hT₁ T (le_trans (le_max_right _ _) (le_max_left _ _))
    have hWval : (modelCorpus θ (θ - ε) hrpos hrlt hθ1).windowTotal T
        = rvmModel (2 * T) - rvmModel T := rfl
    have hOffval : (modelCorpus θ (θ - ε) hrpos hrlt hθ1).windowOff T
        = offModel (θ - ε) (2 * T) - offModel (θ - ε) T := rfl
    have hOnval : (modelCorpus θ (θ - ε) hrpos hrlt hθ1).windowOn T
        = (rvmModel (2 * T) - rvmModel T)
          - (offModel (θ - ε) (2 * T) - offModel (θ - ε) T) := by
      change (rvmModel (2 * T) - offModel (θ - ε) (2 * T))
          - (rvmModel T - offModel (θ - ε) T) = _
      ring
    rw [hWval, hOnval] at h1
    rw [hWval, hOffval] at h2
    have hW : T / 2 ≤ rvmModel (2 * T) - rvmModel T := rvmModel_window_ge hT32
    have hWpos : 0 < rvmModel (2 * T) - rvmModel T := by linarith
    have hkey : p * (rvmModel (2 * T) - rvmModel T)
        ≤ (1 - θ + 2 * ε) * (rvmModel (2 * T) - rvmModel T) := by nlinarith [h1, h2]
    have hple : p ≤ 1 - θ + 2 * ε := le_of_mul_le_mul_right (by linarith [hkey]) hWpos
    linarith
  · intro hp Z
    obtain ⟨T₀, hT₀⟩ := Z.window_onLine
    refine ⟨max T₀ 0, fun T hT => ?_⟩
    have hT0 : (0 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
    have h := hT₀ T (le_trans (le_max_left _ _) hT)
    have hWnn : 0 ≤ Z.windowTotal T := by
      have hm := Z.total_mono (show T ≤ 2 * T by linarith)
      simp only [ZeroCorpus.windowTotal]
      linarith
    have hmul : p * Z.windowTotal T ≤ (1 - θ) * Z.windowTotal T :=
      mul_le_mul_of_nonneg_right hp hWnn
    simp only [ZeroCorpus.windowOn, ZeroCorpus.windowTotal] at *
    linarith

/-! ## The density hypothesis, in full strength

`density_not_sufficient` shows that a density theorem at a fixed `δ` cannot reach the conjecture.
The next question is what happens if the density bound is granted *uniformly in `δ`* — a
hypothesis no method is close to, and strictly stronger than the density hypothesis.  The answer
is that it does buy something, namely a power saving for the whole off-line count
(`off_le_of_uniformDensity`), and that it still does not reach the conjecture
(`uniformDensity_not_sufficient`). -/

/-- The density bound granted *uniformly in the distance `δ`*: one pair of constants works for
every `δ > 0` at once.  This is far beyond the Carlson power saving, beyond the density
hypothesis, and beyond Lindelöf-strength density bounds, all of which fix `δ` first. -/
def UniformDensity {θ : ℝ} (Z : ZeroCorpus θ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ T ≥ (1 : ℝ), Z.offAt δ T ≤ C * T ^ (1 - c)

/-- **What the uniform density hypothesis does buy.**  Because the off-line count of a height is
already attained at some positive distance, a density bound uniform in `δ` transfers to the whole
off-line count: `N_off(T) = O(T^(1−c))`. -/
theorem off_le_of_uniformDensity {θ : ℝ} {Z : ZeroCorpus θ} (h : UniformDensity Z) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ ∀ T ≥ (1 : ℝ), Z.off T ≤ C * T ^ (1 - c) := by
  obtain ⟨c, C, hc0, hc1, hC0, hbd⟩ := h
  refine ⟨c, C, hc0, hc1, hC0, fun T hT => ?_⟩
  obtain ⟨δ, hδ, hδeq⟩ := Z.off_attained T
  rw [← hδeq]
  exact hbd δ hδ T hT

/-- The counting functions of a configuration with exactly two off-line zeroes, sitting at
distance `1/6` from the critical line: the smallest violation of the Riemann hypothesis that the
corpus tolerates. -/
noncomputable def constOffCorpus (θ : ℝ) (hθ0 : 0 < θ) : ZeroCorpus θ where
  total := rvmModel
  distinct := rvmModel
  onLine := fun T => rvmModel T - 2
  off := fun _ => 2
  offAt := fun δ _ => min 2 (2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ))
  total_nonneg := rvmModel_nonneg
  off_nonneg := fun _ => by norm_num
  onLine_nonneg := fun T => by linarith [rvmModel_ge_two T]
  split := fun T => by ring
  distinct_le_total := fun _ => le_rfl
  distinct_window_le := fun _ _ _ => le_rfl
  total_mono := rvmModel_mono
  off_mono := fun _ _ _ => le_rfl
  offAt_mono := fun _ _ _ _ => le_rfl
  offAt_nonneg := fun _ _ => le_min (by norm_num) (by positivity)
  offAt_le_off := fun _ _ => min_le_left _ _
  offAt_antitone := by
    intro δ δ' T hδ hδδ'
    refine min_le_min le_rfl ?_
    have h1 : 1 / δ' ≤ 1 / δ := one_div_le_one_div_of_le hδ hδδ'
    have h2 : (⌊1 / δ'⌋₊ - 4 : ℕ) ≤ (⌊1 / δ⌋₊ - 4 : ℕ) :=
      Nat.sub_le_sub_right (Nat.floor_le_floor h1) 4
    have h3 : ((⌊1 / δ'⌋₊ - 4 : ℕ) : ℝ) ≤ ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  window_onLine := by
    refine ⟨32, fun T hT => ?_⟩
    have hW : T / 2 ≤ rvmModel (2 * T) - rvmModel T := rvmModel_window_ge hT
    have hT0 : (0 : ℝ) < T := by linarith
    change (1 - θ) * (rvmModel (2 * T) - rvmModel T)
      ≤ (rvmModel (2 * T) - 2) - (rvmModel T - 2)
    nlinarith
  rvm := by
    refine ⟨1, one_pos, 32, fun T hT => ?_⟩
    have hT0 : (0 : ℝ) < T := by linarith
    change |rvmModel T - T / (2 * π) * Real.log T| ≤ 1 * (T + (Real.log T) ^ 2)
    rw [rvmModel_eq hT, sub_self, abs_zero]
    positivity
  density := by
    intro δ hδ _
    refine ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num, fun T hT => ?_⟩
    have h2 : (1 : ℝ) ≤ T ^ (1 - 1 / 2 : ℝ) := Real.one_le_rpow hT (by norm_num)
    have h1 : min (2 : ℝ) (2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ)) ≤ 2 := min_le_left _ _
    change min (2 : ℝ) (2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ)) ≤ 2 * T ^ (1 - 1 / 2 : ℝ)
    linarith
  off_even := fun _ => ⟨1, by norm_num⟩
  offAt_even := by
    intro δ T
    refine ⟨min 1 (⌊1 / δ⌋₊ - 4 : ℕ), ?_⟩
    rcases le_total (1 : ℕ) (⌊1 / δ⌋₊ - 4 : ℕ) with h | h
    · have hc : (1 : ℝ) ≤ ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) := by exact_mod_cast h
      rw [min_eq_left h, min_eq_left (by linarith : (2 : ℝ) ≤ 2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ))]
      norm_num
    · have hc : ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h
      rw [min_eq_right h, min_eq_right (by linarith : 2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ) ≤ (2 : ℝ))]
  mult := by
    refine ⟨1, one_pos, 32, fun T hT => ?_⟩
    have hlogT : (3.4 : ℝ) ≤ Real.log T := log_ge_of_ge hT
    have hm := rvmModel_nonneg T
    change rvmModel T ≤ 1 * Real.log T * rvmModel T
    nlinarith
  zeroFree := by
    refine ⟨1, one_pos, 300, fun T hT δ hδ => ?_⟩
    have hlogT : (5.5 : ℝ) ≤ Real.log T := by
      have h256 : Real.log 256 = 8 * Real.log 2 := by
        rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
        push_cast; ring
      have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hle : Real.log 256 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
      rw [h256] at hle
      linarith
    have hδ' : (0.3 : ℝ) < δ := by
      have h1 : 1 / Real.log T ≤ 1 / 5.5 := one_div_le_one_div_of_le (by norm_num) hlogT
      linarith
    have h1δ : 1 / δ < 4 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have hfloor : ⌊1 / δ⌋₊ < 4 := (Nat.floor_lt (by positivity)).2 (by exact_mod_cast h1δ)
    have hsub : (⌊1 / δ⌋₊ - 4 : ℕ) = 0 := by omega
    change min (2 : ℝ) (2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ)) = 0
    rw [hsub]
    norm_num
  off_attained := by
    intro T
    refine ⟨1 / 6, by norm_num, ?_⟩
    have hfloor : ⌊1 / (1 / 6 : ℝ)⌋₊ = 6 := by
      rw [show (1 : ℝ) / (1 / 6) = ((6 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
    change min (2 : ℝ) (2 * ((⌊1 / (1 / 6 : ℝ)⌋₊ - 4 : ℕ) : ℝ)) = 2
    rw [hfloor]
    norm_num

/-- **Even the density hypothesis granted uniformly in `δ` does not give the Riemann
hypothesis.**  There is a configuration satisfying every fact of the corpus, and satisfying a
density bound uniform in `δ`, with two zeroes off the critical line.  Together with
`off_le_of_uniformDensity` this delimits exactly what a full-strength density theorem would
contribute: a power saving for the off-line count, never its vanishing. -/
theorem uniformDensity_not_sufficient :
    ∃ Z : ZeroCorpus 0.33, UniformDensity Z ∧ ¬ RHCounts Z := by
  refine ⟨constOffCorpus 0.33 (by norm_num), ?_, ?_⟩
  · refine ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num, fun δ _ T hT => ?_⟩
    have h2 : (1 : ℝ) ≤ T ^ (1 - 1 / 2 : ℝ) := Real.one_le_rpow hT (by norm_num)
    have h1 : min (2 : ℝ) (2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ)) ≤ 2 := min_le_left _ _
    change min (2 : ℝ) (2 * ((⌊1 / δ⌋₊ - 4 : ℕ) : ℝ)) ≤ 2 * T ^ (1 - 1 / 2 : ℝ)
    linarith
  · intro h
    have := h 32
    change (2 : ℝ) = 0 at this
    norm_num at this

end RiemannHypothesis
