/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.BrunTitchmarshProgressions

/-!
# Brun–Titchmarsh with the constant `2π + o(1)`

`RiemannHypothesis/BrunTitchmarsh.lean` sieves the interval `[x, x + y)` at the rigid level
`Q = ⌊√y⌋`, which makes the term `Q²` of the large sieve as large as the term `π y` and loses an
additive `log 2` in the sifting sum; the resulting constant is `13`, or `9` above `log y ≥ 24`.
Its scope section names the remedy:

> With the sharp large sieve and `Q = √y / log y` the same route gives `2 + o(1)`; with the factor
> `π` kept and `Q` optimized it would give `2π + o(1)`.

This file carries that out.  The sieve is run at a *free* level `Q`, and then at
`Q = ⌊√y / log y⌋`, for which `Q² ≤ y/(log y)²` is negligible against `π y` while the sifting sum
is still `(1/2) log y (1 + o(1))`.

## Main results

* `card_primes_Ico_le_of_level` — the sieve at an arbitrary level `Q ≥ 2`:

      #{p prime : x ≤ p < x + y} ≤ (Q² + π y)/log Q + Q + 1 .

* `card_primes_Ico_le_two_pi` — the Brun–Titchmarsh theorem with the constant `2π + ε`: for every
  `ε > 0` there is a `Y` with

      #{p prime : x ≤ p < x + y} ≤ (2π + ε) y / log y

  for every `y ≥ Y` and *every* starting point `x`.

`2π = 6.283…` replaces the `13` and the `9` of the previous row.  The remaining factor `π` is the
one the repository's large sieve carries in place of the sharp `1`: with the sharp constant
`Q² + N − 1` of Selberg and Montgomery–Vaughan the same argument would give `2 + o(1)`, the
classical Brun–Titchmarsh theorem.

## Proof

At level `Q` the sieve `card_mul_siftSum_le` gives `|A| · siftSum Q ≤ Q² + π y` for the set `A` of
primes of the interval exceeding `Q`, and `log Q ≤ siftSum Q` (`log_le_siftSum`); the primes below
`Q` number at most `Q + 1`.  Taking `Q = ⌊√y/log y⌋` and writing `t = log y`, `s = √y`:
`Q ≤ s/t` gives `Q² ≤ y/t²`, and `Q ≥ s/t − 1 ≥ s/(2t)` gives `log Q ≥ t/2 − log t − log 2`.  The
elementary bound `log t ≤ 2√t` then makes both losses `O(√t)`, negligible against `t/2` once
`t ≥ (1000/ε)²`, and `Q + 1 ≤ s/t + 1` is negligible against `y/t` because `s = √y`.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace BrunTitchmarsh

/-! ## The sieve at a free level -/

/-- **Brun–Titchmarsh at an arbitrary sieve level `Q ≥ 2`.**  Uniformly in the starting point `x`,

`#{p prime : x ≤ p < x + y} ≤ (Q² + π y)/log Q + Q + 1`.

The primes of the interval that exceed `Q` avoid a residue class modulo every prime `p ≤ Q`, so
the large sieve applies to them; the primes at most `Q` are at most `Q + 1` in number. -/
theorem card_primes_Ico_le_of_level (x y : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) :
    (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + Real.pi * y) / Real.log Q + Q + 1 := by
  classical
  set S := (range y).filter (fun m => (x + m).Prime) with hSdef
  set A := S.filter (fun m => Q < x + m) with hAdef
  set B := S.filter (fun m => ¬ (Q < x + m)) with hBdef
  have hAB : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not _
  have hBcard : B.card ≤ Q + 1 := by
    have hsub : B ⊆ range (Q + 1) := by
      intro m hm
      obtain ⟨-, hle⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_range.2 (by omega)
    simpa using Finset.card_le_card hsub
  have hAsub : A ⊆ range y :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmain := card_mul_siftSum_le (N := y) hQ hAsub
    (fun p hp hpQ => shifted_primes_avoid x y Q hp hpQ)
  have hlogpos : 0 < Real.log Q := by
    have h2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 1) (by linarith : (1:ℝ) < (Q : ℝ))
    simpa using this
  have hsift : Real.log Q ≤ siftSum Q := log_le_siftSum Q
  have hAcard0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hA : (A.card : ℝ) ≤ ((Q : ℝ) ^ 2 + Real.pi * y) / Real.log Q := by
    rw [le_div_iff₀ hlogpos]
    calc (A.card : ℝ) * Real.log Q ≤ (A.card : ℝ) * siftSum Q :=
          mul_le_mul_of_nonneg_left hsift hAcard0
      _ ≤ (Q : ℝ) ^ 2 + Real.pi * y := hmain
  have hB : (B.card : ℝ) ≤ (Q : ℝ) + 1 := by exact_mod_cast hBcard
  have hcast : (S.card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hAB.symm
  rw [card_primes_Ico_eq, ← hSdef, hcast]
  linarith

/-! ## Elementary inequalities -/

/-- `log t ≤ 2 √t` for `t > 0`: `log t = 2 log √t ≤ 2(√t − 1)`. -/
theorem log_le_two_mul_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt ht.le] at h
  linarith

/-- `√y ≥ (log y)² / 16`: writing `y = exp t`, `√y = exp(t/2) = (exp(t/4))² ≥ (1 + t/4)²`. -/
theorem sq_log_le_sixteen_mul_sqrt {y : ℝ} (hy : 0 < y) (ht : 0 ≤ Real.log y) :
    Real.log y ^ 2 / 16 ≤ Real.sqrt y := by
  set t := Real.log y with htdef
  have hexp : Real.exp t = y := Real.exp_log hy
  have h1 : (1 : ℝ) + t / 4 ≤ Real.exp (t / 4) := by
    have := Real.add_one_le_exp (t / 4)
    linarith
  have h2 : Real.exp (t / 4) ^ 2 = Real.exp (t / 2) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have h3 : Real.exp (t / 2) = Real.sqrt y := by
    have hy2 : y = Real.exp (t / 2) ^ 2 := by
      rw [sq, ← Real.exp_add, show t / 2 + t / 2 = t by ring, hexp]
    rw [hy2, Real.sqrt_sq (Real.exp_pos _).le]
  have h4 : (1 + t / 4) ^ 2 ≤ Real.exp (t / 4) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 1 + t / 4 := by linarith
    nlinarith [h1, h0]
  have h5 : t ^ 2 / 16 ≤ (1 + t / 4) ^ 2 := by nlinarith
  rw [← h3, ← h2]
  linarith

/-! ## Brun–Titchmarsh with the constant `2π + ε` -/

set_option maxHeartbeats 1000000 in
-- the numeric chain of the proof is long, and does not fit in the default heartbeat budget
/-- **The numeric heart of the optimization**, at the sieve level `Q = ⌊√y / log y⌋`, for `ε ≤ 1`
and with the threshold made explicit: `log y ≥ (1000/ε)² + 10⁶` suffices.  For every `c ≥ 1`,

`(Q² + π y) c / log Q + Q + 1 ≤ (2π + ε) c y / log y`.

The factor `c` is `1` for the interval form and `q/φ(q)` for the arithmetic-progression form. -/
theorem level_bound_le_two_pi {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ Y : ℕ, 3 ≤ Y ∧ ∀ y : ℕ, Y ≤ y →
      2 ≤ ⌊Real.sqrt y / Real.log y⌋₊ ∧
      ∀ c : ℝ, 1 ≤ c →
        (((⌊Real.sqrt y / Real.log y⌋₊ : ℕ) : ℝ) ^ 2 + Real.pi * y) * c
              / Real.log ((⌊Real.sqrt y / Real.log y⌋₊ : ℕ) : ℝ)
            + ((⌊Real.sqrt y / Real.log y⌋₊ : ℕ) : ℝ) + 1
          ≤ (2 * Real.pi + eps) * c * y / Real.log y := by
  classical
  set T : ℝ := (1000 / eps) ^ 2 + 10 ^ 6 with hT
  refine ⟨max 3 ⌈Real.exp T⌉₊, le_max_left _ _, ?_⟩
  intro y hy
  -- the height is at least `exp T`, so `t = log y ≥ T`
  have hyexp : Real.exp T ≤ (y : ℝ) := by
    have h1 : ((⌈Real.exp T⌉₊ : ℕ) : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast le_trans (le_max_right 3 _) hy
    exact (Nat.le_ceil _).trans h1
  have hy0 : (0 : ℝ) < (y : ℝ) := lt_of_lt_of_le (Real.exp_pos T) hyexp
  set t : ℝ := Real.log y with htdef
  have hTt : T ≤ t := by
    have := Real.log_le_log (Real.exp_pos T) hyexp
    rwa [Real.log_exp] at this
  -- `u = √t` is large, and `eps · u ≥ 1000`
  set u : ℝ := Real.sqrt t with hudef
  have ht6 : (10 : ℝ) ^ 6 ≤ t := by
    have h0 : (0 : ℝ) ≤ (1000 / eps) ^ 2 := sq_nonneg _
    rw [hT] at hTt; linarith
  have htpos : (0 : ℝ) < t := by nlinarith
  have hu2 : u ^ 2 = t := Real.sq_sqrt htpos.le
  have hupos : (0 : ℝ) < u := Real.sqrt_pos.mpr htpos
  have hu1000 : (1000 : ℝ) ≤ u := by nlinarith [hu2, ht6, hupos]
  have hepsu : (1000 : ℝ) ≤ eps * u := by
    have hsq : (1000 / eps) ^ 2 ≤ t := by rw [hT] at hTt; nlinarith
    have hnn : (0 : ℝ) ≤ 1000 / eps := by positivity
    have hle : (1000 / eps) ≤ u := by nlinarith [hu2, hupos, hnn]
    calc (1000 : ℝ) = eps * (1000 / eps) := by field_simp
      _ ≤ eps * u := mul_le_mul_of_nonneg_left hle heps.le
  -- the sieve level `Q = ⌊√y / log y⌋`
  set s : ℝ := Real.sqrt y with hsdef
  have hs2 : s ^ 2 = (y : ℝ) := Real.sq_sqrt hy0.le
  have hspos : (0 : ℝ) < s := Real.sqrt_pos.mpr hy0
  have hlogs : Real.log s = t / 2 := by rw [hsdef, Real.log_sqrt hy0.le]
  have hs_ge : t ^ 2 / 16 ≤ s := sq_log_le_sixteen_mul_sqrt hy0 (by linarith)
  set Q : ℕ := ⌊s / t⌋₊ with hQdef
  set q : ℝ := (Q : ℝ) with hqdef
  have hst_pos : (0 : ℝ) < s / t := by positivity
  have hst_big : (62500 : ℝ) ≤ s / t := by
    rw [le_div_iff₀ htpos]
    nlinarith [hs_ge, ht6, htpos]
  have hq_le : q ≤ s / t := Nat.floor_le hst_pos.le
  have hq_ge : s / t - 1 ≤ q := by
    have h := Nat.lt_floor_add_one (s / t)
    rw [← hQdef, ← hqdef] at h
    linarith
  have hq_big : (62499 : ℝ) ≤ q := by linarith
  have hQ2 : 2 ≤ Q := by
    by_contra hcon
    push Not at hcon
    have hq1 : q ≤ 1 := by
      rw [hqdef]
      exact_mod_cast Nat.lt_succ_iff.mp (by omega : Q < 2)
    linarith
  have hqpos : (0 : ℝ) < q := by linarith
  -- `log Q ≥ t/2 − log t − 1`
  have hhalf : s / (2 * t) ≤ q := by
    have h2 : s / (2 * t) = s / t / 2 := by rw [div_div, mul_comm]
    rw [h2]; linarith
  have hhalf_pos : (0 : ℝ) < s / (2 * t) := by positivity
  have hlogq : t / 2 - Real.log t - 1 ≤ Real.log q := by
    have hmono : Real.log (s / (2 * t)) ≤ Real.log q := Real.log_le_log hhalf_pos hhalf
    have hexpand : Real.log (s / (2 * t)) = t / 2 - Real.log 2 - Real.log t := by
      rw [Real.log_div hspos.ne' (by positivity), Real.log_mul (by norm_num) htpos.ne', hlogs]
      ring
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    rw [hexpand] at hmono
    linarith
  have hlogt : Real.log t ≤ 2 * u := by
    have h := log_le_two_mul_sqrt htpos
    rwa [← hudef] at h
  have hDpos : (0 : ℝ) < Real.log q := by
    have h1 : Real.log 1 < Real.log q := Real.log_lt_log (by norm_num) (by linarith)
    simpa using h1
  have hApos : (0 : ℝ) ≤ (y : ℝ) / t := by positivity
  have hq_sq : q ^ 2 ≤ (y : ℝ) / t ^ 2 := by
    have h1 : q ^ 2 ≤ (s / t) ^ 2 := by nlinarith [hq_le, hqpos]
    have h2 : (s / t) ^ 2 = (y : ℝ) / t ^ 2 := by rw [div_pow, hs2]
    linarith [h2.symm.le, h2.le]
  have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  -- the main term
  have hpart1 : (q ^ 2 + Real.pi * y) / Real.log q ≤ (2 * Real.pi + eps / 2) * ((y : ℝ) / t) := by
    rw [div_le_iff₀ hDpos]
    have hkey : (1 : ℝ) / t + (2 * Real.pi + eps / 2) * (Real.log t + 1) ≤ eps / 4 * t := by
      have h7 : 2 * Real.pi + eps / 2 ≤ 7 := by linarith
      have h1t : (1 : ℝ) / t ≤ 1 := by rw [div_le_one htpos]; linarith
      have hnn : (0 : ℝ) ≤ Real.log t + 1 := by
        nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ t)]
      have hlt1 : (2 * Real.pi + eps / 2) * (Real.log t + 1) ≤ 7 * (2 * u + 1) :=
        mul_le_mul h7 (by linarith) hnn (by norm_num)
      have hfin : 14 * u + 8 ≤ eps / 4 * t := by
        have hid : eps / 4 * t = u / 4 * (eps * u) := by rw [← hu2]; ring
        have h1 : u / 4 * 1000 ≤ u / 4 * (eps * u) :=
          mul_le_mul_of_nonneg_left hepsu (by positivity)
        rw [hid]; linarith
      linarith
    have hkey' : (1 : ℝ) / t + Real.pi * t
        ≤ (2 * Real.pi + eps / 2) * (t / 2 - Real.log t - 1) := by
      have hexpand : (2 * Real.pi + eps / 2) * (t / 2 - Real.log t - 1)
          = Real.pi * t + eps / 4 * t - (2 * Real.pi + eps / 2) * (Real.log t + 1) := by ring
      rw [hexpand]; linarith
    have hstep2 : (y : ℝ) / t ^ 2 + Real.pi * y
        ≤ (2 * Real.pi + eps / 2) * ((y : ℝ) / t) * (t / 2 - Real.log t - 1) := by
      have hrw : (2 * Real.pi + eps / 2) * ((y : ℝ) / t) * (t / 2 - Real.log t - 1)
          = ((y : ℝ) / t) * ((2 * Real.pi + eps / 2) * (t / 2 - Real.log t - 1)) := by ring
      have hrw2 : (y : ℝ) / t ^ 2 + Real.pi * y = ((y : ℝ) / t) * (1 / t + Real.pi * t) := by
        field_simp
      rw [hrw, hrw2]
      exact mul_le_mul_of_nonneg_left hkey' hApos
    have hstep3 : (2 * Real.pi + eps / 2) * ((y : ℝ) / t) * (t / 2 - Real.log t - 1)
        ≤ (2 * Real.pi + eps / 2) * ((y : ℝ) / t) * Real.log q :=
      mul_le_mul_of_nonneg_left hlogq (by positivity)
    linarith [hq_sq, hstep2, hstep3]
  -- the primes below the sieve level
  have hpart2 : q + 1 ≤ eps / 2 * ((y : ℝ) / t) := by
    have hmul : (0 : ℝ) ≤ t * (t - 16) := mul_nonneg htpos.le (by linarith)
    have hst : t ≤ s := by linarith [hs_ge, hmul]
    have hepss : (4 : ℝ) ≤ eps * s := by
      have h2 : eps * (t ^ 2 / 16) ≤ eps * s := mul_le_mul_of_nonneg_left hs_ge heps.le
      have h3 : eps * (t ^ 2 / 16) = u ^ 3 / 16 * (eps * u) := by rw [← hu2]; ring
      have h4 : u ^ 3 / 16 * 1000 ≤ u ^ 3 / 16 * (eps * u) :=
        mul_le_mul_of_nonneg_left hepsu (by positivity)
      have hA : (1000 : ℝ) * 1000 ≤ u * u := mul_le_mul hu1000 hu1000 (by norm_num) (by linarith)
      have hB : (1000 : ℝ) * 1000 * 1000 ≤ u * u * u :=
        mul_le_mul hA hu1000 (by norm_num) (by positivity)
      have h5 : (4 : ℝ) ≤ u ^ 3 / 16 * 1000 := by linarith [hB]
      linarith
    have hnum : (0 : ℝ) ≤ eps / 2 * (y : ℝ) - s - t := by
      have h6 : s / 2 * 4 ≤ s / 2 * (eps * s) :=
        mul_le_mul_of_nonneg_left hepss (by positivity)
      have h7 : eps / 2 * (y : ℝ) = s / 2 * (eps * s) := by rw [← hs2]; ring
      linarith
    have hfrac : eps / 2 * ((y : ℝ) / t) - (s / t + 1) = (eps / 2 * (y : ℝ) - s - t) / t := by
      field_simp; ring
    have hnn : (0 : ℝ) ≤ eps / 2 * ((y : ℝ) / t) - (s / t + 1) := by
      rw [hfrac]; exact div_nonneg hnum htpos.le
    linarith [hq_le]
  refine ⟨hQ2, fun c hc => ?_⟩
  have hcnn : (0 : ℝ) ≤ c := by linarith
  have hmain : (q ^ 2 + Real.pi * y) * c / Real.log q
      ≤ (2 * Real.pi + eps / 2) * ((y : ℝ) / t) * c := by
    have hrw : (q ^ 2 + Real.pi * y) * c / Real.log q
        = ((q ^ 2 + Real.pi * y) / Real.log q) * c := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hpart1 hcnn
  have hsmall : q + 1 ≤ eps / 2 * ((y : ℝ) / t) * c := by
    have h1 : eps / 2 * ((y : ℝ) / t) * 1 ≤ eps / 2 * ((y : ℝ) / t) * c :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    linarith [hpart2]
  have hgoal : (2 * Real.pi + eps) * c * (y : ℝ) / t
      = (2 * Real.pi + eps / 2) * ((y : ℝ) / t) * c + eps / 2 * ((y : ℝ) / t) * c := by
    field_simp
    ring
  rw [hgoal]
  linarith [hmain, hsmall]

/-- **Brun–Titchmarsh with the constant `2π + o(1)`.**  For every `ε > 0` there is a threshold `Y`
such that, for every `y ≥ Y` and every starting point `x`,

`#{p prime : x ≤ p < x + y} ≤ (2π + ε) y / log y`. -/
theorem card_primes_Ico_le_two_pi_aux {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ Y : ℕ, 3 ≤ Y ∧ ∀ y : ℕ, Y ≤ y → ∀ x : ℕ,
      (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
        ≤ (2 * Real.pi + eps) * y / Real.log y := by
  obtain ⟨Y, hY3, hY⟩ := level_bound_le_two_pi heps heps1
  refine ⟨Y, hY3, fun y hy x => ?_⟩
  obtain ⟨hQ2, hbound⟩ := hY y hy
  refine (card_primes_Ico_le_of_level x y hQ2).trans ?_
  have h := hbound 1 le_rfl
  simpa using h

/-- **Brun–Titchmarsh with the constant `2π + o(1)`.**  For every `ε > 0` there is a threshold `Y`
such that, for every `y ≥ Y` and every starting point `x`,

`#{p prime : x ≤ p < x + y} ≤ (2π + ε) y / log y`. -/
theorem card_primes_Ico_le_two_pi {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∀ x : ℕ,
      (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
        ≤ (2 * Real.pi + eps) * y / Real.log y := by
  rcases le_total eps 1 with hle | hge
  · obtain ⟨Y, -, hY⟩ := card_primes_Ico_le_two_pi_aux heps hle
    exact ⟨Y, hY⟩
  · obtain ⟨Y, hY3, hY⟩ := card_primes_Ico_le_two_pi_aux (eps := 1) one_pos le_rfl
    refine ⟨Y, fun y hy x => (hY y hy x).trans ?_⟩
    have hy3 : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast le_trans hY3 hy
    have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
    have hynn : (0 : ℝ) ≤ (y : ℝ) := by linarith
    gcongr

/-! ## The arithmetic-progression form -/

/-- The progression form for `ε ≤ 1`, with `3 ≤ Y₀`. -/
theorem card_primes_Ico_mod_le_two_pi_aux {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ Y₀ : ℕ, 3 ≤ Y₀ ∧ ∀ q a : ℕ, 1 ≤ q → a < q → ∀ x y : ℕ, Y₀ ≤ y / q + 1 →
      (((Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
        ≤ (2 * Real.pi + eps) * ((q : ℝ) / (q.totient : ℝ)) * ((y / q + 1 : ℕ) : ℝ)
            / Real.log ((y / q + 1 : ℕ) : ℝ) := by
  obtain ⟨Y₀, hY3, hY⟩ := level_bound_le_two_pi heps heps1
  refine ⟨Y₀, hY3, fun q a hq ha x y hy => ?_⟩
  set n : ℕ := y / q + 1 with hn
  obtain ⟨hQ2, hbound⟩ := hY n hy
  set Q : ℕ := ⌊Real.sqrt (n : ℝ) / Real.log (n : ℝ)⌋₊ with hQ
  -- the factor `c = q/φ(q) ≥ 1`
  have hqpos : 0 < q := hq
  have hphi : 0 < q.totient := Nat.totient_pos.mpr hqpos
  have hphiR : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast hphi
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hle : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hc : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := (one_le_div hphiR).mpr hle
  have hbase := card_primes_Ico_mod_le_of_level hq ha x y (Q := Q) hQ2
  refine hbase.trans ?_
  have hrw : ((Q : ℝ) ^ 2 + Real.pi * ((y / q + 1 : ℕ) : ℝ)) * q
        / ((q.totient : ℝ) * Real.log (Q : ℝ))
      = ((Q : ℝ) ^ 2 + Real.pi * (n : ℝ)) * ((q : ℝ) / (q.totient : ℝ))
        / Real.log (Q : ℝ) := by
    rw [← hn]
    field_simp
  rw [hrw]
  exact hbound ((q : ℝ) / (q.totient : ℝ)) hc

/-- **Brun–Titchmarsh in arithmetic progressions with the constant `2π + o(1)`.**  For every
`ε > 0` there is a threshold `Y₀` such that, whenever `⌊y/q⌋ + 1 ≥ Y₀`, the number of primes of
`[x, x + y)` in any fixed residue class `a` modulo `q` is at most

`(2π + ε) (q/φ(q)) Y / log Y`,  with `Y = ⌊y/q⌋ + 1`,

uniformly in the starting point `x`, in the modulus `q` and in the residue `a`. -/
theorem card_primes_Ico_mod_le_two_pi {eps : ℝ} (heps : 0 < eps) :
    ∃ Y₀ : ℕ, ∀ q a : ℕ, 1 ≤ q → a < q → ∀ x y : ℕ, Y₀ ≤ y / q + 1 →
      (((Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
        ≤ (2 * Real.pi + eps) * ((q : ℝ) / (q.totient : ℝ)) * ((y / q + 1 : ℕ) : ℝ)
            / Real.log ((y / q + 1 : ℕ) : ℝ) := by
  rcases le_total eps 1 with hle | hge
  · obtain ⟨Y₀, -, hY⟩ := card_primes_Ico_mod_le_two_pi_aux heps hle
    exact ⟨Y₀, hY⟩
  · obtain ⟨Y₀, hY3, hY⟩ := card_primes_Ico_mod_le_two_pi_aux (eps := 1) one_pos le_rfl
    refine ⟨Y₀, fun q a hq ha x y hy => (hY q a hq ha x y hy).trans ?_⟩
    have hn3 : (3 : ℝ) ≤ ((y / q + 1 : ℕ) : ℝ) := by exact_mod_cast le_trans hY3 hy
    have hlogpos : 0 < Real.log ((y / q + 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hphi : 0 < q.totient := Nat.totient_pos.mpr hq
    have hphiR : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast hphi
    have hcnn : (0 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := by positivity
    gcongr

/-- **A Chebyshev-type upper bound with the constant `2π`**, the case `x = 0` of
`card_primes_Ico_le_two_pi`: for every `ε > 0`, `π(N) ≤ (2π + ε) N / log N` for all large `N`. -/
theorem card_primes_range_le_two_pi {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℕ, ∀ N : ℕ, Y ≤ N →
      (((range N).filter Nat.Prime).card : ℝ) ≤ (2 * Real.pi + eps) * N / Real.log N := by
  obtain ⟨Y, hY⟩ := card_primes_Ico_le_two_pi heps
  refine ⟨Y, fun N hN => ?_⟩
  have h := hY N hN 0
  rwa [Nat.zero_add, ← Finset.range_eq_Ico] at h

end BrunTitchmarsh

end RiemannHypothesis
