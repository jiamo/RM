/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylPolynomial

/-!
# Weyl's equidistribution theorem: the exact criterion

`RiemannHypothesis.WeylPolynomial` proves one half of Weyl's theorem: the values `p(n)` of a real
polynomial are equidistributed modulo one as soon as the *leading* coefficient is irrational.
This file removes that restriction and proves the exact criterion:

> `n ↦ p(n)` is equidistributed modulo one **iff** some coefficient `p.coeff j` with `j ≥ 1`
> is irrational.

## Main results

* `equidistributedMod1_of_residue_classes` — a sequence all of whose arithmetic subsequences
  `k ↦ x (v k + r)`, `r < v`, are equidistributed is itself equidistributed.
* `equidistributedMod1_of_sub_int` — equidistribution only depends on the sequence modulo one.
* `equidistributedMod1_polyEval_of_exists_irrational` — the substantial direction.
* `not_equidistributedMod1_polyEval_of_forall_rat` — the converse.
* `equidistributedMod1_polyEval_iff` — **Weyl's criterion for polynomial sequences**.

## Proof

The converse is a computation: if every coefficient of index `≥ 1` is rational with common
denominator `L` then `L · p(n)` is congruent to `L · p(0)` modulo one, so the Weyl sum at
frequency `L` has modulus `N`.

The forward direction is a strong induction on `deg p`.  If the leading coefficient is irrational
we are done by `equidistributedMod1_polyEval`.  Otherwise the leading coefficient is a rational
`u/v`, and along the arithmetic progression `n = v m + r` the term `(u/v) n^d` is congruent
modulo one to the constant `(u/v) r^d`, because `v ∣ (v m + r)^d − r^d`.  What is left is a
polynomial in `m` of strictly smaller degree, namely `(taylor r (eraseLead p)).comp (C v · X)`,
and the coefficient of index `j₀` of `taylor r (eraseLead p)` is `p.coeff j₀` plus a rational
number, where `j₀` is the largest index carrying an irrational coefficient.  The induction
hypothesis applies, and `equidistributedMod1_of_residue_classes` glues the progressions together.
-/

noncomputable section

open Complex Filter Finset Topology Polynomial

namespace RiemannHypothesis

namespace WeylPolynomial

open WeylCriterion WeylCount KusminLandau

/-! ### The rational numbers as a subfield of `ℝ` -/

/-- The image of `ℚ` in `ℝ`, as a subfield.  Its complement is the set of irrational numbers. -/
def ratSubfield : Subfield ℝ := (Rat.castHom ℝ).fieldRange

theorem mem_ratSubfield_iff (x : ℝ) : x ∈ ratSubfield ↔ ¬ Irrational x := by
  simp [ratSubfield, Irrational, RingHom.mem_fieldRange, eq_comm]

theorem not_mem_ratSubfield_iff (x : ℝ) : x ∉ ratSubfield ↔ Irrational x := by
  simp [mem_ratSubfield_iff]

theorem ratCast_mem_ratSubfield (q : ℚ) : (q : ℝ) ∈ ratSubfield := ⟨q, rfl⟩

theorem natCast_mem_ratSubfield (n : ℕ) : (n : ℝ) ∈ ratSubfield := ⟨(n : ℚ), by simp⟩

theorem intCast_mem_ratSubfield (n : ℤ) : (n : ℝ) ∈ ratSubfield := ⟨(n : ℚ), by simp⟩

theorem irrational_add_of_mem {a b : ℝ} (ha : Irrational a) (hb : b ∈ ratSubfield) :
    Irrational (a + b) := by
  rw [← not_mem_ratSubfield_iff] at ha ⊢
  exact fun hab => ha (by simpa using ratSubfield.sub_mem hab hb)

theorem irrational_mul_of_mem {a b : ℝ} (ha : Irrational a) (hb : b ∈ ratSubfield)
    (hb0 : b ≠ 0) : Irrational (a * b) := by
  rw [← not_mem_ratSubfield_iff] at ha ⊢
  exact fun hab => ha (by simpa [hb0] using ratSubfield.mul_mem hab (ratSubfield.inv_mem hb))

/-! ### Two stability properties of equidistribution -/

/-- Equidistribution modulo one only sees the sequence modulo one. -/
theorem equidistributedMod1_of_sub_int {x y : ℕ → ℝ} (h : ∀ n, ∃ k : ℤ, x n = y n + k)
    (hy : EquidistributedMod1 y) : EquidistributedMod1 x := by
  refine equidistributedMod1_of_weylSumsVanish fun m hm => ?_
  refine (weylSumsVanish_of_equidistributedMod1 hy m hm).congr fun N => ?_
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  obtain ⟨k, hk⟩ := h n
  have hrw : (m : ℝ) * y n = (m : ℝ) * x n - ((m * k : ℤ) : ℝ) := by
    rw [hk]; push_cast; ring
  rw [hrw, e2pi_sub_int]

/-- The number of `k` with `v k + r < N`. -/
def blockCount (v r N : ℕ) : ℕ := (N - r + (v - 1)) / v

theorem lt_blockCount_iff {v r N k : ℕ} (hv : 0 < v) :
    k < blockCount v r N ↔ v * k + r < N := by
  rw [blockCount, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hv,
    show (k + 1) * v = v * k + v by ring]
  generalize v * k = t
  omega

theorem blockCount_le {v r N : ℕ} (hv : 0 < v) : blockCount v r N ≤ N := by
  by_contra hcon
  rw [not_le] at hcon
  have hpos : 0 < blockCount v r N := lt_of_le_of_lt (Nat.zero_le N) hcon
  have h1 : v * (blockCount v r N - 1) + r < N :=
    (lt_blockCount_iff hv).1 (by omega)
  have h2 : blockCount v r N - 1 ≤ v * (blockCount v r N - 1) :=
    Nat.le_mul_of_pos_left _ hv
  omega

theorem tendsto_blockCount_atTop {v r : ℕ} (hv : 0 < v) :
    Tendsto (fun N => blockCount v r N) atTop atTop := by
  refine tendsto_atTop.2 fun K => eventually_atTop.2 ⟨v * K + r + 1, fun N hN => ?_⟩
  exact le_of_lt ((lt_blockCount_iff hv).2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hN))

theorem sum_range_eq_sum_residues {M : Type*} [AddCommMonoid M] (f : ℕ → M) {v : ℕ} (hv : 0 < v)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, f n
      = ∑ r ∈ Finset.range v, ∑ k ∈ Finset.range (blockCount v r N), f (v * k + r) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % v) (t := Finset.range v)
    (fun i _ => Finset.mem_range.2 (Nat.mod_lt _ hv)) f]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrv : r < v := Finset.mem_range.1 hr
  refine Finset.sum_nbij' (fun n => n / v) (fun k => v * k + r) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    refine Finset.mem_range.2 ((lt_blockCount_iff hv).2 ?_)
    rw [← hn.2, Nat.div_add_mod]
    exact hn.1
  · intro k hk
    have hk' := (lt_blockCount_iff (r := r) hv).1 (Finset.mem_range.1 hk)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hk', by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hrv⟩
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rw [← hn.2, Nat.div_add_mod]
  · intro k _
    rw [Nat.mul_add_div hv, Nat.div_eq_of_lt hrv, add_zero]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rw [← hn.2, Nat.div_add_mod]

/-- If every arithmetic progression `k ↦ x (v k + r)` is equidistributed modulo one, so is `x`. -/
theorem equidistributedMod1_of_residue_classes {x : ℕ → ℝ} {v : ℕ} (hv : 0 < v)
    (h : ∀ r < v, EquidistributedMod1 fun k => x (v * k + r)) : EquidistributedMod1 x := by
  refine equidistributedMod1_of_weylSumsVanish fun m hm => ?_
  set G : ℕ → ℕ → ℝ := fun r K =>
    ‖∑ k ∈ Finset.range K, e2pi ((m : ℝ) * x (v * k + r))‖ / K with hGdef
  set F : ℕ → ℕ → ℝ := fun r N => G r (blockCount v r N) with hFdef
  have hG : ∀ r < v, Tendsto (G r) atTop (𝓝 0) := fun r hr =>
    weylSumsVanish_of_equidistributedMod1 (h r hr) m hm
  have hFtend : ∀ r < v, Tendsto (F r) atTop (𝓝 0) := fun r hr =>
    (hG r hr).comp (tendsto_blockCount_atTop hv)
  have hsum : Tendsto (fun N => ∑ r ∈ Finset.range v, F r N) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range v)
      (fun r hr => hFtend r (Finset.mem_range.1 hr))
    simpa using this
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hsum
  have hsplit := sum_range_eq_sum_residues (fun n => e2pi ((m : ℝ) * x n)) hv N
  have hnorm : ‖∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n)‖
      ≤ ∑ r ∈ Finset.range v, ‖∑ k ∈ Finset.range (blockCount v r N),
          e2pi ((m : ℝ) * x (v * k + r))‖ := by
    rw [hsplit]; exact norm_sum_le _ _
  have hstep : ∀ r ∈ Finset.range v,
      ‖∑ k ∈ Finset.range (blockCount v r N), e2pi ((m : ℝ) * x (v * k + r))‖ / N ≤ F r N := by
    intro r _
    rcases Nat.eq_zero_or_pos (blockCount v r N) with hc | hc
    · simp [hFdef, hGdef, hc]
    · have hcN : (blockCount v r N : ℝ) ≤ N := by exact_mod_cast blockCount_le (r := r) hv
      have hc' : (0 : ℝ) < blockCount v r N := by exact_mod_cast hc
      simp only [hFdef, hGdef]
      gcongr
  calc ‖∑ n ∈ Finset.range N, e2pi ((m : ℝ) * x n)‖ / N
      ≤ (∑ r ∈ Finset.range v, ‖∑ k ∈ Finset.range (blockCount v r N),
            e2pi ((m : ℝ) * x (v * k + r))‖) / N := by
        gcongr
    _ = ∑ r ∈ Finset.range v, ‖∑ k ∈ Finset.range (blockCount v r N),
            e2pi ((m : ℝ) * x (v * k + r))‖ / N := by rw [Finset.sum_div]
    _ ≤ ∑ r ∈ Finset.range v, F r N := Finset.sum_le_sum hstep

/-! ### Coefficients of the shifted and dilated polynomial -/

/-- If all coefficients of `g` above `j` are rational, then the `j`-th Taylor coefficient of `g`
at a rational point is irrational exactly when `g.coeff j` is. -/
theorem irrational_taylor_coeff {g : ℝ[X]} {j : ℕ} (hirr : Irrational (g.coeff j))
    (hgt : ∀ k, j < k → g.coeff k ∈ ratSubfield) {r : ℝ} (hr : r ∈ ratSubfield) :
    Irrational ((Polynomial.taylor r g).coeff j) := by
  rw [taylor_coeff, eval_eq_sum_range, Finset.sum_range_succ']
  have h0 : (hasseDeriv j g).coeff 0 * r ^ 0 = g.coeff j := by
    rw [hasseDeriv_coeff]; simp
  rw [h0, add_comm]
  refine irrational_add_of_mem hirr (sum_mem fun i _ => ?_)
  rw [hasseDeriv_coeff]
  exact ratSubfield.mul_mem
    (ratSubfield.mul_mem (natCast_mem_ratSubfield _) (hgt _ (by omega))) (pow_mem hr _)

/-! ### The forward direction -/

theorem equidistributedMod1_polyEval_aux' :
    ∀ D : ℕ, ∀ p : ℝ[X], p.natDegree ≤ D → (∃ j, 1 ≤ j ∧ Irrational (p.coeff j)) →
      EquidistributedMod1 fun n : ℕ => p.eval (n : ℝ) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D IH =>
  classical
  rintro p hpD ⟨j, hj1, hjirr⟩
  have hjle : j ≤ p.natDegree := le_natDegree_of_ne_zero hjirr.ne_zero
  have hD1 : 1 ≤ p.natDegree := le_trans hj1 hjle
  by_cases htop : Irrational (p.coeff p.natDegree)
  · exact equidistributedMod1_polyEval hD1 htop
  -- the leading coefficient is a rational `q`; split into residue classes modulo its denominator
  set j₀ := Nat.findGreatest (fun k => 1 ≤ k ∧ Irrational (p.coeff k)) p.natDegree with hj₀def
  have hj₀P : 1 ≤ j₀ ∧ Irrational (p.coeff j₀) :=
    Nat.findGreatest_spec (P := fun k => 1 ≤ k ∧ Irrational (p.coeff k)) (m := j) hjle
      ⟨hj1, hjirr⟩
  have habove : ∀ k, j₀ < k → p.coeff k ∈ ratSubfield := by
    intro k hk
    rcases le_or_gt k p.natDegree with hkd | hkd
    · rw [mem_ratSubfield_iff]
      exact fun hirr => Nat.findGreatest_is_greatest hk hkd ⟨by omega, hirr⟩
    · rw [coeff_eq_zero_of_natDegree_lt hkd]; exact ratSubfield.zero_mem
  have hj₀ne : j₀ ≠ p.natDegree := by
    intro h; exact htop (h ▸ hj₀P.2)
  obtain ⟨q, hq⟩ : ∃ q : ℚ, (q : ℝ) = p.coeff p.natDegree :=
    (mem_ratSubfield_iff _).2 htop
  set v : ℕ := q.den with hvdef
  have hv : 0 < v := q.pos
  set g : ℝ[X] := p.eraseLead with hgdef
  have hgcoeff : ∀ k, j₀ < k → g.coeff k ∈ ratSubfield := by
    intro k hk
    by_cases hkd : k = p.natDegree
    · rw [hgdef, hkd, eraseLead_coeff, if_pos rfl]; exact ratSubfield.zero_mem
    · rw [hgdef, eraseLead_coeff_of_ne k hkd]; exact habove k hk
  have hgj₀ : Irrational (g.coeff j₀) := by
    rw [hgdef, eraseLead_coeff_of_ne j₀ hj₀ne]; exact hj₀P.2
  have hgdeg : g.natDegree ≤ p.natDegree - 1 := eraseLead_natDegree_le p
  have hgp : ∀ x : ℝ, p.eval x = g.eval x + p.coeff p.natDegree * x ^ p.natDegree := by
    intro x
    have hx := congrArg (fun f : ℝ[X] => f.eval x) (eraseLead_add_C_mul_X_pow p)
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, leadingCoeff] at hx
    rw [hgdef]
    exact hx.symm
  refine equidistributedMod1_of_residue_classes hv fun r hr => ?_
  -- the auxiliary polynomial in the progression variable
  set h : ℝ[X] :=
    C (p.coeff p.natDegree * (r : ℝ) ^ p.natDegree)
      + (Polynomial.taylor (r : ℝ) g).comp (C (v : ℝ) * X) with hhdef
  have hCvX : (C (v : ℝ) * X).natDegree = 1 := by
    rw [natDegree_C_mul_X]
    exact_mod_cast hv.ne'
  have hhdeg : h.natDegree ≤ p.natDegree - 1 := by
    refine le_trans (natDegree_add_le _ _)
      (max_le (le_trans (le_of_eq (natDegree_C _)) (Nat.zero_le _)) ?_)
    refine le_trans natDegree_comp_le ?_
    rw [natDegree_taylor, hCvX, mul_one]
    exact hgdeg
  have hheval : ∀ k : ℕ, h.eval (k : ℝ)
      = p.coeff p.natDegree * (r : ℝ) ^ p.natDegree + g.eval ((v : ℝ) * k + r) := by
    intro k
    rw [hhdef]
    simp [eval_comp, taylor_eval, mul_comm]
  -- the sequence along the progression differs from `h` by an integer
  have hint : ∀ k : ℕ, ∃ z : ℤ, p.eval (((v * k + r : ℕ) : ℝ)) = h.eval (k : ℝ) + z := by
    intro k
    have hBA : r ^ p.natDegree ≤ (v * k + r) ^ p.natDegree :=
      Nat.pow_le_pow_left (by omega) _
    have hdvd : v ∣ (v * k + r) ^ p.natDegree - r ^ p.natDegree := by
      refine (Nat.modEq_iff_dvd' hBA).1 ?_
      have hmod : (v * k + r) ≡ r [MOD v] := by simp [Nat.ModEq]
      exact (hmod.pow p.natDegree).symm
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨q.num * t, ?_⟩
    have hcast : (((v * k + r : ℕ) : ℝ)) = (v : ℝ) * k + r := by push_cast; ring
    have hdiff : (((v * k + r : ℕ) : ℝ)) ^ p.natDegree - (r : ℝ) ^ p.natDegree
        = (v : ℝ) * t := by
      have := congrArg (fun n : ℕ => (n : ℝ)) ht
      push_cast [Nat.cast_sub hBA] at this ⊢
      linarith [this]
    have hqnum : (q : ℝ) * ((v : ℝ) * t) = ((q.num * t : ℤ) : ℝ) := by
      have hden : (q : ℝ) * (v : ℝ) = ((q.num : ℤ) : ℝ) := by
        rw [hvdef, show ((q : ℝ) * (q.den : ℝ)) = (((q * q.den : ℚ)) : ℝ) by push_cast; ring]
        exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) (Rat.mul_den_eq_num q)
      rw [← mul_assoc, hden]; push_cast; ring
    rw [hgp, hheval k, ← hcast, ← hq]
    have : (q : ℝ) * (((v * k + r : ℕ) : ℝ)) ^ p.natDegree
        = (q : ℝ) * (r : ℝ) ^ p.natDegree + ((q.num * t : ℤ) : ℝ) := by
      rw [← hqnum, ← hdiff]; ring
    rw [this, hcast]
    ring
  refine equidistributedMod1_of_sub_int hint ?_
  -- the induction hypothesis applies to `h`
  refine IH (p.natDegree - 1) (by omega) h hhdeg ⟨j₀, hj₀P.1, ?_⟩
  have hcoeff : h.coeff j₀ = (Polynomial.taylor (r : ℝ) g).coeff j₀ * (v : ℝ) ^ j₀ := by
    rw [hhdef, coeff_add, coeff_C, if_neg (by omega), zero_add, comp_C_mul_X_coeff]
  rw [hcoeff]
  refine irrational_mul_of_mem
    (irrational_taylor_coeff hgj₀ hgcoeff (natCast_mem_ratSubfield r))
    (pow_mem (natCast_mem_ratSubfield v) j₀) (pow_ne_zero _ ?_)
  exact_mod_cast hv.ne'

/-- **Weyl's theorem**, forward direction: a polynomial with an irrational coefficient of positive
index takes equidistributed values modulo one. -/
theorem equidistributedMod1_polyEval_of_exists_irrational {p : ℝ[X]} {j : ℕ} (hj : 1 ≤ j)
    (hirr : Irrational (p.coeff j)) : EquidistributedMod1 fun n : ℕ => p.eval (n : ℝ) :=
  equidistributedMod1_polyEval_aux' p.natDegree p le_rfl ⟨j, hj, hirr⟩

/-! ### The converse -/

/-- Multiplying a rational by a multiple of its denominator gives an integer. -/
theorem exists_int_mul_of_den_dvd (q : ℚ) {L : ℕ} (hd : q.den ∣ L) :
    ∃ z : ℤ, (L : ℝ) * (q : ℝ) = z := by
  obtain ⟨c, hc⟩ := hd
  refine ⟨c * q.num, ?_⟩
  have hnum : (q.den : ℚ) * q = (q.num : ℚ) := by
    rw [mul_comm]; exact_mod_cast Rat.mul_den_eq_num q
  have hQ : (L : ℚ) * q = (c : ℚ) * q.num := by
    rw [hc]
    push_cast
    calc ((q.den : ℚ) * c) * q = c * ((q.den : ℚ) * q) := by ring
      _ = c * q.num := by rw [hnum]
  exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) hQ

/-- A common denominator for the coefficients of positive index. -/
theorem exists_common_denom {p : ℝ[X]} (h : ∀ j, 1 ≤ j → p.coeff j ∈ ratSubfield) :
    ∃ L : ℕ, 0 < L ∧ ∀ j, 1 ≤ j → ∃ z : ℤ, (L : ℝ) * p.coeff j = z := by
  classical
  have h' : ∀ j : ℕ, ∃ q : ℚ, 1 ≤ j → (q : ℝ) = p.coeff j := by
    intro j
    by_cases hj : 1 ≤ j
    · obtain ⟨q, hq⟩ := h j hj
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun hj' => absurd hj' hj⟩
  choose qf hqf using h'
  refine ⟨∏ j ∈ Finset.range (p.natDegree + 1), (qf j).den, Finset.prod_pos fun j _ => (qf j).pos,
    fun j hj => ?_⟩
  rcases le_or_gt j p.natDegree with hjd | hjd
  · have hdvd : (qf j).den ∣ ∏ i ∈ Finset.range (p.natDegree + 1), (qf i).den :=
      Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))
    obtain ⟨z, hz⟩ := exists_int_mul_of_den_dvd (qf j) hdvd
    exact ⟨z, by rw [← hqf j hj]; exact hz⟩
  · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt hjd]; simp⟩

/-- If every coefficient of positive index is rational, the values of `p` are *not*
equidistributed modulo one: modulo one they are periodic, hence take finitely many values. -/
theorem not_equidistributedMod1_polyEval_of_forall_rat {p : ℝ[X]}
    (h : ∀ j, 1 ≤ j → ¬ Irrational (p.coeff j)) :
    ¬ EquidistributedMod1 fun n : ℕ => p.eval (n : ℝ) := by
  classical
  intro heq
  obtain ⟨L, hL, hLz⟩ :=
    exists_common_denom (p := p) fun j hj => (mem_ratSubfield_iff _).2 (h j hj)
  choose zf hzf using fun i : ℕ => hLz (i + 1) (by omega)
  have hev0 : p.eval (0 : ℝ) = p.coeff 0 := (coeff_zero_eq_eval_zero p).symm
  have key : ∀ n : ℕ, ∃ z : ℤ,
      (L : ℝ) * p.eval ((n : ℕ) : ℝ) = (L : ℝ) * p.eval (0 : ℝ) + z := by
    intro n
    have hev : p.eval ((n : ℕ) : ℝ)
        = (∑ i ∈ Finset.range p.natDegree, p.coeff (i + 1) * (n : ℝ) ^ (i + 1))
          + p.coeff 0 := by
      rw [eval_eq_sum_range, Finset.sum_range_succ']
      simp
    have hterms : ∀ i ∈ Finset.range p.natDegree,
        (L : ℝ) * (p.coeff (i + 1) * (n : ℝ) ^ (i + 1)) = (zf i : ℝ) * (n : ℝ) ^ (i + 1) := by
      intro i _
      rw [← mul_assoc, hzf i]
    refine ⟨∑ i ∈ Finset.range p.natDegree, zf i * (n : ℤ) ^ (i + 1), ?_⟩
    calc (L : ℝ) * p.eval ((n : ℕ) : ℝ)
        = (∑ i ∈ Finset.range p.natDegree, (L : ℝ) * (p.coeff (i + 1) * (n : ℝ) ^ (i + 1)))
            + (L : ℝ) * p.coeff 0 := by rw [hev, mul_add, Finset.mul_sum]
      _ = (∑ i ∈ Finset.range p.natDegree, (zf i : ℝ) * (n : ℝ) ^ (i + 1))
            + (L : ℝ) * p.coeff 0 := by rw [Finset.sum_congr rfl hterms]
      _ = (L : ℝ) * p.eval (0 : ℝ)
            + ((∑ i ∈ Finset.range p.natDegree, zf i * (n : ℤ) ^ (i + 1) : ℤ) : ℝ) := by
          rw [hev0]; push_cast; ring
  have hW := weylSumsVanish_of_equidistributedMod1 heq (L : ℤ) (by exact_mod_cast hL.ne')
  have hterm : ∀ n : ℕ,
      e2pi (((L : ℤ) : ℝ) * p.eval ((n : ℕ) : ℝ)) = e2pi ((L : ℝ) * p.eval (0 : ℝ)) := by
    intro n
    obtain ⟨z, hz⟩ := key n
    have hz' : ((L : ℤ) : ℝ) * p.eval ((n : ℕ) : ℝ)
        = (L : ℝ) * p.eval (0 : ℝ) - ((-z : ℤ) : ℝ) := by
      push_cast at hz ⊢
      linarith
    rw [hz', e2pi_sub_int]
  have hone : Tendsto
      (fun N : ℕ => ‖∑ n ∈ Finset.range N, e2pi (((L : ℤ) : ℝ) * p.eval ((n : ℕ) : ℝ))‖ / N)
      atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ)))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    rw [Finset.sum_congr rfl fun n _ => hterm n, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, norm_mul, norm_e2pi, mul_one, Complex.norm_natCast]
    field_simp
  have hcontra := tendsto_nhds_unique hW hone
  norm_num at hcontra

/-- **Weyl's criterion for polynomial sequences.**  The values `p(n)` of a real polynomial are
equidistributed modulo one if and only if some coefficient of positive index is irrational. -/
theorem equidistributedMod1_polyEval_iff (p : ℝ[X]) :
    (EquidistributedMod1 fun n : ℕ => p.eval (n : ℝ)) ↔ ∃ j, 1 ≤ j ∧ Irrational (p.coeff j) := by
  refine ⟨fun hp => ?_,
    fun ⟨j, hj, hirr⟩ => equidistributedMod1_polyEval_of_exists_irrational hj hirr⟩
  by_contra hcon
  exact not_equidistributedMod1_polyEval_of_forall_rat
    (fun j hj hirr => hcon ⟨j, hj, hirr⟩) hp

end WeylPolynomial

end RiemannHypothesis
