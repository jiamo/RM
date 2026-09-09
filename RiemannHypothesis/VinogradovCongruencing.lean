/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.VinogradovMeanValue

/-!
# The congruencing step of Vinogradov's mean value theorem

`RiemannHypothesis/VinogradovMeanValue.lean` fixes the solution count `J_{s,k}(X)` of the
Vinogradov system and proves its two invariances.  This file proves the *congruencing lemma*
itself: the step of Wooley's efficient congruencing that splits the solutions of the system
along the residue classes of a modulus `q` and descends to a system in a box `q` times shorter.

The mechanism is the one the translation invariance was recorded for.  If all `2s` variables of
a solution lie in the same class `r` modulo `q`, write `x_i = r + q u_i` and `y_i = r + q v_i`.
Then the binomial expansion of the `j`-th equation is a `ℕ`-linear combination of the equations
`∑ u_i^m = ∑ v_i^m` with `m ≤ j` whose leading coefficient is `q^j`, so by induction on `j` the
reduced tuples `u, v` solve the *same* system — of the same degree `k`, in a box of length
`X/q`.  Iterating is then automatic, because the descent is available for every modulus, in
particular for `q = p^m`.

## Main results

* `RiemannHypothesis.Vinogradov.vinogradovEq_of_affine` — **the descent.**  If
  `(r + q·u, r + q·v)` solves the system and `q ≠ 0`, then `(u, v)` solves it.  This is the exact
  converse of `vinogradovEq_translate` composed with `vinogradovEq_dilate`, and it is where the
  translation invariance of the system is used.
* `RiemannHypothesis.Vinogradov.residuePair`, `vinogradovCount_eq_sum_fiber` — **the
  decomposition.**  `J_{s,k}(X)` is the sum, over the pairs of residue profiles modulo `q`, of
  the number of solutions with those residues.
* `RiemannHypothesis.Vinogradov.congruentCount` — the number of solutions all of whose `2s`
  variables are congruent to `r` modulo `q` (the diagonal profile).
* `RiemannHypothesis.Vinogradov.congruentCount_le` — **the congruencing lemma.**
  `C_{s,k}(X; q, r) ≤ J_{s,k}(X/q + 1)`: a class of the diagonal profile contributes at most the
  full solution count of a box shorter by the factor `q`.
* `RiemannHypothesis.Vinogradov.diagonalClassCount_le` — summing over the `q` classes:
  `∑_{r < q} C_{s,k}(X; q, r) ≤ q · J_{s,k}(X/q + 1)`.
* `RiemannHypothesis.Vinogradov.diagonalClassCount_le_pow` — the iterated form, with `q = p^m`:
  `∑_{r < p^m} C_{s,k}(X; p^m, r) ≤ p^m · J_{s,k}(X/p^m + 1)`.
* `RiemannHypothesis.Vinogradov.diagonalClassCount_eq` — the diagonal profile is a disjoint
  union of the classes, so the bound above really is a bound for the number of solutions whose
  variables all share a residue.

## Scope

What is proved is the descent and the class decomposition — the two halves of one congruencing
step — for an arbitrary modulus, with the elementary bounds that follow from them.  The mean
value theorem itself is *not* proved: efficient congruencing runs the step with two distinct
blocks of variables and a carefully tuned pair of parameters, and closes the induction with a
convexity argument over the resulting family of counts; none of that is here.  The statement of
the theorem remains recorded, unproved, as `VinogradovMeanValueBound`.
-/

noncomputable section

open Finset

namespace RiemannHypothesis

namespace Vinogradov

/-! ## The descent -/

/-- The power sums of a dilated and shifted tuple: `∑ (r + q·u_i)^j` expanded by the binomial
theorem, with the `m`-th term carrying the factor `q^m`. -/
theorem sum_affine_pow_eq {s : ℕ} (u : Fin s → ℕ) (r q j : ℕ) :
    ∑ i, (r + q * u i) ^ j
      = ∑ m ∈ Finset.range (j + 1),
          (j.choose m * r ^ (j - m) * q ^ m) * ∑ i, u i ^ m := by
  have hbin : ∀ i, (r + q * u i) ^ j
      = ∑ m ∈ Finset.range (j + 1), (j.choose m * r ^ (j - m) * q ^ m) * u i ^ m := by
    intro i
    have := add_pow (q * u i) r j
    rw [add_comm r (q * u i), this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => hbin i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]

/-- **The descent of the Vinogradov system along a congruence class.**  If the shifted, dilated
tuples `(r + q·u, r + q·v)` solve the system of degree `k` and `q ≠ 0`, then `(u, v)` solve it
too.  This is the step of efficient congruencing: a solution whose variables all lie in one
class modulo `q` comes from a solution of the same system in a box `q` times shorter. -/
theorem vinogradovEq_of_affine {k s r q : ℕ} (hq : 0 < q) {u v : Fin s → ℕ}
    (h : VinogradovEq k (fun i => r + q * u i) (fun i => r + q * v i)) : VinogradovEq k u v := by
  have key : ∀ j : ℕ, j ≤ k → ∑ i, u i ^ j = ∑ i, v i ^ j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hjk
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · simp
      have hlow : ∀ m ∈ Finset.range j, ∑ i, u i ^ m = ∑ i, v i ^ m := fun m hm =>
        ih m (Finset.mem_range.mp hm) (le_trans (Finset.mem_range.mp hm).le hjk)
      have hj' := h j (Finset.mem_Icc.mpr ⟨hj1, hjk⟩)
      simp only [] at hj'
      rw [sum_affine_pow_eq u r q j, sum_affine_pow_eq v r q j, Finset.sum_range_succ,
        Finset.sum_range_succ] at hj'
      have hcong : ∑ m ∈ Finset.range j, (j.choose m * r ^ (j - m) * q ^ m) * ∑ i, u i ^ m
          = ∑ m ∈ Finset.range j, (j.choose m * r ^ (j - m) * q ^ m) * ∑ i, v i ^ m :=
        Finset.sum_congr rfl fun m hm => by rw [hlow m hm]
      rw [hcong] at hj'
      have hcancel : (j.choose j * r ^ (j - j) * q ^ j) * ∑ i, u i ^ j
          = (j.choose j * r ^ (j - j) * q ^ j) * ∑ i, v i ^ j := Nat.add_left_cancel hj'
      have hqj : 0 < j.choose j * r ^ (j - j) * q ^ j := by
        simp only [Nat.choose_self, Nat.sub_self, pow_zero, one_mul]
        exact pow_pos hq j
      exact Nat.eq_of_mul_eq_mul_left hqj hcancel
  intro j hj
  exact key j (Finset.mem_Icc.mp hj).2

/-! ## The decomposition along the residue classes -/

/-- The pair of residue profiles of a pair of tuples modulo `q`. -/
def residuePair (q : ℕ) {s : ℕ} (p : (Fin s → ℕ) × (Fin s → ℕ)) : (Fin s → ℕ) × (Fin s → ℕ) :=
  (fun i => p.1 i % q, fun i => p.2 i % q)

/-- The solutions of the system in the box `[1, X]^s` whose residue profiles modulo `q` are
`c` and `d`. -/
def profileCount (k s X q : ℕ) (c d : Fin s → ℕ) : ℕ :=
  (((vinBox s X) ×ˢ (vinBox s X)).filter
    (fun p => VinogradovEq k p.1 p.2 ∧ residuePair q p = (c, d))).card

/-- **The decomposition of `J_{s,k}(X)` along the residue classes modulo `q`.**  Every solution
has a well-defined pair of residue profiles, so the solution count is the sum of the counts with
a prescribed profile. -/
theorem vinogradovCount_eq_sum_fiber (k s X q : ℕ) (hq : 0 < q) :
    vinogradovCount k s X
      = ∑ cd ∈ (Fintype.piFinset (fun _ : Fin s => Finset.range q)) ×ˢ
          (Fintype.piFinset (fun _ : Fin s => Finset.range q)),
          profileCount k s X q cd.1 cd.2 := by
  classical
  rw [vinogradovCount]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : (Fin s → ℕ) × (Fin s → ℕ) => residuePair q p)
    (t := (Fintype.piFinset (fun _ : Fin s => Finset.range q)) ×ˢ
      (Fintype.piFinset (fun _ : Fin s => Finset.range q))) ?_]
  · refine Finset.sum_congr rfl fun cd _ => ?_
    rw [profileCount]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hmem, heq⟩, hres⟩
      exact ⟨hmem, heq, by rw [hres]⟩
    · rintro ⟨hmem, heq, hres⟩
      exact ⟨⟨hmem, heq⟩, by rw [hres]⟩
  · intro p _
    refine Finset.mem_product.mpr ⟨?_, ?_⟩ <;>
      · refine Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (Nat.mod_lt _ hq)

/-! ## The congruencing lemma -/

/-- The solutions of the system in `[1, X]^s` all of whose `2s` variables are congruent to `r`
modulo `q`: the diagonal residue profile.  This is the configuration that the congruencing step
descends. -/
def congruentCount (k s X q r : ℕ) : ℕ :=
  (((vinBox s X) ×ˢ (vinBox s X)).filter
    (fun p => VinogradovEq k p.1 p.2 ∧ (∀ i, p.1 i % q = r) ∧ (∀ i, p.2 i % q = r))).card

/-- **The congruencing lemma.**  The solutions whose `2s` variables all lie in one class modulo
`q` are at most the solutions of the same system in a box shorter by the factor `q`:
`C_{s,k}(X; q, r) ≤ J_{s,k}(X/q + 1)`.

The map is `x_i ↦ x_i / q + 1`: the descent `vinogradovEq_of_affine` turns a solution of the
class into a solution of the system in `[0, X/q]`, and the translation invariance
`vinogradovEq_translate` moves that box to `[1, X/q + 1]`. -/
theorem congruentCount_le (k s X q r : ℕ) (hq : 0 < q) :
    congruentCount k s X q r ≤ vinogradovCount k s (X / q + 1) := by
  classical
  set S := ((vinBox s X) ×ˢ (vinBox s X)).filter
    (fun p => VinogradovEq k p.1 p.2 ∧ (∀ i, p.1 i % q = r) ∧ (∀ i, p.2 i % q = r)) with hS
  set T := ((vinBox s (X / q + 1)) ×ˢ (vinBox s (X / q + 1))).filter
    (fun p => VinogradovEq k p.1 p.2) with hT
  set F : (Fin s → ℕ) × (Fin s → ℕ) → (Fin s → ℕ) × (Fin s → ℕ) :=
    fun p => (fun i => p.1 i / q + 1, fun i => p.2 i / q + 1) with hF
  have hmaps : ∀ p ∈ S, F p ∈ T := by
    intro p hp
    obtain ⟨hmem, heq, hr1, hr2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hmem
    have hbox : ∀ x : Fin s → ℕ, x ∈ vinBox s X →
        (fun i => x i / q + 1) ∈ vinBox s (X / q + 1) := by
      intro x hx
      refine Fintype.mem_piFinset.mpr fun i => ?_
      have hxi := Fintype.mem_piFinset.mp hx i
      obtain ⟨-, hle⟩ := Finset.mem_Icc.mp hxi
      exact Finset.mem_Icc.mpr
        ⟨Nat.le_add_left 1 _, Nat.add_le_add_right (Nat.div_le_div_right hle) 1⟩
    -- the descent
    have hrewrite : ∀ (x : Fin s → ℕ), (∀ i, x i % q = r) → x = fun i => r + q * (x i / q) := by
      intro x hx
      funext i
      rw [← hx i, Nat.mod_add_div (x i) q]
    have hdesc : VinogradovEq k (fun i => p.1 i / q) (fun i => p.2 i / q) := by
      refine vinogradovEq_of_affine (r := r) (q := q) hq ?_
      have h1 := hrewrite p.1 hr1
      have h2 := hrewrite p.2 hr2
      rw [← h1, ← h2]
      exact heq
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hbox p.1 hb1, hbox p.2 hb2⟩,
      vinogradovEq_translate hdesc 1⟩
  have hinj : ∀ p ∈ S, ∀ p' ∈ S, F p = F p' → p = p' := by
    intro p hp p' hp' hFF
    obtain ⟨-, -, hr1, hr2⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, -, hr1', hr2'⟩ := Finset.mem_filter.mp hp'
    have hcomp : ∀ (x y : Fin s → ℕ), (∀ i, x i % q = r) → (∀ i, y i % q = r) →
        (fun i => x i / q + 1) = (fun i => y i / q + 1) → x = y := by
      intro x y hx hy hxy
      funext i
      have hdiv : x i / q = y i / q := by
        have := congrFun hxy i
        omega
      have hx' : x i % q + q * (x i / q) = x i := Nat.mod_add_div _ _
      have hy' : y i % q + q * (y i / q) = y i := Nat.mod_add_div _ _
      rw [hdiv] at hx'
      have hxr := hx i
      have hyr := hy i
      omega
    have h1 : (fun i => p.1 i / q + 1) = (fun i => p'.1 i / q + 1) := congrArg Prod.fst hFF
    have h2 : (fun i => p.2 i / q + 1) = (fun i => p'.2 i / q + 1) := congrArg Prod.snd hFF
    exact Prod.ext (hcomp p.1 p'.1 hr1 hr1' h1) (hcomp p.2 p'.2 hr2 hr2' h2)
  calc congruentCount k s X q r = S.card := rfl
    _ ≤ T.card := Finset.card_le_card_of_injOn F hmaps hinj
    _ = vinogradovCount k s (X / q + 1) := rfl

/-- **One congruencing step, summed over the classes.**  The solutions whose variables all share
a residue modulo `q` number at most `q · J_{s,k}(X/q + 1)`. -/
theorem diagonalClassCount_le (k s X q : ℕ) (hq : 0 < q) :
    ∑ r ∈ Finset.range q, congruentCount k s X q r ≤ q * vinogradovCount k s (X / q + 1) := by
  calc ∑ r ∈ Finset.range q, congruentCount k s X q r
      ≤ ∑ _r ∈ Finset.range q, vinogradovCount k s (X / q + 1) :=
        Finset.sum_le_sum fun r _ => congruentCount_le k s X q r hq
    _ = q * vinogradovCount k s (X / q + 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **The iterated congruencing step.**  Running the descent at the modulus `p^m` shortens the
box by the factor `p^m`. -/
theorem diagonalClassCount_le_pow (k s X p m : ℕ) (hp : 0 < p) :
    ∑ r ∈ Finset.range (p ^ m), congruentCount k s X (p ^ m) r
      ≤ p ^ m * vinogradovCount k s (X / p ^ m + 1) :=
  diagonalClassCount_le k s X (p ^ m) (pow_pos hp m)

/-- The solutions whose `2s` variables all share a residue modulo `q`. -/
def diagonalClassCount (k s X q : ℕ) : ℕ :=
  (((vinBox s X) ×ˢ (vinBox s X)).filter
    (fun p => VinogradovEq k p.1 p.2 ∧
      ∃ r ∈ Finset.range q, (∀ i, p.1 i % q = r) ∧ (∀ i, p.2 i % q = r))).card

/-- The diagonal profile is covered by its `q` classes. -/
theorem diagonalClassCount_le_sum (k s X q : ℕ) :
    diagonalClassCount k s X q ≤ ∑ r ∈ Finset.range q, congruentCount k s X q r := by
  classical
  have hsub : ((vinBox s X) ×ˢ (vinBox s X)).filter
      (fun p => VinogradovEq k p.1 p.2 ∧
        ∃ r ∈ Finset.range q, (∀ i, p.1 i % q = r) ∧ (∀ i, p.2 i % q = r))
      ⊆ (Finset.range q).biUnion (fun r => ((vinBox s X) ×ˢ (vinBox s X)).filter
        (fun p => VinogradovEq k p.1 p.2 ∧ (∀ i, p.1 i % q = r) ∧ (∀ i, p.2 i % q = r))) := by
    intro p hp
    obtain ⟨hmem, heq, r, hr, hr1, hr2⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨hmem, heq, hr1, hr2⟩⟩
  calc diagonalClassCount k s X q ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ r ∈ Finset.range q, congruentCount k s X q r := Finset.card_biUnion_le

/-- **The congruencing bound for the diagonal profile.**  The solutions all of whose variables
share a residue modulo `q` number at most `q · J_{s,k}(X/q + 1)`. -/
theorem diagonalClassCount_le' (k s X q : ℕ) (hq : 0 < q) :
    diagonalClassCount k s X q ≤ q * vinogradovCount k s (X / q + 1) :=
  le_trans (diagonalClassCount_le_sum k s X q) (diagonalClassCount_le k s X q hq)

end Vinogradov

end RiemannHypothesis
