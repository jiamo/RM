/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange

/-!
# Conditioning: a tuple is determined by its power sums

`RiemannHypothesis/VinogradovCongruencing.lean` proves the descent half of one efficient
congruencing step — what happens to the solutions whose variables all lie in *one* residue class.
The complementary half is the *conditioning* estimate, which controls the solutions whose
residues are spread out, and its algebraic core is the following classical fact:

> over a field in which `1, 2, …, k` are invertible, a `k`-tuple is determined, up to the order
> of its entries, by its power sums of degrees `1, …, k`.

In particular, over `ZMod p` with `k < p`, two `k`-tuples solving the Vinogradov system of degree
`k` modulo `p` are rearrangements of one another.  This is the statement that bounds by `k!` the
number of solutions of the congruence system with a prescribed set of residues, and it is what
makes the well-conditioned part of the count small.

## Main results

* `RiemannHypothesis.Vinogradov.natCast_mul_esymm_eq_sum` — Newton's identities, evaluated at a
  tuple: `n · e_n(x) = (−1)^{n+1} ∑_{i + j = n, i < n} (−1)^i e_i(x) p_j(x)`.
* `RiemannHypothesis.Vinogradov.esymm_eq_of_powerSum_eq` — equal power sums up to degree `k`
  force equal elementary symmetric functions up to degree `k`.
* `RiemannHypothesis.Vinogradov.multiset_map_eq_of_powerSum_eq` — hence the two tuples have the
  same multiset of entries: `∏ (T − x_i) = ∏ (T − y_i)`, and the roots of a polynomial are its
  multiset of linear factors.
* `RiemannHypothesis.Vinogradov.multiset_map_eq_of_powerSum_eq_zmod` — the arithmetic form, over
  `ZMod p` with `k < p`: this is the conditioning input of efficient congruencing.
* `RiemannHypothesis.Vinogradov.exists_perm_of_entries_eq` — two tuples with the same multiset of
  entries differ by a permutation of the indices.
* `RiemannHypothesis.Vinogradov.card_congruenceSolutions_le_factorial` — **the conditioning
  bound**: modulo a prime `p > k`, the solutions of the Vinogradov congruence system of degree
  `k` with prescribed power sums number at most `k !`.

## Scope

The conditioning estimate is proved for one prescribed vector of power sums.  What is *not*
formalized is its interleaving with the descent of `VinogradovCongruencing.lean`: the induction
of efficient congruencing, which alternates the two and closes with a convexity argument, and
hence Vinogradov's mean value theorem, which remains only a statement.
-/

noncomputable section

open Finset Polynomial

namespace RiemannHypothesis

namespace Vinogradov

variable {F : Type*} {k : ℕ}

/-- The multiset of entries of a tuple. -/
def entries (x : Fin k → F) : Multiset F := Finset.univ.val.map x

@[simp] lemma card_entries (x : Fin k → F) : Multiset.card (entries x) = k := by
  simp [entries]

/-- **Newton's identities, evaluated at a tuple.** -/
theorem natCast_mul_esymm_eq_sum [CommRing F] (x : Fin k → F) (n : ℕ) :
    (n : F) * (entries x).esymm n
      = (-1) ^ (n + 1) * ∑ a ∈ {a ∈ Finset.antidiagonal n | a.1 < n},
          (-1) ^ a.1 * (entries x).esymm a.1 * (∑ i, x i ^ a.2) := by
  have h := congrArg (MvPolynomial.aeval x) (MvPolynomial.mul_esymm_eq_sum (Fin k) F n)
  simpa [MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, entries, map_sum,
    map_mul, map_pow] using h

/-- **Equal power sums force equal elementary symmetric functions.**  If the power sums of `x`
and `y` of degrees `1, …, k` agree, and `1, …, k` are invertible in `F`, then all the elementary
symmetric functions of degree at most `k` agree. -/
theorem esymm_eq_of_powerSum_eq [Field F] (hchar : ∀ m : ℕ, 0 < m → m ≤ k → (m : F) ≠ 0)
    (x y : Fin k → F) (h : ∀ j : ℕ, 0 < j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∀ n ≤ k, (entries x).esymm n = (entries y).esymm n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Multiset.esymm]
    · have hsum : ∑ a ∈ {a ∈ Finset.antidiagonal n | a.1 < n},
          (-1 : F) ^ a.1 * (entries x).esymm a.1 * (∑ i, x i ^ a.2)
          = ∑ a ∈ {a ∈ Finset.antidiagonal n | a.1 < n},
            (-1 : F) ^ a.1 * (entries y).esymm a.1 * (∑ i, y i ^ a.2) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
        have hadd : a.1 + a.2 = n := Finset.mem_antidiagonal.mp ha1
        have h1 : (entries x).esymm a.1 = (entries y).esymm a.1 :=
          ih a.1 ha2 (le_trans ha2.le hnk)
        have h2 : ∑ i, x i ^ a.2 = ∑ i, y i ^ a.2 := by
          refine h a.2 ?_ (by omega)
          omega
        rw [h1, h2]
      have hx := natCast_mul_esymm_eq_sum x n
      have hy := natCast_mul_esymm_eq_sum y n
      have hne : (n : F) ≠ 0 := hchar n hn hnk
      have : (n : F) * (entries x).esymm n = (n : F) * (entries y).esymm n := by
        rw [hx, hy, hsum]
      exact mul_left_cancel₀ hne this

/-- **A tuple is determined by its power sums.**  Over a field in which `1, …, k` are invertible,
two `k`-tuples with the same power sums of degrees `1, …, k` have the same multiset of
entries. -/
theorem multiset_map_eq_of_powerSum_eq [Field F] (hchar : ∀ m : ℕ, 0 < m → m ≤ k → (m : F) ≠ 0)
    (x y : Fin k → F) (h : ∀ j : ℕ, 0 < j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    entries x = entries y := by
  have hesymm := esymm_eq_of_powerSum_eq hchar x y h
  set P : F[X] := ((entries x).map fun t => Polynomial.X - Polynomial.C t).prod with hP
  set Q : F[X] := ((entries y).map fun t => Polynomial.X - Polynomial.C t).prod with hQ
  have hmonic : ∀ (s : Multiset F) (f : F[X]),
      f ∈ s.map (fun t => Polynomial.X - Polynomial.C t) → f.Monic := by
    intro s f hf
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hf
    exact monic_X_sub_C a
  have hdegsum : ∀ z : Fin k → F,
      ((Multiset.map (fun t : F => Polynomial.X - Polynomial.C t) (entries z)).map
        Polynomial.natDegree).sum = k := by
    intro z
    rw [entries, Multiset.map_map, Multiset.map_map]
    have hfun : (Polynomial.natDegree ∘ fun t : F => Polynomial.X - Polynomial.C t) ∘ z
        = fun _ : Fin k => 1 := by
      funext i
      simp
    rw [hfun]
    simp
  have hdegP : P.natDegree = k := by
    rw [hP, natDegree_multiset_prod_of_monic _ (hmonic (entries x)), hdegsum x]
  have hdegQ : Q.natDegree = k := by
    rw [hQ, natDegree_multiset_prod_of_monic _ (hmonic (entries y)), hdegsum y]
  have hPQ : P = Q := by
    refine Polynomial.ext fun j => ?_
    rcases le_or_gt j k with hj | hj
    · have hjx : j ≤ Multiset.card (entries x) := by simpa using hj
      have hjy : j ≤ Multiset.card (entries y) := by simpa using hj
      rw [hP, hQ, Multiset.prod_X_sub_C_coeff _ hjx, Multiset.prod_X_sub_C_coeff _ hjy]
      have hcard : Multiset.card (entries x) = k := card_entries x
      have hcard' : Multiset.card (entries y) = k := card_entries y
      rw [hcard, hcard', hesymm (k - j) (Nat.sub_le _ _)]
    · have h1 : P.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h2 : Q.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h1, h2]
  have hrootsP : P.roots = entries x := by
    rw [hP, Polynomial.roots_multiset_prod_X_sub_C]
  have hrootsQ : Q.roots = entries y := by
    rw [hQ, Polynomial.roots_multiset_prod_X_sub_C]
  rw [← hrootsP, ← hrootsQ, hPQ]

/-- **The conditioning input of efficient congruencing.**  Modulo a prime `p > k`, two `k`-tuples
of residues with the same power sums of degrees `1, …, k` — that is, two solutions of the
Vinogradov congruence system of degree `k` — are rearrangements of one another. -/
theorem multiset_map_eq_of_powerSum_eq_zmod {p : ℕ} [hp : Fact p.Prime] (hk : k < p)
    (x y : Fin k → ZMod p) (h : ∀ j : ℕ, 0 < j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    entries x = entries y := by
  have hchar : ∀ m : ℕ, 0 < m → m ≤ k → ((m : ZMod p) ≠ 0) := by
    intro m hm hmk
    have hmp : m < p := lt_of_le_of_lt hmk hk
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd hm hdvd
    omega
  exact multiset_map_eq_of_powerSum_eq hchar x y h

/-! ### From the algebra to the count -/

lemma entries_eq_ofFn (x : Fin k → F) : entries x = ↑(List.ofFn x) := by
  rw [entries, List.ofFn_eq_map]; rfl

lemma entries_comp_equiv (x : Fin k → F) (e : Equiv.Perm (Fin k)) :
    entries (x ∘ e) = entries x := by
  rw [entries, entries, ← Multiset.map_map, Multiset.map_univ_val_equiv]

lemma entries_succ {k : ℕ} (x : Fin (k + 1) → F) :
    entries x = x 0 ::ₘ entries (fun i : Fin k => x i.succ) := by
  rw [entries_eq_ofFn, entries_eq_ofFn, List.ofFn_succ]; rfl

lemma mem_entries (x : Fin k → F) (i : Fin k) : x i ∈ entries x := by
  rw [entries]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)

/-- **Equal multisets of entries means equal up to a permutation of the indices.** -/
theorem exists_perm_of_entries_eq :
    ∀ {k : ℕ} (x y : Fin k → F), entries x = entries y → ∃ e : Equiv.Perm (Fin k), x = y ∘ e := by
  intro k
  induction k with
  | zero => intro x y _; exact ⟨1, funext fun i => absurd i.isLt (by omega)⟩
  | succ k ih =>
    intro x y h
    have hx0 : x 0 ∈ entries y := h ▸ mem_entries x 0
    rw [entries] at hx0
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hx0
    classical
    set t : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 j with ht
    have hyt : entries (y ∘ t) = entries y := entries_comp_equiv y t
    have h0 : (y ∘ t) 0 = x 0 := by simp [ht, hj]
    have htail : entries (fun i : Fin k => x i.succ)
        = entries (fun i : Fin k => (y ∘ t) i.succ) := by
      have hcons := h.trans hyt.symm
      rw [entries_succ x, entries_succ (y ∘ t), h0] at hcons
      exact (Multiset.cons_inj_right _).mp hcons
    obtain ⟨e, he⟩ := ih _ _ htail
    refine ⟨Equiv.Perm.decomposeFin.symm (j, e), funext fun i => ?_⟩
    refine Fin.cases ?_ ?_ i
    · simp [Equiv.Perm.decomposeFin_symm_apply_zero, hj]
    · intro i
      have hi := congrFun he i
      simp only [Function.comp_apply] at hi ⊢
      rw [Equiv.Perm.decomposeFin_symm_apply_succ]
      simpa [ht] using hi

open scoped Classical in
/-- **The conditioning bound.**  Modulo a prime `p > k`, the solutions `x : Fin k → ZMod p` of the
Vinogradov congruence system with prescribed power sums `c 1, …, c k` number at most `k !`:  they
all have the same multiset of entries, hence are rearrangements of one another. -/
theorem card_congruenceSolutions_le_factorial {p : ℕ} [Fact p.Prime] (hk : k < p)
    (c : ℕ → ZMod p) :
    (Finset.univ.filter
        (fun x : Fin k → ZMod p => ∀ j : ℕ, 0 < j → j ≤ k → ∑ i, x i ^ j = c j)).card
      ≤ Nat.factorial k := by
  classical
  rcases Finset.eq_empty_or_nonempty
      (Finset.univ.filter
        (fun x : Fin k → ZMod p => ∀ j : ℕ, 0 < j → j ≤ k → ∑ i, x i ^ j = c j))
    with hempty | ⟨y, hy⟩
  · simp [hempty]
  have hyP := (Finset.mem_filter.mp hy).2
  have hsub : (Finset.univ.filter
      (fun x : Fin k → ZMod p => ∀ j : ℕ, 0 < j → j ≤ k → ∑ i, x i ^ j = c j))
      ⊆ Finset.image (fun e : Equiv.Perm (Fin k) => y ∘ ⇑e) Finset.univ := by
    intro x hx
    have hxP := (Finset.mem_filter.mp hx).2
    have hxy : entries x = entries y :=
      multiset_map_eq_of_powerSum_eq_zmod hk x y fun j hj hjk => by
        rw [hxP j hj hjk, hyP j hj hjk]
    obtain ⟨e, he⟩ := exists_perm_of_entries_eq x y hxy
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he.symm⟩
  calc (Finset.univ.filter
        (fun x : Fin k → ZMod p => ∀ j : ℕ, 0 < j → j ≤ k → ∑ i, x i ^ j = c j)).card
      ≤ (Finset.image (fun e : Equiv.Perm (Fin k) => y ∘ ⇑e) Finset.univ).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin k))).card := Finset.card_image_le
    _ = Nat.factorial k := by simp [Finset.card_univ, Fintype.card_perm]

end Vinogradov

end RiemannHypothesis
