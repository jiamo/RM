/-
Host-compatibility backports for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb), Siegel-zero closure
(`OAI.NumberTheory.SiegelZeros.Main`).

The absorbed modules use the following names, which exist at the upstream Mathlib pin
d13f23b723b8a846827a245b89c10fc7d3f11612 but not at this repository's Mathlib pin db584cd6.
Each is proved here from host material:

* `logDeriv_fun_mul` — the host's `logDeriv_mul` (same statement, the `fun z => f z * g z`
  form; upstream renamed it);
* `Finset.prod_lt_prod_of_nonempty₀` — the host's `Finset.prod_lt_prod_of_nonempty`;
* `Polynomial.preHilbertPoly_eq_choose_add_sub` — the evaluation of `preHilbertPoly` under the
  weaker hypothesis `k ≤ n + d` (the host's `preHilbertPoly_eq_choose_sub_add` needs `k ≤ n`;
  for `n < k ≤ n + d` both sides vanish);
* `Ideal.under_lt_under_of_integral_mem_sdiff` — the host's
  `Ideal.comap_lt_comap_of_integral_mem_sdiff`, stated with `Ideal.under`;
* `Ideal.IsIntegral.under_lt_under` — the host's `Ideal.IsIntegral.comap_lt_comap`, stated with
  `Ideal.under`;
* `IsPrimitiveRoot.pow_div_gcd` — `ζ ^ p` is a primitive `k / gcd k p`-th root of unity;
* `IntermediateField.adjoin_simple_mul_algebraMap` — `F⟮x * r⟯ = F⟮x⟯` for a non-zero scalar `r`;
* `Submodule.isCompl_map` — complements are preserved by mapping along a linear equivalence;
* `Ideal.height_span_le_card_of_span_ne_top` — Krull's height theorem for a proper ideal spanned
  by a finite set, from the host's `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`;
* `Derivation.sum_apply` — a finite sum of derivations is applied termwise;
* `logDeriv_fun_comp` — the host's `logDeriv_comp`, in the `fun y => f (g y)` form;
* `Int.sq_emod_four` (`x ^ 2 % 4 = x % 2`) and `Int.squarefree_iff_prime_sq_not_dvd`;
* `Int.IsFundamentalDiscr` — the predicate "`d` is a fundamental discriminant": `d ≡ 1 mod 4` and
  `d` squarefree, or `d = 4m` with `m` squarefree and `m ≡ 2, 3 mod 4` (the classical definition;
  `1` counts, as for the trivial character).  The definition is not present at the host pin, so it
  is stated here; the absorbed modules use it only through `Int.isFundamentalDiscr_iff_squarefree`,
  `Int.isFundamentalDiscr_four_mul` and `Int.IsFundamentalDiscr.emod_four_eq_zero_or_one`, and
  carry it as a conjunct of intermediate statements.  It does not occur in the public theorems.

Proof status: NEWLY PROVED FOR COMPATIBILITY.
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Order.Hom.Lattice
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Derivation.Basic

/-- Upstream name of the host's `logDeriv_mul`. -/
theorem logDeriv_fun_mul {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {f g : 𝕜 → 𝕜'} (x : 𝕜)
    (hf : f x ≠ 0) (hg : g x ≠ 0) (hdf : DifferentiableAt 𝕜 f x)
    (hdg : DifferentiableAt 𝕜 g x) :
    logDeriv (fun z => f z * g z) x = logDeriv f x + logDeriv g x :=
  logDeriv_mul x hf hg hdf hdg

namespace Finset

variable {ι R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]
  [PosMulStrictMono R] [Nontrivial R] {s : Finset ι} {f g : ι → R}

/-- Upstream name of the host's `Finset.prod_lt_prod_of_nonempty`. -/
lemma prod_lt_prod_of_nonempty₀ (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i < g i)
    (h_ne : s.Nonempty) : ∏ i ∈ s, f i < ∏ i ∈ s, g i :=
  prod_lt_prod_of_nonempty hf hfg h_ne

end Finset

namespace Polynomial

/-- `preHilbertPoly F d k` evaluated at `n` is `(n + d - k).choose d` whenever `k ≤ n + d`. -/
lemma preHilbertPoly_eq_choose_add_sub (F : Type*) [Field F] [CharZero F] (d : ℕ) {k n : ℕ}
    (hkn : k ≤ n + d) :
    (preHilbertPoly F d k).eval (n : F) = (n + d - k).choose d := by
  rcases le_or_gt k n with h | h
  · rw [preHilbertPoly_eq_choose_sub_add F d h]
    congr 2
    omega
  · have hz : (n + d - k).choose d = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz]
    simp only [preHilbertPoly, eval_smul, eval_comp, eval_add, eval_sub, eval_X, eval_C,
      eval_one, smul_eq_mul, Nat.cast_zero]
    have : ((n : F) - k + 1) = -((k - n - 1 : ℕ) : F) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [this, ascPochhammer_eval_neg_coe_nat_of_lt (by omega), mul_zero]

end Polynomial

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {I J : Ideal S}

/-- Upstream name of the host's `Ideal.comap_lt_comap_of_integral_mem_sdiff`. -/
theorem under_lt_under_of_integral_mem_sdiff [I.IsPrime] (hIJ : I ≤ J) {x : S}
    (mem : x ∈ (J : Set S) \ I) (integral : IsIntegral R x) :
    I.under R < J.under R :=
  comap_lt_comap_of_integral_mem_sdiff hIJ mem integral

end Ideal

namespace Ideal.IsIntegral

/-- Upstream name of the host's `Ideal.IsIntegral.comap_lt_comap`. -/
theorem under_lt_under {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] {I J : Ideal A} [I.IsPrime] (h : I < J) :
    I.under R < J.under R :=
  Ideal.IsIntegral.comap_lt_comap h

end Ideal.IsIntegral

/-- `ζ ^ p` is a primitive `k / gcd k p`-th root of unity. -/
theorem IsPrimitiveRoot.pow_div_gcd {M : Type*} [CommMonoid M] {ζ : M} {k : ℕ}
    (h : IsPrimitiveRoot ζ k) (p : ℕ) (hp : k.gcd p ≠ 0) :
    IsPrimitiveRoot (ζ ^ p) (k / k.gcd p) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · have hk : k ≠ 0 := by simpa using hp
    simp [Nat.div_self (Nat.pos_of_ne_zero hk)]
  · rw [h.eq_orderOf, ← orderOf_pow' ζ hp0.ne']
    exact IsPrimitiveRoot.orderOf _

open IntermediateField in
/-- Adjoining `x * r` for a non-zero scalar `r` is the same as adjoining `x`. -/
theorem IntermediateField.adjoin_simple_mul_algebraMap {F E : Type*} [Field F] [Field E]
    [Algebra F E] (x : E) (r : F) (hr : r ≠ 0) :
    F⟮x * algebraMap F E r⟯ = F⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact mul_mem (IntermediateField.mem_adjoin_simple_self F x)
      (IntermediateField.algebraMap_mem _ r)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h : x * algebraMap F E r * algebraMap F E r⁻¹ = x := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, mul_one]
    have hm : x * algebraMap F E r * algebraMap F E r⁻¹ ∈ F⟮x * algebraMap F E r⟯ :=
      mul_mem (IntermediateField.mem_adjoin_simple_self F _)
        (IntermediateField.algebraMap_mem _ _)
    rwa [h] at hm

/-- Upstream name of the host's `logDeriv_comp`, in the `fun y => f (g y)` form. -/
theorem logDeriv_fun_comp {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {f : 𝕜' → 𝕜'} {g : 𝕜 → 𝕜'} {x : 𝕜}
    (hf : DifferentiableAt 𝕜' f (g x)) (hg : DifferentiableAt 𝕜 g x) :
    logDeriv (fun y => f (g y)) x = logDeriv f (g x) * deriv g x :=
  logDeriv_comp hf hg

namespace Int

theorem sq_emod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · obtain ⟨k, rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero h
    rw [h]
    ring_nf
    omega
  · have : x = 2 * (x / 2) + 1 := by omega
    rw [h, this]
    ring_nf
    omega

theorem squarefree_iff_prime_sq_not_dvd {n : ℤ} :
    Squarefree n ↔ ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ^ 2 ∣ n) := by
  rw [← Int.squarefree_natAbs, Nat.squarefree_iff_prime_squarefree]
  refine forall_congr' fun p => imp_congr_right fun _ => not_congr ?_
  rw [← Int.natCast_dvd, sq]
  simp

/-- `d` is a fundamental discriminant: `d ≡ 1 mod 4` and squarefree, or `d = 4m` with `m`
squarefree and `m ≡ 2, 3 mod 4`. -/
def IsFundamentalDiscr (d : ℤ) : Prop :=
  (d % 4 = 1 ∧ Squarefree d) ∨ ∃ m : ℤ, d = 4 * m ∧ Squarefree m ∧ (m % 4 = 2 ∨ m % 4 = 3)

theorem isFundamentalDiscr_iff_squarefree {d : ℤ} :
    IsFundamentalDiscr d ↔ (d % 4 = 1 ∧ Squarefree d) ∨
      (d % 4 = 0 ∧ Squarefree (d / 4) ∧ (d / 4 % 4 = 2 ∨ d / 4 % 4 = 3)) := by
  unfold IsFundamentalDiscr
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨m, rfl, hm, hm4⟩
    refine ⟨by omega, ?_⟩
    rw [Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)]
    exact ⟨hm, hm4⟩
  · rintro ⟨h0, hs, h4⟩
    exact ⟨d / 4, by omega, hs, h4⟩

theorem isFundamentalDiscr_four_mul {d : ℤ} :
    IsFundamentalDiscr (4 * d) ↔ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3) := by
  unfold IsFundamentalDiscr
  constructor
  · rintro (⟨h, _⟩ | ⟨m, hm, hs, h4⟩)
    · omega
    · have : d = m := by omega
      subst this
      exact ⟨hs, h4⟩
  · rintro ⟨hs, h4⟩
    exact Or.inr ⟨d, rfl, hs, h4⟩

theorem IsFundamentalDiscr.emod_four_eq_zero_or_one {d : ℤ} (h : IsFundamentalDiscr d) :
    d % 4 = 0 ∨ d % 4 = 1 := by
  rcases h with ⟨h, _⟩ | ⟨m, rfl, _, _⟩
  · exact Or.inr h
  · left
    omega

end Int

/-- Complements are preserved by mapping along a linear equivalence. -/
theorem Submodule.isCompl_map {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) {p q : Submodule R M} (h : IsCompl p q) :
    IsCompl (p.map (e : M →ₗ[R] N)) (q.map (e : M →ₗ[R] N)) :=
  (Submodule.orderIsoMapComap e).isCompl h

/-- Krull's height theorem for a proper ideal spanned by a finite set. -/
theorem Ideal.height_span_le_card_of_span_ne_top {R : Type*} [CommRing R] [IsNoetherianRing R]
    {s : Finset R} (h : Ideal.span (s : Set R) ≠ ⊤) :
    (Ideal.span (s : Set R)).height ≤ s.card := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes h
  have : p.IsPrime := hp.1.1
  calc (Ideal.span (s : Set R)).height ≤ p.height := Ideal.height_mono hp.1.2
    _ ≤ s.card := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hp

/-- A finite sum of derivations is applied termwise. -/
theorem Derivation.sum_apply {R A M ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] (s : Finset ι) (D : ι → Derivation R A M)
    (a : A) : (∑ i ∈ s, D i) a = ∑ i ∈ s, D i a := by
  rw [← Finset.sum_apply]
  exact congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := R) (A := A) (M := M)) D s) a
