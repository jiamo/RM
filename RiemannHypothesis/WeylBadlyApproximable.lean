/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.WeylMinSum
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# An unconditional rate for a quadratic Weyl sum: badly approximable coefficients

`RiemannHypothesis.WeylMinSum` bounds `quadSum α N = ∑_{0 ≤ n < N} e(α n²)` *conditionally* on the
existence of a rational approximation `|2α − a/q| ≤ 1/q²` whose denominator `q` lies in a
prescribed range.  That hypothesis cannot be dropped: for `α` close to a rational with small
denominator the sum has no cancellation at all.  It can, however, be *discharged* for a natural
class of `α`, and that is what this file does.

Dirichlet's theorem (mathlib's `Real.exists_rat_abs_sub_le_and_den_le`) produces, for every `n`, a
fraction `a/q` in lowest terms with `q ≤ n` and `|2α − a/q| ≤ 1/(q(n+1))`.  If `2α` is *badly
approximable*, that is if there is a `c > 0` with `|2α − a/q| ≥ c/q²` for every fraction — the
Diophantine condition satisfied by every quadratic irrational, and by every irrational with
bounded partial quotients — then `c/q² ≤ 1/(q(n+1))` forces `q ≥ c(n+1)`, so the Dirichlet
denominator is *large*, of the size of `n`, and the conditional bound applies with `n = N`.

## Results

* `normSq_quadSum_le_of_den_le` — the bound of `WeylMinSum` in the shape `16N²/q + 26N(1 + log N)`,
  valid for every denominator `q ≤ N`.
* `BadlyApproximable` — the Diophantine class, and `exists_coprime_approx`, Dirichlet's theorem in
  the numerator/denominator form used here.
* `normSq_quadSum_le_of_badlyApproximable`, `norm_quadSum_le_of_badlyApproximable` — for `2α`
  badly approximable with constant `c`,

      ‖quadSum α N‖² ≤ (16/c + 26) N (1 + log N),   ‖quadSum α N‖ ≤ √((16/c + 26) N (1 + log N)),

  **unconditionally in `N`**: no hypothesis on the size of a denominator is left to the caller.
* `badlyApproximable_sqrt_two` — `√2` is badly approximable, with `c = 1/4`.
* `norm_quadSum_sqrt_two_le` — hence, for the explicit coefficient `α = √2/2`,

      ‖∑_{0 ≤ n < N} e((√2/2) n²)‖ ≤ √(90 N (1 + log N)).

* `inv_le_abs_sub_div_of_quadratic`, `badlyApproximable_of_quadratic` — **every quadratic
  irrational is badly approximable**, by Liouville's argument, with the explicit constant
  `1/(|A|(2|x| + 1) + |B|)`; hence `exists_norm_quadSum_le_of_quadratic`, square-root cancellation
  whenever `2α` is a quadratic irrational.

This is the first *effective* rate of cancellation in the repository for a *fixed* irrational
coefficient: `M1-WEYL-EQUIDISTRIBUTION` proves `quadSum α N = o(N)` for every irrational `α`, but
through an ineffective minimum over finitely many `k`, and records "no rate" as its open boundary.

## Scope

Nothing here is about `ζ`.  The class of coefficients covered is the badly approximable ones, not
all irrationals — for an irrational of infinite type no power saving is true.  The logarithm is
not removed and the constants are not optimized.  The converse characterization of the class, by
bounded partial quotients of the continued fraction, is not formalized.
-/

noncomputable section

open Complex Finset

namespace RiemannHypothesis

namespace WeylQuadratic

/-! ## The conditional bound, in a form usable with Dirichlet's theorem -/

/-- The bound of `normSq_quadSum_le_of_approx_count`, for a denominator `q ≤ N`, in the shape
`16N²/q + 26N(1 + log N)`. -/
theorem normSq_quadSum_le_of_den_le {α : ℝ} {a : ℤ} {q N : ℕ} (hq : 0 < q) (hqN : q ≤ N)
    (hcop : IsCoprime (q : ℤ) a) (happ : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖WeylEquidistribution.quadSum α N‖ ^ 2
      ≤ 16 * (N : ℝ) ^ 2 / q + 26 * N * (1 + Real.log N) := by
  have hN : 0 < N := lt_of_lt_of_le hq hqN
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hlogq : Real.log q ≤ Real.log N := Real.log_le_log hqR hqNR
  have hlogq0 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNR
  have hmain := normSq_quadSum_le_of_approx_count hq hN hcop happ
  have hexp : 4 * ((N : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q))
      = 16 * (N : ℝ) ^ 2 / q + 4 * N * (1 + Real.log q) + 16 * N
        + 4 * q * (1 + Real.log q) := by
    field_simp
    ring
  have hqlog : (q : ℝ) * (1 + Real.log q) ≤ (N : ℝ) * (1 + Real.log N) := by
    have h1 : (0 : ℝ) ≤ 1 + Real.log q := by linarith
    nlinarith
  have hNlog : (4 : ℝ) * N * (1 + Real.log q) ≤ 4 * N * (1 + Real.log N) := by nlinarith
  have h16 : (16 : ℝ) * N ≤ 16 * N * (1 + Real.log N) := by nlinarith
  have h2 : (2 : ℝ) * N ≤ 2 * N * (1 + Real.log N) := by nlinarith
  have : ‖WeylEquidistribution.quadSum α N‖ ^ 2
      ≤ 2 * (N : ℝ) + 4 * ((N : ℝ) / q + 1) * (4 * N + q * (1 + Real.log q)) := hmain
  rw [hexp] at this
  nlinarith [this, hNlog, h16, h2, hqlog]

/-! ## Badly approximable numbers -/

/-- `x` is *badly approximable* if `|x − a/q| ≥ c/q²` for some `c > 0` and every fraction `a/q`.
Equivalently, the partial quotients of `x` are bounded. -/
def BadlyApproximable (x : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |x - (a : ℝ) / q|

/-- **Dirichlet's approximation theorem**, in the numerator/denominator form used here: for every
`n ≥ 1` there is a fraction `a/q` in lowest terms with `q ≤ n` and `|x − a/q| ≤ 1/(q(n+1))`. -/
theorem exists_coprime_approx (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ q ≤ n ∧ IsCoprime (q : ℤ) a ∧
      |x - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (n + 1)) := by
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hn
  refine ⟨r.num, r.den, r.pos, hden, ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.coprime_comm] using r.reduced
  · have hrr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
      exact_mod_cast (Rat.cast_def (K := ℝ) r)
    rw [← hrr]
    calc |x - (r : ℝ)| ≤ 1 / ((n + 1) * r.den) := hr
      _ = 1 / ((r.den : ℝ) * (n + 1)) := by ring_nf

/-- For a badly approximable `x`, the Dirichlet denominator is large: `q ≥ c (n+1)`. -/
theorem le_den_of_badlyApproximable {x : ℝ} {c : ℝ}
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |x - (a : ℝ) / q|)
    {a : ℤ} {q n : ℕ} (hq : 0 < q) (happ : |x - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (n + 1))) :
    c * ((n : ℝ) + 1) ≤ q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h := (hbad a q hq).trans happ
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
  nlinarith [hqR, h]

/-! ## The unconditional bound -/

/-- **An unconditional rate.**  If `2α` is badly approximable with constant `c ≤ 1`, then
`‖quadSum α N‖² ≤ (16/c + 26) N (1 + log N)` for every `N ≥ 1`. -/
theorem normSq_quadSum_le_of_badlyApproximable {α : ℝ} {c : ℝ} (hc : 0 < c)
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |2 * α - (a : ℝ) / q|)
    {N : ℕ} (hN : 0 < N) :
    ‖WeylEquidistribution.quadSum α N‖ ^ 2 ≤ (16 / c + 26) * N * (1 + Real.log N) := by
  obtain ⟨a, q, hq, hqN, hcop, happ⟩ := exists_coprime_approx (2 * α) hN
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNR
  -- the approximation is of Weyl quality
  have happ2 : |2 * α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    refine happ.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hmain := normSq_quadSum_le_of_den_le hq hqN hcop happ2
  -- the denominator is large
  have hden : c * ((N : ℝ) + 1) ≤ q := le_den_of_badlyApproximable hbad hq happ
  have hcN : (0 : ℝ) < c * ((N : ℝ) + 1) := by positivity
  have hdiv : 16 * (N : ℝ) ^ 2 / q ≤ 16 * (N : ℝ) ^ 2 / (c * ((N : ℝ) + 1)) := by
    apply div_le_div_of_nonneg_left (by positivity) hcN hden
  have hdiv2 : 16 * (N : ℝ) ^ 2 / (c * ((N : ℝ) + 1)) ≤ 16 * N / c := by
    rw [div_le_div_iff₀ (by positivity) hc]
    nlinarith
  have hfinal : 16 * (N : ℝ) / c ≤ (16 / c) * N * (1 + Real.log N) := by
    have hnn : (0 : ℝ) ≤ 16 / c * N := by positivity
    have : (16 / c) * N ≤ (16 / c) * N * (1 + Real.log N) := by
      nlinarith [mul_nonneg hnn hlogN0]
    calc 16 * (N : ℝ) / c = (16 / c) * N := by ring
      _ ≤ (16 / c) * N * (1 + Real.log N) := this
  nlinarith [hmain, hdiv, hdiv2, hfinal]

/-- The same in the form `‖quadSum α N‖ ≤ √((16/c + 26) N (1 + log N))`. -/
theorem norm_quadSum_le_of_badlyApproximable {α : ℝ} {c : ℝ} (hc : 0 < c)
    (hbad : ∀ (a : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |2 * α - (a : ℝ) / q|)
    {N : ℕ} (hN : 0 < N) :
    ‖WeylEquidistribution.quadSum α N‖ ≤ Real.sqrt ((16 / c + 26) * N * (1 + Real.log N)) := by
  have hsq := normSq_quadSum_le_of_badlyApproximable hc hbad hN
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at h

/-! ## `√2` is badly approximable -/

/-- `a² ≠ 2q²` for a positive integer `q`: otherwise `√2` would be rational. -/
theorem sq_ne_two_mul_sq {a : ℤ} {q : ℕ} (hq : 0 < q) : a ^ 2 ≠ 2 * (q : ℤ) ^ 2 := by
  intro h
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : (((|a| : ℤ) : ℝ) / q) ^ 2 = 2 := by
    have h2 : ((a : ℝ)) ^ 2 = 2 * (q : ℝ) ^ 2 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast [abs_eq_self]
    rw [div_pow, sq_abs]
    field_simp
    linarith [h2]
  have hnn : (0 : ℝ) ≤ ((|a| : ℤ) : ℝ) / q := by positivity
  have hval : Real.sqrt 2 = ((|a| : ℤ) : ℝ) / q := by rw [← hsq, Real.sqrt_sq hnn]
  have hirr := irrational_sqrt_two
  rw [hval] at hirr
  exact hirr ⟨((|a| : ℤ) : ℚ) / (q : ℚ), by push_cast; ring⟩

/-- **`√2` is badly approximable**, with constant `1/4`. -/
theorem badlyApproximable_sqrt_two :
    ∀ (a : ℤ) (q : ℕ), 0 < q →
      (1 / 4 : ℝ) / (q : ℝ) ^ 2 ≤ |Real.sqrt 2 - (a : ℝ) / q| := by
  intro a q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  set s := Real.sqrt 2 with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 2
  have hssq : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < s := by nlinarith
  have hs2 : s < 3 / 2 := by nlinarith
  set r : ℝ := (a : ℝ) / q with hr
  have hsmall : (1 / 4 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hq2]; nlinarith
  rcases le_or_gt r 0 with h | h
  · have h4 : (1 / 4 : ℝ) ≤ |s - r| := by
      rw [abs_of_nonneg (by linarith)]; linarith
    linarith
  rcases le_or_gt r 2 with h2 | h2
  · have hne : a ^ 2 ≠ 2 * (q : ℤ) ^ 2 := sq_ne_two_mul_sq hq
    have hintZ : (1 : ℤ) ≤ |2 * (q : ℤ) ^ 2 - a ^ 2| :=
      Int.one_le_abs (by intro hz; exact hne (by linarith))
    have hint : (1 : ℝ) ≤ |2 * (q : ℝ) ^ 2 - (a : ℝ) ^ 2| := by exact_mod_cast hintZ
    have habs : |2 - r ^ 2| = |2 * (q : ℝ) ^ 2 - (a : ℝ) ^ 2| / (q : ℝ) ^ 2 := by
      rw [hr, div_pow,
        show (2 : ℝ) - (a : ℝ) ^ 2 / (q : ℝ) ^ 2
            = (2 * (q : ℝ) ^ 2 - (a : ℝ) ^ 2) / (q : ℝ) ^ 2 by field_simp,
        abs_div, abs_of_pos hq2]
    have hlow : 1 / (q : ℝ) ^ 2 ≤ |2 - r ^ 2| := by rw [habs]; gcongr
    have hprod : |s - r| * (s + r) = |2 - r ^ 2| := by
      rw [← hssq, show s ^ 2 - r ^ 2 = (s - r) * (s + r) by ring, abs_mul,
        abs_of_pos (by linarith : (0 : ℝ) < s + r)]
    have hstep : 1 / (q : ℝ) ^ 2 ≤ |s - r| * 4 := by
      calc 1 / (q : ℝ) ^ 2 ≤ |s - r| * (s + r) := by rw [hprod]; exact hlow
        _ ≤ |s - r| * 4 := by nlinarith [abs_nonneg (s - r)]
    have h5 : (1 : ℝ) ≤ |s - r| * 4 * (q : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hstep hq2.le
      rwa [one_div, inv_mul_cancel₀ hq2.ne'] at hmul
    rw [div_le_iff₀ hq2]
    linarith
  · have h4 : (1 / 4 : ℝ) ≤ |s - r| := by
      rw [abs_of_nonpos (by linarith)]; linarith
    linarith

theorem badlyApproximable_sqrt_two' : BadlyApproximable (Real.sqrt 2) :=
  ⟨1 / 4, by norm_num, badlyApproximable_sqrt_two⟩

/-- **Square-root cancellation for an explicit irrational coefficient**:
`‖∑_{0 ≤ n < N} e((√2/2) n²)‖ ≤ √(90 N (1 + log N))` for every `N ≥ 1`. -/
theorem norm_quadSum_sqrt_two_le {N : ℕ} (hN : 0 < N) :
    ‖WeylEquidistribution.quadSum (Real.sqrt 2 / 2) N‖
      ≤ Real.sqrt (90 * N * (1 + Real.log N)) := by
  have hbad : ∀ (a : ℤ) (q : ℕ), 0 < q →
      (1 / 4 : ℝ) / (q : ℝ) ^ 2 ≤ |2 * (Real.sqrt 2 / 2) - (a : ℝ) / q| := by
    intro a q hq
    have h := badlyApproximable_sqrt_two a q hq
    rwa [show 2 * (Real.sqrt 2 / 2) = Real.sqrt 2 by ring]
  have h := norm_quadSum_le_of_badlyApproximable (c := 1 / 4) (by norm_num) hbad hN
  rwa [show (16 : ℝ) / (1 / 4) + 26 = 90 by norm_num] at h

/-! ## Quadratic irrationals -/

/-- **Every quadratic irrational is badly approximable**, with the explicit constant
`1/(|A|(2|x| + 1) + |B|)`: if `A x² + B x + C = 0` with `A ≠ 0` and `x` irrational, then for every
fraction `a/q`, `q ≥ 1`,

    |x − a/q| ≥ (1/(|A|(2|x| + 1) + |B|)) / q².

The mechanism is Liouville's: `A a² + B a q + C q²` is a *nonzero* integer, because a rational
root would make the second root `−B/A − a/q` of the quadratic rational too, and `x` is one of the
two roots; so `|f(a/q)| ≥ 1/q²`, while `f(a/q) = f(a/q) − f(x) = (a/q − x)(A(a/q + x) + B)` is at
most `|x − a/q|` times a bounded factor. -/
theorem inv_le_abs_sub_div_of_quadratic {x : ℝ} {A B C : ℤ} (hA : A ≠ 0)
    (hroot : (A : ℝ) * x ^ 2 + B * x + C = 0) (hirr : Irrational x)
    (a : ℤ) (q : ℕ) (hq : 0 < q) :
    (1 / (|(A : ℝ)| * (2 * |x| + 1) + |(B : ℝ)|)) / (q : ℝ) ^ 2 ≤ |x - (a : ℝ) / q| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  set r : ℝ := (a : ℝ) / q with hrdef
  have hAR : (1 : ℝ) ≤ |(A : ℝ)| := by
    have h : (1 : ℤ) ≤ |A| := Int.one_le_abs hA
    have hc : ((1 : ℤ) : ℝ) ≤ ((|A| : ℤ) : ℝ) := by exact_mod_cast h
    simpa using hc
  set M : ℝ := |(A : ℝ)| * (2 * |x| + 1) + |(B : ℝ)| with hM
  have hM1 : (1 : ℝ) ≤ M := by
    have hx : (0 : ℝ) ≤ |x| := abs_nonneg x
    have hb : (0 : ℝ) ≤ |(B : ℝ)| := abs_nonneg _
    have hstep : |(A : ℝ)| * 1 ≤ |(A : ℝ)| * (2 * |x| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    rw [hM]; linarith
  have hM0 : (0 : ℝ) < M := by linarith
  set m : ℤ := A * a ^ 2 + B * a * q + C * (q : ℤ) ^ 2 with hmdef
  have hfr : (A : ℝ) * r ^ 2 + B * r + C = (m : ℝ) / (q : ℝ) ^ 2 := by
    rw [hmdef, hrdef]; push_cast; field_simp
  have hdiff : (A : ℝ) * r ^ 2 + B * r + C = (r - x) * ((A : ℝ) * (r + x) + B) := by
    nlinarith [hroot]
  have hmne : m ≠ 0 := by
    intro h0
    have hr : (A : ℝ) * r ^ 2 + B * r + C = 0 := by rw [hfr, h0]; norm_num
    have hne : x ≠ r := fun hxr =>
      hirr ⟨(a : ℚ) / (q : ℚ), by rw [hxr, hrdef]; push_cast; ring⟩
    have hfac : (x - r) * ((A : ℝ) * (x + r) + B) = 0 := by nlinarith [hroot, hr]
    have hlin : (A : ℝ) * (x + r) + B = 0 := by
      rcases mul_eq_zero.1 hfac with h | h
      · exact absurd (sub_eq_zero.1 h) hne
      · exact h
    have hA0 : (A : ℝ) ≠ 0 := Int.cast_ne_zero.2 hA
    have hxval : x = -((B : ℝ) / A) - r := by field_simp; field_simp at hlin; linarith
    exact hirr ⟨-((B : ℚ) / A) - (a : ℚ) / (q : ℚ), by rw [hxval, hrdef]; push_cast; ring⟩
  have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
    have h1m : (1 : ℤ) ≤ |m| := by
      rcases lt_trichotomy m 0 with h | h | h
      · rw [abs_of_neg h]; omega
      · exact absurd h hmne
      · rw [abs_of_pos h]; omega
    have hc : ((1 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1m
    simpa using hc
  rcases le_or_gt 1 |x - r| with hbig | hsmall
  · have hle : (1 / M) / (q : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one hq2, div_le_iff₀ hM0]
      nlinarith [hq1, hM1]
    linarith
  · have hrb : |r| ≤ |x| + 1 := by
      have h1 := abs_sub_abs_le_abs_sub r x
      have h2 : |r - x| = |x - r| := abs_sub_comm r x
      linarith [h1, h2.le, hsmall.le]
    have hcoef : |(A : ℝ) * (r + x) + B| ≤ M := by
      have h1 : |(A : ℝ) * (r + x)| = |(A : ℝ)| * |r + x| := abs_mul _ _
      have h2 : |r + x| ≤ |r| + |x| := abs_add_le r x
      have h3 : |(A : ℝ) * (r + x) + B| ≤ |(A : ℝ) * (r + x)| + |(B : ℝ)| := abs_add_le _ _
      have h5 : |(A : ℝ)| * |r + x| ≤ |(A : ℝ)| * (2 * |x| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      rw [hM]; linarith
    have hkey : (1 : ℝ) / (q : ℝ) ^ 2 ≤ |x - r| * M := by
      have h1 : |(m : ℝ)| / (q : ℝ) ^ 2 = |x - r| * |(A : ℝ) * (r + x) + B| := by
        rw [← abs_of_pos hq2, ← abs_div, ← hfr, hdiff, abs_mul, abs_sub_comm r x]
      have h2 : (1 : ℝ) / (q : ℝ) ^ 2 ≤ |(m : ℝ)| / (q : ℝ) ^ 2 := by gcongr
      rw [h1] at h2
      have h3 : |x - r| * |(A : ℝ) * (r + x) + B| ≤ |x - r| * M :=
        mul_le_mul_of_nonneg_left hcoef (abs_nonneg _)
      linarith
    rw [div_div, div_le_iff₀ (by positivity : (0 : ℝ) < M * (q : ℝ) ^ 2)]
    have h9 : (1 : ℝ) ≤ |x - r| * M * (q : ℝ) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hkey hq2.le
      rwa [one_div, inv_mul_cancel₀ hq2.ne'] at hh
    nlinarith [h9]

/-- Every quadratic irrational is badly approximable. -/
theorem badlyApproximable_of_quadratic {x : ℝ} {A B C : ℤ} (hA : A ≠ 0)
    (hroot : (A : ℝ) * x ^ 2 + B * x + C = 0) (hirr : Irrational x) :
    BadlyApproximable x := by
  have hAR : (1 : ℝ) ≤ |(A : ℝ)| := by
    have h : (1 : ℤ) ≤ |A| := Int.one_le_abs hA
    have hc : ((1 : ℤ) : ℝ) ≤ ((|A| : ℤ) : ℝ) := by exact_mod_cast h
    simpa using hc
  refine ⟨1 / (|(A : ℝ)| * (2 * |x| + 1) + |(B : ℝ)|), ?_,
    inv_le_abs_sub_div_of_quadratic hA hroot hirr⟩
  have hx : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hb : (0 : ℝ) ≤ |(B : ℝ)| := abs_nonneg _
  have hstep : |(A : ℝ)| * 1 ≤ |(A : ℝ)| * (2 * |x| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have : (0 : ℝ) < |(A : ℝ)| * (2 * |x| + 1) + |(B : ℝ)| := by linarith
  positivity

/-- **The rate, for every badly approximable coefficient**, in the form that hides the constant:
there is a `K > 0` with `‖quadSum α N‖ ≤ √(K N (1 + log N))` for every `N ≥ 1`. -/
theorem exists_norm_quadSum_le_of_badlyApproximable {α : ℝ} (h : BadlyApproximable (2 * α)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ‖WeylEquidistribution.quadSum α N‖ ≤ Real.sqrt (K * N * (1 + Real.log N)) := by
  obtain ⟨c, hc, hbad⟩ := h
  exact ⟨16 / c + 26, by positivity, fun N hN => norm_quadSum_le_of_badlyApproximable hc hbad hN⟩

/-- **Square-root cancellation whenever `2α` is a quadratic irrational.** -/
theorem exists_norm_quadSum_le_of_quadratic {α : ℝ} {A B C : ℤ} (hA : A ≠ 0)
    (hroot : (A : ℝ) * (2 * α) ^ 2 + B * (2 * α) + C = 0) (hirr : Irrational (2 * α)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ‖WeylEquidistribution.quadSum α N‖ ≤ Real.sqrt (K * N * (1 + Real.log N)) :=
  exists_norm_quadSum_le_of_badlyApproximable (badlyApproximable_of_quadratic hA hroot hirr)

end WeylQuadratic

end RiemannHypothesis
