/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization
-/
import RiemannHypothesis.Zeros

/-!
# The equivalence of the formulations

This is the top of the development.  The Riemann hypothesis is open, and no proof of it is
attempted here; what this file establishes is that its standard formulations are
*equivalent*.  Three statements appear in `RiemannHypothesis.Defs`:

* `ZetaForm` — the classical form in terms of the analytically continued Riemann zeta
  function of Mathlib: every zero of `ζ` that is neither a trivial zero nor the pole at
  `s = 1` lies on the critical line `re s = 1/2`.

* `ZetaStripForm` — the same claim restricted to the critical strip `0 < re s < 1`.

* `EtaForm` — the same claim in terms of the Dirichlet eta function `η`, defined by its
  (absolutely convergent) paired series; for `1 < re s` it agrees with the classical
  alternating series (see `dirichletEta_eq_tsum_alternating_of_one_lt_re`).

The main results of this file are:

* `zeta_strip_iff_eta`: `ZetaStripForm ↔ EtaForm`.  This is where all of `RiemannHypothesis.Eta`
  is used.  The classical identity `η(s) = (1 - 2^(1-s)) ζ(s)` is proved on the punctured
  right half-plane by the identity theorem for analytic functions
  (`dirichletEta_eq_mul_riemannZeta`); both sides are analytic there (the eta side by the
  Weierstrass theorem applied to the paired series, whose terms are entire and whose partial
  sums converge locally uniformly; the zeta side by construction), and they agree on the open
  set `{s | 1 < re s}` by an elementary manipulation of absolutely convergent Dirichlet
  series.  The factor `1 - 2^(1-s)` has no zeroes in the critical strip
  (`one_sub_two_cpow_ne_zero`), so inside the strip the zeroes of `η` are exactly the zeroes
  of `ζ`.

* `zeta_iff_zeta_strip`: `ZetaForm ↔ ZetaStripForm`.  The only input beyond the above is
  that a zero of `ζ` with `re s ≤ 0` is a trivial zero (`riemannZeta_eq_zero_of_re_nonpos`),
  a standard consequence of the functional equation, together with
  `riemannZeta_ne_zero_of_one_le_re` (no zeroes with `re s ≥ 1`).

* `zeta_iff_eta`: `ZetaForm ↔ EtaForm`, combining the two.
-/

noncomputable section

namespace RiemannHypothesis

open Complex

/-- **The Riemann hypothesis in the strip form is equivalent to its Dirichlet eta form.**
Inside the critical strip the zeroes of `η` are exactly the zeroes of `ζ`, because of the
identity `η(s) = (1 - 2^(1-s)) ζ(s)` and the fact that the factor does not vanish there. -/
theorem zeta_strip_iff_eta : ZetaStripForm ↔ EtaForm := by
  constructor
  · intro hzeta s hs0 hs1 heta
    -- `η(s) = 0` and the identity give `(1 - 2^(1-s)) ζ(s) = 0`; the factor does not vanish
    have hz : riemannZeta s = 0 := by
      have hne1 : s ≠ 1 := by
        intro h
        have : s.re = 1 := congrArg re h
        linarith [hs1, this]
      have hident := dirichletEta_eq_mul_riemannZeta hs0 hne1
      have hfactor : (1 - 2 ^ (1 - s) : ℂ) ≠ 0 := one_sub_two_cpow_ne_zero hs1
      have : (1 - 2 ^ (1 - s)) * riemannZeta s = 0 := by
        rw [← hident]
        exact heta
      exact (mul_eq_zero.mp this).resolve_left hfactor
    exact hzeta s hs0 hs1 hz
  · intro heta s hs0 hs1 hz
    -- `ζ(s) = 0` gives `η(s) = 0` by the identity, then `EtaForm` applies
    have heta0 : dirichletEta s = 0 := by
      have hne1 : s ≠ 1 := by
        intro h
        have : s.re = 1 := congrArg re h
        linarith [hs1, this]
      rw [dirichletEta_eq_mul_riemannZeta hs0 hne1]
      simp [hz]
    exact heta s hs0 hs1 heta0

/-- **The zeta form is equivalent to the strip form.**  A zero of `ζ` with `re s ≤ 0` is a
trivial zero (the functional equation), and there are no zeroes with `re s ≥ 1`, so the
nontrivial zeroes of `ζ` are exactly the zeroes inside the strip. -/
theorem zeta_iff_zeta_strip : ZetaForm ↔ ZetaStripForm := by
  constructor
  · intro hzeta s hs0 hs1 hz
    have hne1 : s ≠ 1 := by
      intro h
      have : s.re = 1 := congrArg re h
      linarith [hs1, this]
    have htriv : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
      intro ⟨n, hn⟩
      have : s.re = -2 * (n + 1 : ℝ) := by
        rw [hn]
        norm_num
      nlinarith [hs0]
    have htriv' : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      intro h
      exact htriv (trivial_zero_iff.mpr h)
    exact hzeta s hz htriv' hne1
  · intro hstrip s hz htriv hs1
    have htriv' : ¬∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℕ) := by
      intro h
      exact htriv (trivial_zero_iff.mp h)
    have hsstrip : 0 < s.re ∧ s.re < 1 := zero_of_nontrivial_mem_strip hz htriv'
    exact hstrip s hsstrip.1 hsstrip.2 hz

/-- **The Riemann hypothesis in its zeta form is equivalent to its Dirichlet eta form.** -/
theorem zeta_iff_eta : ZetaForm ↔ EtaForm := by
  rw [zeta_iff_zeta_strip]
  exact zeta_strip_iff_eta

end RiemannHypothesis

end
