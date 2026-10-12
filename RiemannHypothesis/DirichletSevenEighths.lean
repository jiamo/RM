/-
Copyright (c) 2026 Riemann Hypothesis formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Hypothesis formalization

The proof of the main theorem is the native absorption of openai/math, family 003
(github.com/openai/math, revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache 2.0; see
NOTICE and LICENSES/openai-math-LICENSE), ported under `RiemannHypothesis/Family003/`.
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Nonvanishing

/-!
# Dirichlet `L`-functions have no zeroes with `re s > 7/8`

* `LFunction_ne_zero_of_seven_eighths_lt_re` — for every modulus `q ≥ 1`, every Dirichlet
  character `χ` modulo `q` (primitive or not, principal or not) and every `s` with
  `7/8 < re s`, Mathlib's `DirichletCharacter.LFunction χ s` is non-zero, except at the pole
  `χ = 1, s = 1` of the principal character.  This is upstream
  `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (openai/math `fd4aeeb`,
  module `OAI.NumberTheory.DirichletL.Nonvanishing`), whose proof is compiled here, against this
  repository's Lean and Mathlib pins, as
  `RiemannHypothesis.Family003.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`.

The public theorem has no hypothesis besides `7/8 < re s` and the pole exclusion: no detector
certificate, analytic band assumption or other unproved input appears in it, and its axioms are
`propext`, `Classical.choice`, `Quot.sound`.

## The excluded point

For `χ = 1` (the trivial character modulo `q`), `LFunction 1 s` is `ζ(s)` times the finite
Euler factor `∏_{p ∣ q} (1 - p^{-s})`, which has a pole at `s = 1`; there Mathlib's total
function `LFunction` takes a junk value, so the point is excluded, exactly as upstream.  For
`q = 1` this is `riemannZeta`, and the exclusion is harmless: `riemannZeta 1 ≠ 0` anyway (see
`RiemannHypothesis.QuasiRiemann`).
-/

namespace RiemannHypothesis.DirichletSevenEighths

/-- **Quasi-Riemann hypothesis for Dirichlet `L`-functions.**  For every Dirichlet character
`χ` of any modulus `q ≥ 1`, `L(s, χ) ≠ 0` whenever `7/8 < re s`, apart from the pole of the
principal character at `s = 1`. -/
theorem LFunction_ne_zero_of_seven_eighths_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  RiemannHypothesis.Family003.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    χ hs hpole

end RiemannHypothesis.DirichletSevenEighths
