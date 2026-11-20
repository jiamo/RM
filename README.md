This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# The Riemann Hypothesis in Lean

A formalization of the **Riemann hypothesis** — its *precise statement*, the proof that its
standard formulations are **equivalent**, and the unconditional theory that surrounds it:
the prime number theorem, Mertens' three theorems, the classical de la Vallée Poussin
zero-free region, the growth and convexity bounds, the zero-counting theorems, Hardy's
theorem, the moments of `ζ`, the proportion of zeroes on the critical line, and five
sufficient conditions ("routes") each of which would imply the hypothesis.

The Riemann hypothesis is open, and this repository does not claim to prove it.  What it
does prove is that the following three formulations say the same thing:

```lean
/-- The Riemann hypothesis (zeta form, as in Mathlib). -/
abbrev ZetaForm : Prop := RiemannHypothesis
-- every zero of ζ, other than the trivial zeroes −2(n+1) and the pole at s = 1,
-- has real part 1/2

/-- The Riemann hypothesis restricted to the critical strip. -/
def ZetaStripForm : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- The Riemann hypothesis in terms of the Dirichlet eta function. -/
def EtaForm : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → dirichletEta s = 0 → s.re = 1 / 2
```

The three main theorems of the repository are the equivalences between them:

```lean
theorem zeta_strip_iff_eta : ZetaStripForm ↔ EtaForm
theorem zeta_iff_zeta_strip : ZetaForm ↔ ZetaStripForm
theorem zeta_iff_eta : ZetaForm ↔ EtaForm
```

[`RiemannHypothesis/Symmetry.lean`](RiemannHypothesis/Symmetry.lean) adds five more equivalent
formulations, obtained from the symmetries of the zero set inside the strip:

```lean
theorem zeta_strip_iff_upper_strip : ZetaStripForm ↔ ZetaUpperStripForm
theorem zeta_strip_iff_right_strip : ZetaStripForm ↔ ZetaRightStripForm
theorem zeta_strip_iff_nonvanishing_right : ZetaStripForm ↔ ZetaNonvanishingRightForm
theorem zeta_strip_iff_self_reflective : ZetaStripForm ↔ ZetaSelfReflectiveForm
theorem zeta_strip_iff_forall_verifiedUpToHeight : ZetaStripForm ↔ ∀ H : ℝ, VerifiedUpToHeight H
```

That is: it is enough to constrain the zeroes of positive imaginary part; equivalently, `ζ`
has no zero at all in `1/2 < re s < 1`, equivalently none in the half-plane `re s > 1/2`;
equivalently every zero in the strip is fixed by the reflection `s ↦ 1 - conj s`; and
equivalently the numerical verification succeeds at *every* height.  The inputs are the
conjugation symmetry `ζ(conj s) = conj (ζ s)` (proved here from the paired eta series, since
Mathlib does not have it), the reflection `s ↦ 1 - s` of the functional equation, and the
nonvanishing of `ζ` on the real interval `(0, 1)` (proved here from the positivity of every
paired term of the eta series).

Finally, [`RiemannHypothesis/Alternating.lean`](RiemannHypothesis/Alternating.lean) removes
the last trace of analytic machinery from the statement.  Inside the strip the alternating
series converges only *conditionally*, so its unconditional sum (Mathlib's `tsum`) is
useless there; what is true is that its **partial sums** converge:

```lean
theorem tendsto_alternating_partialSum_dirichletEta {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) atTop
      (𝓝 (dirichletEta s))

theorem zeta_iff_eta_limit : ZetaForm ↔ EtaLimitForm
```

where `EtaLimitForm` says: *if the partial sums of `∑ (-1)ⁿ / (n+1)ˢ` tend to `0` at a point
of the critical strip, then that point has real part `1/2`*.  This is the Riemann hypothesis
with no analytic continuation and no unconditional summation anywhere in the statement.

## Highlights

The strongest results in the repository, all machine-checked, `sorry`-free, and depending on
exactly the three standard axioms `propext`, `Classical.choice`, `Quot.sound`:

| Result | Statement | Where |
| --- | --- | --- |
| **Equivalent forms of the hypothesis** | `ZetaForm ↔ ZetaStripForm ↔ EtaForm ↔ EtaLimitForm ↔ XiForm`, plus the upper-strip, right-strip, nonvanishing, self-reflective, every-height-verified, reciprocal, log-branch, counting, supremum and logarithmic-derivative forms | [`Main.lean`](RiemannHypothesis/Main.lean), [`Symmetry.lean`](RiemannHypothesis/Symmetry.lean), [`Alternating.lean`](RiemannHypothesis/Alternating.lean), [`Xi.lean`](RiemannHypothesis/Xi.lean), [`Criteria.lean`](RiemannHypothesis/Criteria.lean), [`LogDerivCriterion.lean`](RiemannHypothesis/LogDerivCriterion.lean) |
| **Five sufficient conditions for the hypothesis** | square-root cancellation in `M(N)`, in `det (A n)`, in `ψ(N) − N`, in `∑_{n≤N} μ(n)/n` or in `L(N)` — each *implies* `ZetaForm` | [`MoebiusCriterion.lean`](RiemannHypothesis/MoebiusCriterion.lean), [`Redheffer.lean`](RiemannHypothesis/Redheffer.lean), [`ChebyshevCriterion.lean`](RiemannHypothesis/ChebyshevCriterion.lean), [`MoebiusOverNCriterion.lean`](RiemannHypothesis/MoebiusOverNCriterion.lean), [`LiouvilleCriterion.lean`](RiemannHypothesis/LiouvilleCriterion.lean) |
| **More than two thirds of the zeroes are simple and on the critical line** | `(2/3 − ε)·N(T,2T) ≤ N₀ˢ(T,2T)` for all large `T` | [`Zeta23Bridge.lean`](RiemannHypothesis/Zeta23Bridge.lean) (restated from the vendored [`Zeta23`](vendor/zeta23)) |
| **At least 67 % of the zeroes are on the critical line, `ε`-free** | `0.67·N(T,2T) ≤ N₀*(T,2T)` for all large `T`, from `c₁* > 88/117` | [`SixtySevenPercent.lean`](RiemannHypothesis/SixtySevenPercent.lean) |
| **At least 80 % of the distinct zeroes are simple** | `0.8·N_d ≤ Nˢ`, `ε`-free, and `4/5 ≤ liminf Nˢ(0,T)/N_d(0,T)` | [`EightyPercentSimple.lean`](RiemannHypothesis/EightyPercentSimple.lean) |
| **At least 80 % of the zeroes are distinct** | `0.8·N ≤ N_d`, `ε`-free | [`EightyPercent.lean`](RiemannHypothesis/EightyPercent.lean) |
| **At most a third of the zeroes lie off the critical line** | `limsup N_off(T)/N(T) ≤ 1/3` — the hypothesis says this count is `0` | [`OffLine.lean`](RiemannHypothesis/OffLine.lean) |
| **The de Bruijn–Newman bridge, unconditionally** | `H₀(z) = Ξ(z/2)/8`, hence `ZetaForm ↔ ∀ z, H₀ z = 0 → z.im = 0`, with no hypotheses | [`FourierXi.lean`](RiemannHypothesis/FourierXi.lean), [`ThetaW.lean`](RiemannHypothesis/ThetaW.lean) |
| **The prime number theorem** | `π(x) ∼ x/log x`, together with Mertens' three theorems and Chebyshev's bounds | [`PrimeNumberTheorem.lean`](RiemannHypothesis/PrimeNumberTheorem.lean), [`PrimeCounting.lean`](RiemannHypothesis/PrimeCounting.lean), [`Mertens.lean`](RiemannHypothesis/Mertens.lean) |
| **The de la Vallée Poussin zero-free region** | `ζ(s) ≠ 0` for `re s > 1 − c/log|im s|`, `|im s| ≥ 3` — the classical exponent one; every zero with `|im s| ≥ 3` then satisfies `|re s − 1/2| ≤ 1/2 − c/log|im s|` | [`ZeroFreeClassical.lean`](RiemannHypothesis/ZeroFreeClassical.lean), [`ZeroLocationClassical.lean`](RiemannHypothesis/ZeroLocationClassical.lean) |
| **An explicit, self-contained zero-free region** | `ζ(s) ≠ 0` for `re s > 1 − 2⁻⁴⁵/(log|im s|)⁹`, `|im s| ≥ 4` — weaker in shape than the above, but with a completely explicit constant and no Hadamard-product input | [`ZeroFreeRegion.lean`](RiemannHypothesis/ZeroFreeRegion.lean), [`ZeroLocation.lean`](RiemannHypothesis/ZeroLocation.lean) |
| **Weil's explicit formula, and the positive direction of his criterion** | the explicit formula in test-function form, the Weil functional, and `ZetaForm → 0 ≤ Re W(k)` for every positive test function (the class shown nonempty) | [`ExplicitFormula.lean`](RiemannHypothesis/ExplicitFormula.lean), [`WeilPositivity.lean`](RiemannHypothesis/WeilPositivity.lean), [`WeilTestFunctions.lean`](RiemannHypothesis/WeilTestFunctions.lean) |
| **A conditional route past 80 % on the critical line** | the counting functions of `ζ` and of `ξ′` differ by `O(log T)` (proved); *conditionally* on the counting form of Speiser's theorem, `84 %` of the distinct zeroes and `70 %` of the zeroes with multiplicity lie on the line | [`EightyPercentRoute.lean`](RiemannHypothesis/EightyPercentRoute.lean) |
| **Speiser's transfer for the multiple zeroes, unconditionally** | `m_{ξ′}(ρ) + 1 = m_ζ(ρ)` at every nontrivial zero, hence at most `13.136 %` of the zeroes of `ζ` are both multiple and off the critical line | [`SpeiserMultiple.lean`](RiemannHypothesis/SpeiserMultiple.lean) |
| **Rolle's theorem on the critical line, and what the Speiser transfer really costs** | unconditionally, between two zeroes of `ζ` on the line there is a zero of `ξ′` on the line, so `N₀ᵐ ≤ N₀ᵐ_{ξ′} + 1` and `N_offᵐ_{ξ′} ≤ N_offᵐ + O(log T)`; the transfer hypothesis is *equivalent* to the reverse comparison, and already implies `86.864 %` on the line | [`CriticalLineXi.lean`](RiemannHypothesis/CriticalLineXi.lean), [`SpeiserRolle.lean`](RiemannHypothesis/SpeiserRolle.lean), [`SpeiserEquivalence.lean`](RiemannHypothesis/SpeiserEquivalence.lean), [`EightyPercentMultiplicity.lean`](RiemannHypothesis/EightyPercentMultiplicity.lean) |
| **The easy half of Speiser's theorem, quantitatively** | if every nontrivial zero of `ζ` is on the critical line, then `ξ′` has only `O(log T)` off-line zeroes per dyadic window; contrapositively, enough off-line zeroes of `ξ′` would disprove the hypothesis | [`SpeiserRH.lean`](RiemannHypothesis/SpeiserRH.lean) |
| **The argument principle on a rectangle, and Littlewood's counting identity** | for an *arbitrary* `f`: `(1/2πi)∮_{∂R} f′/f` is the number of zeroes of `f` inside `R` with multiplicity, and integrating that count across `R` gives `∑_ρ ord_ρ(f)·(re ρ − σ₀)`; specialized to `ζ` on a rectangle inside the strip | [`RectangleZeroCount.lean`](RiemannHypothesis/RectangleZeroCount.lean), [`RectangleArgumentPrinciple.lean`](RiemannHypothesis/RectangleArgumentPrinciple.lean), [`ZetaRectangleCount.lean`](RiemannHypothesis/ZetaRectangleCount.lean) |
| **Littlewood's lemma** | for an *arbitrary* `f` analytic on a neighbourhood of a rectangle and nonvanishing on its border, `2π ∑_ρ ord_ρ(f)·(re ρ − z.re)` equals boundary data: the integral of `log ‖f‖` over the two vertical sides, plus the increments of a continuous argument of `f` over the two horizontal sides; the branch of the logarithm is built by integrating `f′/f`, and the winding number around the border is proved to be an integer | [`ArgumentSegment.lean`](RiemannHypothesis/ArgumentSegment.lean), [`LogDerivIntegrable.lean`](RiemannHypothesis/LogDerivIntegrable.lean), [`Littlewood.lean`](RiemannHypothesis/Littlewood.lean) |
| **The Bohr–Landau zero-density theorem** | for every fixed `σ > 1/2` the zeroes with `re ρ ≥ σ` and `0 < im ρ ≤ T` number `O_σ(T)`; since `N(0, T) ≫ T log T`, **almost all zeroes lie within `δ` of the critical line**, the exceptional proportion being `O_δ(1/log T)` | [`StripMeanSquareUniform.lean`](RiemannHypothesis/StripMeanSquareUniform.lean), [`ZetaCircleAverage.lean`](RiemannHypothesis/ZetaCircleAverage.lean), [`BohrLandau.lean`](RiemannHypothesis/BohrLandau.lean) |
| **Counting the zeroes** | `N(T) = O(T log T)`, `N(T) → ∞`, `∑_ρ 1/(1+γ²) < ∞`, and infinitely many zeroes in the strip | [`ZeroCount.lean`](RiemannHypothesis/ZeroCount.lean), [`ZeroCountLower.lean`](RiemannHypothesis/ZeroCountLower.lean), [`ZeroSum.lean`](RiemannHypothesis/ZeroSum.lean) |
| **Hardy's theorem, quantified** | zeroes on the critical line of arbitrarily large ordinate, in both directions; `Ξ` has unbounded real zeroes | [`CriticalLineOrdinates.lean`](RiemannHypothesis/CriticalLineOrdinates.lean) |
| **The shape of the zero set** | zeroes off the line come in quadruples `ρ, conj ρ, 1−ρ, 1−conj ρ` of *equal multiplicity*, so `N(T)` is even and `4 ∣ N_off(T)` — with or without multiplicity | [`OffLineQuadruple.lean`](RiemannHypothesis/OffLineQuadruple.lean), [`ZeroMultiplicitySymmetry.lean`](RiemannHypothesis/ZeroMultiplicitySymmetry.lean) |

**What is deliberately not claimed.** The Riemann hypothesis is open and is *not* proved here:
there is no term of type `ZetaForm` anywhere in the repository, and
[`scripts/audit.sh`](scripts/audit.sh) checks that none appears.  The proportion results are
`liminf`/`limsup` statements with no effective threshold `T₀`; raising the proportion of zeroes
*on the critical line* to `80 %` is an open research problem and is recorded as a statement only.
Everything above is either a classical theorem, an equivalent reformulation of the hypothesis, or
a consequence of the two, and several of the proportion results are restatements of the vendored
[`Zeta23`](vendor/zeta23) library, attributed module by module.

Running [`scripts/audit.sh`](scripts/audit.sh) rebuilds the project, checks that no `sorry`
occurs outside [`Challenge.lean`](Challenge.lean) (the statement of record, discharged in
[`Solution.lean`](Solution.lean)), prints the axioms of every headline declaration, re-elaborates
the pinned statements of [`scripts/revalidation.lean`](scripts/revalidation.lean), lists every
*conditional* theorem — one whose hypotheses mention a `Prop` this repository states but does not
prove — and validates the task board.  That last check makes the conditional/unconditional
boundary machine-checked rather than a docstring claim: the list produced by
[`scripts/conditional_theorems.lean`](scripts/conditional_theorems.lean) is diffed against
`docs/goal/conditional-theorems.txt`, so a new hypothesis-carrying theorem cannot be added
without recording it.  The manifest is generated by running
`lake env lean scripts/conditional_theorems.lean > docs/goal/conditional-theorems.txt` once.

## Why this is interesting (and not a formality)

The **zeta form** is written in terms of the analytically continued Riemann zeta function —
it needs complex analysis just to be *stated*.  The **eta form** is elementary: the Dirichlet
eta function `η(s) = 1 − 2⁻ˢ + 3⁻ˢ − 4⁻ˢ + ⋯` is given by a series that converges (conditionally)
for `re s > 0`.  The bridge between the two is the classical identity

```
η(s) = (1 − 2^(1−s)) ζ(s)
```

valid on the punctured right half-plane `re s > 0, s ≠ 1`.  Because the factor
`1 − 2^(1−s)` never vanishes inside the critical strip (its zeroes all lie on the line
`re s = 1`), the zeroes of `η` inside the strip are *exactly* the zeroes of `ζ` there — which
is precisely the equivalence `ZetaStripForm ↔ EtaForm`.

## How the identity is proved (the mathematical content)

1. **The Dirichlet eta function** is defined by its *paired* series
   `η(s) = Σⱼ ((2j+1)⁻ˢ − (2j+2)⁻ˢ)` ([`Defs.lean`](RiemannHypothesis/Defs.lean)).  Grouping
   the terms of the classical alternating series in pairs is what makes the series converge
   *absolutely* for `re s > 0`, which the definition needs (Mathlib's `tsum` is the
   unconditional sum, and the alternating series is only conditionally convergent in the
   strip).  The classical alternating-series representation is recovered for `1 < re s` in
   [`dirichletEta_eq_tsum_alternating_of_one_lt_re`](RiemannHypothesis/Eta.lean).

2. **Analyticity of `η` on `re s > 0`** ([`Eta.lean`](RiemannHypothesis/Eta.lean)): each
   paired term is entire, the series converges absolutely and locally uniformly (the bound
   comes from the mean value theorem applied to `exp`), so the Weierstrass theorem applies.

3. **The identity on `1 < re s`**: an elementary manipulation of absolutely convergent
   Dirichlet series (split the series of `ζ` into its odd and even parts).

4. **The identity on `0 < re s, s ≠ 1`**: the identity theorem for analytic functions.
   Both sides are analytic on the punctured right half-plane and agree on the open set
   `{s | 1 < re s}`.  The domain is preconnected — proved directly, by joining every point
   to `2` with a segment, in [`Connected.lean`](RiemannHypothesis/Connected.lean).

5. **The trivial zeroes** ([`Zeros.lean`](RiemannHypothesis/Zeros.lean)): a zero of `ζ` with
   `re s ≤ 0` is a trivial zero `s = −2(n+1)`, by the functional equation.  Together with
   the nonvanishing of `ζ` on `re s ≥ 1` (from Mathlib) this gives
   `ZetaForm ↔ ZetaStripForm`.

## Repository layout

| file | contents |
|---|---|
| [`Challenge.lean`](Challenge.lean) | the statement of record: the three equivalences, stated and unproved (`sorry`), the Comparator convention |
| [`Solution.lean`](Solution.lean) | the same three equivalences, proved as bridges to the library |
| [`RiemannHypothesis/Defs.lean`](RiemannHypothesis/Defs.lean) | `dirichletEta`, `ZetaForm`, `ZetaStripForm`, `EtaForm` |
| [`RiemannHypothesis/Connected.lean`](RiemannHypothesis/Connected.lean) | the punctured right half-plane is preconnected |
| [`RiemannHypothesis/Eta.lean`](RiemannHypothesis/Eta.lean) | the eta function: analyticity, the alternating series, the identity `η = (1−2^(1−s)) ζ` |
| [`RiemannHypothesis/Zeros.lean`](RiemannHypothesis/Zeros.lean) | the factor has no zeroes in the strip; the trivial zeroes |
| [`RiemannHypothesis/Symmetry.lean`](RiemannHypothesis/Symmetry.lean) | conjugation and reflection symmetry of the zeroes, no real zero in `(0,1)`, five further equivalent formulations |
| [`RiemannHypothesis/Alternating.lean`](RiemannHypothesis/Alternating.lean) | the alternating partial sums converge to `η` on `re s > 0`; the fully elementary form of the hypothesis |
| [`RiemannHypothesis/Bounds.lean`](RiemannHypothesis/Bounds.lean) | an explicit bound `‖ζ(s)‖ ≤ 1 + 1/(re s − 1)` on the half-plane of absolute convergence |
| [`RiemannHypothesis/MertensSums.lean`](RiemannHypothesis/MertensSums.lean) | the hyperbola reindexings of `∑_{d·e ≤ m}`, the identity `∑_{n ≤ N} μ(n)⌊N/n⌋ = 1`, and Landau's inequality `\|∑_{n ≤ N} μ(n)/n\| ≤ 1` |
| [`RiemannHypothesis/Criteria.lean`](RiemannHypothesis/Criteria.lean) | four further equivalent forms: the analytic reciprocal, the log-branch, the counting and the supremum form |
| [`RiemannHypothesis/LogDerivCriterion.lean`](RiemannHypothesis/LogDerivCriterion.lean) | the logarithmic-derivative form `∃ g holomorphic on re s > 1/2 with P' = g·P`, `P(s) = (s−1)ζ(s)`, and the rigidity lemma `f' = S·f ⇒ f(p) ≠ 0` behind it |
| [`RiemannHypothesis/AbelDirichlet.lean`](RiemannHypothesis/AbelDirichlet.lean) | the Abel-summation skeleton shared by the criteria: partial sums `A(N) = O(N^(θ+ε))` make `∑ a(n) n^(−s)` holomorphic on `re s > θ` |
| [`RiemannHypothesis/MoebiusCriterion.lean`](RiemannHypothesis/MoebiusCriterion.lean) | the Mertens criterion: `M(N) = O(N^(1/2+ε))` implies the hypothesis |
| [`RiemannHypothesis/MoebiusOverNCriterion.lean`](RiemannHypothesis/MoebiusOverNCriterion.lean) | the weighted criterion: `∑_{n ≤ N} μ(n)/n = O(N^(−1/2+ε))` implies the hypothesis |
| [`RiemannHypothesis/ChebyshevCriterion.lean`](RiemannHypothesis/ChebyshevCriterion.lean) | the Chebyshev criterion: a square-root error term `ψ(N) − N = O(N^(1/2+ε))` in the prime number theorem implies the hypothesis |
| [`RiemannHypothesis/LiouvilleCriterion.lean`](RiemannHypothesis/LiouvilleCriterion.lean) | the Liouville criterion: `∑_{n ≤ N} λ(n) = O(N^(1/2+ε))` implies the hypothesis, from `ζ(s)·L(λ,s) = ζ(2s)` |
| [`RiemannHypothesis/LiouvilleSums.lean`](RiemannHypothesis/LiouvilleSums.lean) | the elementary Liouville sums `∑_{n ≤ N} λ(n)⌊N/n⌋ = ⌊√N⌋` and `\|∑_{n ≤ N} λ(n)/n − ⌊√N⌋/N\| ≤ 1` |
| [`RiemannHypothesis/Redheffer.lean`](RiemannHypothesis/Redheffer.lean) | Redheffer's matrix `A n` and the determinant evaluation `det (A n) = M(n)`; a square-root bound for these determinants implies the hypothesis |
| [`RiemannHypothesis/Growth.lean`](RiemannHypothesis/Growth.lean) | growth of `ζ` *inside* the strip: `‖ζ(σ+it)‖ ≤ C(σ)(1+\|t\|)`, and the Mertens `3-4-1` product bound |
| [`RiemannHypothesis/EulerMaclaurin.lean`](RiemannHypothesis/EulerMaclaurin.lean) | the Euler–Maclaurin representation of `ζ` and the logarithmic bound `‖ζ(s)‖ ≤ 6 + log(1+\|t\|)` on `1 ≤ re s ≤ 2` |
| [`RiemannHypothesis/ZeroFree.lean`](RiemannHypothesis/ZeroFree.lean) | a quantitative lower bound for `ζ` to the right of the line `re s = 1`, from the `3-4-1` inequality and the two upper bounds |
| [`RiemannHypothesis/DirichletSeriesBounds.lean`](RiemannHypothesis/DirichletSeriesBounds.lean) | the sharp real Dirichlet-series bounds right of `re s = 1`: `1/(σ−1) ≤ ζ(σ) ≤ 1/(σ−1) + 1`, `−ζ'/ζ(σ) ≤ (1+o(1))/(σ−1)`, and the `3-4-1` inequality for `−Re ζ'/ζ` |
| [`RiemannHypothesis/Continuation.lean`](RiemannHypothesis/Continuation.lean) | the Euler–Maclaurin representation continued to the punctured right half-plane `{0 < re s} \ {1}` by the identity theorem |
| [`RiemannHypothesis/NearLine.lean`](RiemannHypothesis/NearLine.lean) | the logarithmic bound `‖ζ(s)‖ ≤ 18 log\|t\|` on `1 − 1/(2 log\|t\|) ≤ re s ≤ 2`, i.e. on *both* sides of the line `re s = 1` |
| [`RiemannHypothesis/ZeroFreeRegion.lean`](RiemannHypothesis/ZeroFreeRegion.lean) | Cauchy's estimate `‖ζ'(s)‖ ≤ 288 (log\|t\|)²` near the line, and the zero-free region `ζ(s) ≠ 0` for `re s > 1 − 2^(−45)/(log\|im s\|)^9` |
| [`RiemannHypothesis/ZeroLocation.lean`](RiemannHypothesis/ZeroLocation.lean) | reflecting that region: every zero with `\|im s\| ≥ 4` satisfies `\|re s − 1/2\| ≤ 1/2 − 2^(−45)/(log\|im s\|)^9` |
| [`RiemannHypothesis/ZeroFreeClassical.lean`](RiemannHypothesis/ZeroFreeClassical.lean) | **the de la Vallée Poussin zero-free region**, exponent one: `ζ(s) ≠ 0` for `\|im s\| ≥ 3` and `re s > 1 − c/log\|im s\|`, from the `3-4-1` inequality and the Hadamard expansion of `ξ'/ξ` |
| [`RiemannHypothesis/ZeroLocationClassical.lean`](RiemannHypothesis/ZeroLocationClassical.lean) | reflecting that region: every zero with `\|im s\| ≥ 3` satisfies `\|re s − 1/2\| ≤ 1/2 − c/log\|im s\|` |
| [`RiemannHypothesis/StripGrowth.lean`](RiemannHypothesis/StripGrowth.lean) | the trivial convexity bound `‖ζ(s)‖ ≤ (8/σ)\|t\|^(1−σ)(1+log\|t\|)` inside the strip `0 < σ ≤ 1`, i.e. `O(√\|t\| log\|t\|)` at `σ = 1/2` |
| [`RiemannHypothesis/ImaginaryAxis.lean`](RiemannHypothesis/ImaginaryAxis.lean) | the exact modulus `‖Γ(1−it)‖² = πt/sinh(πt)` of the functional-equation factor, and the square-root bound `‖ζ(it)‖ ≤ √(\|t\|/2π)(6+log(1+\|t\|))` |
| [`RiemannHypothesis/Convexity.lean`](RiemannHypothesis/Convexity.lean) | the Phragmén–Lindelöf convexity bound `‖ζ(σ+it)‖ ≤ C_ε \|t\|^((1−σ)/2+ε)` on `0 ≤ σ ≤ 1`, and `O(\|t\|^(1/4+ε))` on the critical line |
| [`RiemannHypothesis/ConvexityLog.lean`](RiemannHypothesis/ConvexityLog.lean) | the same bound without the `ε`: `‖ζ(σ+it)‖ ≤ C(1+log\|t\|)\|t\|^((1−σ)/2)`, with an absolute constant |
| [`RiemannHypothesis/PrimeCounting.lean`](RiemannHypothesis/PrimeCounting.lean) | the prime number theorem reduced to the Chebyshev asymptotic `ψ(x) ~ x` |
| [`RiemannHypothesis/ChebyshevLower.lean`](RiemannHypothesis/ChebyshevLower.lean) | Chebyshev's lower bound `ψ(x) ≥ (log 2/2)x`, `θ(x) ≫ x` and `π(x) ≫ x/log x`, by the central-binomial argument |
| [`RiemannHypothesis/Mertens.lean`](RiemannHypothesis/Mertens.lean) | Mertens' first theorem `∑_{n ≤ x} Λ(n)/n = log x + O(1)`, with an explicit constant |
| [`RiemannHypothesis/MertensSecond.lean`](RiemannHypothesis/MertensSecond.lean) | Mertens' second theorem `∑_{p ≤ x} 1/p = log log x + O(1)`, with an explicit constant, by Abel summation |
| [`RiemannHypothesis/MertensThird.lean`](RiemannHypothesis/MertensThird.lean) | Mertens' third theorem in bounded form: `∏_{p ≤ x} (1 − 1/p)⁻¹ ≍ log x` |
| [`RiemannHypothesis/Spectral.lean`](RiemannHypothesis/Spectral.lean) | the heat-kernel reading of the functional equation: theta modularity on the imaginary axis, and `Λ(s)` as the Mellin transform of the heat trace |
| [`RiemannHypothesis/Xi.lean`](RiemannHypothesis/Xi.lean) | the Riemann `Ξ` function, proved entire, and the equivalence of the hypothesis with "every zero of `Ξ` is real" |
| [`RiemannHypothesis/ZeroCountingLemma.lean`](RiemannHypothesis/ZeroCountingLemma.lean) | a Jensen-type counting lemma: a function holomorphic on a disc of radius `3r` has at most `log(M/\|f(c)\|)/log 3` zeroes in the disc of radius `r` |
| [`RiemannHypothesis/XiGrowth.lean`](RiemannHypothesis/XiGrowth.lean) | the completed function `ξ(s) = ½s(s−1)Λ(s)` is entire and of order one: `‖ξ(s)‖ ≤ exp(C(1+‖s‖)log(2+‖s‖))` |
| [`RiemannHypothesis/RectangleZeroCount.lean`](RiemannHypothesis/RectangleZeroCount.lean) | the zeroes of an arbitrary `f` in a rectangle and their number with multiplicity, the finiteness of that set, monotonicity in the rectangle, and Littlewood's identity in counting form — mathlib only |
| [`RiemannHypothesis/RectangleArgumentPrinciple.lean`](RiemannHypothesis/RectangleArgumentPrinciple.lean) | the argument principle on a rectangle in counting form and its weighted version, on top of the vendored `Zeta23` contour machinery — general infrastructure about an arbitrary function of a complex variable |
| [`RiemannHypothesis/LogModulusSegment.lean`](RiemannHypothesis/LogModulusSegment.lean) | the derivative of `log ‖f‖` along a segment is `re (f′/f)`, and the resulting fundamental theorem of calculus on the horizontal and vertical sides of a rectangle — the half of Littlewood's lemma that needs no branch of the logarithm |
| [`RiemannHypothesis/RectangleLogModulus.lean`](RiemannHypothesis/RectangleLogModulus.lean) | the four sides assembled: the increments of `log ‖f‖` telescope around the border, so the real part of the contour integral of `f′/f` vanishes and the normalized integral is real, assuming only analyticity and nonvanishing on the border |
| [`RiemannHypothesis/ArgumentSegment.lean`](RiemannHypothesis/ArgumentSegment.lean) | the argument half: a continuous branch of the argument of `g` along a segment, built by integrating `g′/g`, and hence the integrality of the winding number `(1/2πi) ∮_{∂R} f′/f` under nonvanishing on the border alone |
| [`RiemannHypothesis/LogDerivIntegrable.lean`](RiemannHypothesis/LogDerivIntegrable.lean) | `f′/f` is locally integrable even across the zeroes of `f`: near a zero it is bounded by `C/‖s − ρ‖`, which is integrable in two real dimensions |
| [`RiemannHypothesis/Littlewood.lean`](RiemannHypothesis/Littlewood.lean) | **Littlewood's lemma**: `2π ∑_ρ ord_ρ (re ρ − z.re)` as boundary data — the integral of `log ‖f‖` over the two vertical sides plus the increments of a continuous argument over the two horizontal sides |
| [`RiemannHypothesis/RectangleLogModulusZeros.lean`](RiemannHypothesis/RectangleLogModulusZeros.lean) | the modulus half of Littlewood's lemma with **no hypothesis on the border**: analyticity on an open neighbourhood, `f` nowhere locally zero, and finitely many zeroes in the rectangle suffice |
| [`RiemannHypothesis/ZetaRectangleCount.lean`](RiemannHypothesis/ZetaRectangleCount.lean) | the same machinery for `ζ` and `ξ`: the zeroes counted in a rectangle are the nontrivial zeroes of `ζ`, the count is finite unconditionally, `ζ` and `ξ` have the same multiplicities inside the strip, and the argument principle and Littlewood's counting identity for `ζ` itself |
| [`RiemannHypothesis/ZetaLittlewood.lean`](RiemannHypothesis/ZetaLittlewood.lean) | Littlewood's lemma for `ζ` itself, on a rectangle inside the open critical strip with no zero of `ζ` on its border, the sum being over the nontrivial zeroes inside |
| [`RiemannHypothesis/ZeroCount.lean`](RiemannHypothesis/ZeroCount.lean) | the Riemann–von Mangoldt *upper* bound: the zeroes of `ζ` in the critical strip with `\|im s\| ≤ T` are finite in number and at most `C·T·log T` |
| [`RiemannHypothesis/GammaVertical.lean`](RiemannHypothesis/GammaVertical.lean) | the exponential decay of `Γ` on vertical lines, `‖Γ(s)‖ ≤ 8(5+n+‖s‖)^{5+n} e^{−π\|im s\|/2}`, from the reflection formula and Phragmén–Lindelöf |
| [`RiemannHypothesis/ZeroCountLocal.lean`](RiemannHypothesis/ZeroCountLocal.lean) | the *local* Riemann–von Mangoldt bound: the zeroes of `ζ` in the critical strip with `\|im s − T\| ≤ 1` number at most `41 log T` for `T ≥ 25` |
| [`RiemannHypothesis/ZeroSum.lean`](RiemannHypothesis/ZeroSum.lean) | the nontrivial zeroes are countable, and the classical convergent sums over them: `∑_ρ 1/(1+γ²) < ∞` and `∑_ρ 1/‖ρ‖² < ∞` |
| [`RiemannHypothesis/ZeroExponent.lean`](RiemannHypothesis/ZeroExponent.lean) | the exponent of convergence of the zeroes is at most `1`: `∑_ρ ‖ρ‖^(−(1+e)) < ∞` for every `e > 0` |
| [`RiemannHypothesis/ZeroExponentOne.lean`](RiemannHypothesis/ZeroExponentOne.lean) | and it is exactly `1`: `∑_ρ 1/‖ρ‖` diverges |
| [`RiemannHypothesis/ZeroSumLogSq.lean`](RiemannHypothesis/ZeroSumLogSq.lean) | how fast it diverges: `∑_{0 < γ ≤ T} 1/‖ρ‖ ≍ (log T)²` |
| [`RiemannHypothesis/RvMCumulative.lean`](RiemannHypothesis/RvMCumulative.lean) | the Riemann–von Mangoldt asymptotic with its constant: `N(T) = (T/2π) log T + O(T)`, so `N(T)/(T log T) → 1/(2π)` |
| [`RiemannHypothesis/MultiplicityCountingLemma.lean`](RiemannHypothesis/MultiplicityCountingLemma.lean) | the Jensen-type bound on the *total order* of the zeroes in a disc: zeroes of total order `n` in the concentric disc of a quarter radius force `3^n ‖f c‖ ≤ M` |
| [`RiemannHypothesis/ZeroMultiplicityBound.lean`](RiemannHypothesis/ZeroMultiplicityBound.lean) | the multiplicity of a nontrivial zero is `O(log \|γ\|)`, and the counting function *with* multiplicity is `O(T log T)` |
| [`RiemannHypothesis/ZeroExists.lean`](RiemannHypothesis/ZeroExists.lean) | `ζ` really does have a zero in the open critical strip: an entire zero-free function is `exp` of a linear function (Borel–Carathéodory), which contradicts the factorial growth of `ξ` on the real axis |
| [`RiemannHypothesis/ZeroInfinite.lean`](RiemannHypothesis/ZeroInfinite.lean) | there are *infinitely many* such zeroes: an entire function with finitely many zeroes factors as a polynomial times a nowhere-vanishing exponential, and the same growth contradiction applies |
| [`RiemannHypothesis/ZeroCountLower.lean`](RiemannHypothesis/ZeroCountLower.lean) | the counting function is unbounded: the heights of the nontrivial zeroes are unbounded and `N(T) → ∞` |
| [`RiemannHypothesis/ZeroSymmetryCount.lean`](RiemannHypothesis/ZeroSymmetryCount.lean) | the zero set is stable under `s ↦ conj s` and `s ↦ 1 − s` and contains no real point, so each half-plane holds infinitely many zeroes and `N(T)` is even |
| [`RiemannHypothesis/OffLineQuadruple.lean`](RiemannHypothesis/OffLineQuadruple.lean) | the two symmetries generate the reflection `s ↦ 1 − conj s` in the critical line, so off-line zeroes come in quadruples and `4 ∣ N_off(T)` |
| [`RiemannHypothesis/ZeroMultiplicitySymmetry.lean`](RiemannHypothesis/ZeroMultiplicitySymmetry.lean) | the three symmetries preserve the multiplicity of a zero, so the counts *with multiplicity* are even, resp. divisible by four |
| [`RiemannHypothesis/DeBruijnNewman.lean`](RiemannHypothesis/DeBruijnNewman.lean) | the de Bruijn–Newman weight `Φ`, the family `H_t(z) = ∫_0^∞ e^{tu²}Φ(u)cos(uz)du` proved entire in `z`, the constant `Λ`, and the two literature statements around it (stated, not proved) |
| [`RiemannHypothesis/ThetaW.lean`](RiemannHypothesis/ThetaW.lean) | the theta series `ω(x) = ∑_{n≥1}e^{−πn²x}` and `W(u) = e^u ω(e^{4u})`: the functional equation `W(−u) = W(u) + sinh u`, hence `W'(0) = −1/2`, termwise double differentiation, the identity `Φ = (W''−W)/8`, and the decay estimates that make the cosine integrals converge |
| [`RiemannHypothesis/FourierXi.lean`](RiemannHypothesis/FourierXi.lean) | Riemann's integral representation `Ξ(z) = 1/2 − (4z²+1)∫_0^∞ W(u)cos(2uz)du`, and the resulting **unconditional** identification `H_0(z) = Ξ(z/2)/8`, so that `RH ↔ every zero of H_0 is real` |
| [`RiemannHypothesis/Partial.lean`](RiemannHypothesis/Partial.lean) | the known partial results (zero-free region, Hardy, Selberg/Conrey proportion, density theorem, numerical verification), stated as `Prop` and unproved |
| [`RiemannHypothesis/Zeta23Bridge.lean`](RiemannHypothesis/Zeta23Bridge.lean) | the counting functions `N`, `N_d`, `N₀*`, `N₀ˢ`, and the vendored `Zeta23` results restated here: `liminf N₀ˢ/N ≥ 2/3`, `liminf N_d/N ≥ 5/6`, the Montgomery–Taylor window, and the Dirichlet `L`-function versions |
| [`RiemannHypothesis/Zeta23Verification.lean`](RiemannHypothesis/Zeta23Verification.lean) | the two-thirds theorem in **absolute** form: the Riemann–von Mangoldt formula in these counting functions (`|N(T,2T) − (T/2π)(log(T/2π)+2log 2−1)| ≤ C log T`), hence `N(T,2T) ≥ (T/4π)log T`, hence at least `(T/8π)·log T` distinct — and as many simple — zeroes on the critical line with ordinate in `(T, 2T]` |
| [`RiemannHypothesis/Zeta23Sharp.lean`](RiemannHypothesis/Zeta23Sharp.lean) | the same with the **sharp** constant: `N(T,2T) ~ (T/2π) log T`, and for every `ε > 0` eventually at least `(2/3 − ε)(T/2π) log T` distinct (and as many simple) zeroes on the critical line, and `(5/6 − ε)(T/2π) log T` distinct zeroes, with ordinate in `(T, 2T]` |
| [`RiemannHypothesis/QuasiRiemann.lean`](RiemannHypothesis/QuasiRiemann.lean) | `ζ(s) ≠ 0` for `re s > 7/8`, and every nontrivial zero has real part in `[1/8, 7/8]` (absorbed from openai/math family 003; see [`docs/family003/README.md`](docs/family003/README.md)) |
| [`RiemannHypothesis/DirichletSevenEighths.lean`](RiemannHypothesis/DirichletSevenEighths.lean) | `L(s, χ) ≠ 0` for `re s > 7/8`, every Dirichlet character, away from the pole (family 003) |
| [`RiemannHypothesis/HeckeSevenEighths.lean`](RiemannHypothesis/HeckeSevenEighths.lean) | the same for the finite-order Hecke `L`-functions of `ℚ(√-3)` in the upstream character model, with the residue-character and ray-class corollaries (family 003) |
| [`RiemannHypothesis/SiegelZeroGap.lean`](RiemannHypothesis/SiegelZeroGap.lean) | an absolute `c > 0` with `c ≤ (1 − β) log q` for every real zero `β ∈ (0, 1)` of `L(s, χ)`, `χ` real, primitive, non-trivial mod `q ≥ 3` (family 003) |
| [`RiemannHypothesis/EventualCountingCriterion.lean`](RiemannHypothesis/EventualCountingCriterion.lean) | the hypothesis as an *eventual* counting statement: `RH ↔ N₀*(0,T) = N_d(0,T)` for all large `T`, so no separate verification of the low zeroes is needed — an off-line zero is missed by every window above its ordinate |
| [`RiemannHypothesis/CriticalLine.lean`](RiemannHypothesis/CriticalLine.lean) | **Hardy's theorem**: `ζ` has infinitely many zeroes on the critical line, and infinitely many *simple* ones; Selberg, Levinson and Conrey proportions in window form |
| [`RiemannHypothesis/CriticalLineOrdinates.lean`](RiemannHypothesis/CriticalLineOrdinates.lean) | the zeroes on the line are unbounded in *both* directions (also for simple zeroes), and `Ξ` has infinitely many real zeroes, bounded neither above nor below |
| [`RiemannHypothesis/OffLine.lean`](RiemannHypothesis/OffLine.lean) | the two-thirds theorem read from the other side: at most a third of the nontrivial zeroes lie *off* the critical line, `limsup N_off(T)/N(T) ≤ 1/3` |
| [`RiemannHypothesis/EightyPercent.lean`](RiemannHypothesis/EightyPercent.lean) | at least 80 % of the nontrivial zeroes of `ζ` are distinct (an `ε`-free corollary of `5/6`), and the `ξ'` counting functions with the `80 %`/`90 %` bounds for `ξ'` |
| [`RiemannHypothesis/EightyPercentSimple.lean`](RiemannHypothesis/EightyPercentSimple.lean) | at least 80 % of the *distinct* nontrivial zeroes of `ζ` are simple (`ε`-free, from the Montgomery–Taylor window), at least 92 % of the distinct zeroes of `ξ'` are simple, and the same 80 % for a primitive Dirichlet `L`-function |
| [`RiemannHypothesis/SixtySevenPercent.lean`](RiemannHypothesis/SixtySevenPercent.lean) | the Montgomery–Taylor constant satisfies `c₁* > 88/117`, giving the `ε`-free `0.67·N(T,2T) ≤ N₀*(T,2T)` on the critical line (and `N_off ≤ 0.33·N`), together with the quartic cosine bound `cos x ≤ 1 − x²/2 + x⁴/24` |
| [`RiemannHypothesis/EightyPercentRoute.lean`](RiemannHypothesis/EightyPercentRoute.lean) | the counting functions of the zeroes of `ζ` and of `ξ'` differ by `O(log T)` (proved), and — **conditionally** on the counting form of Speiser's theorem, recorded there as the unproved `Prop` `SpeiserTransfer` — at least 84 % of the *distinct* zeroes, and 70 % of the zeroes with multiplicity, lie on the critical line |
| [`RiemannHypothesis/SpeiserMultiple.lean`](RiemannHypothesis/SpeiserMultiple.lean) | the unconditional, local half of Speiser's transfer: `ξ` and `ζ` vanish to the same order in the strip, so `m_{ξ′}(ρ) + 1 = m_ζ(ρ)`; hence at most `13.136 %` of the zeroes of `ζ` are both multiple and off the critical line |
| [`RiemannHypothesis/EightyPercentMultiplicity.lean`](RiemannHypothesis/EightyPercentMultiplicity.lean) | the on-line/off-line split of the window count **with multiplicity**, the multiplicity-weighted transfer `SpeiserTransferMult`, and the conditional `73.7 %` / `86.864 %` bounds with multiplicity |
| [`RiemannHypothesis/CriticalLineXi.lean`](RiemannHypothesis/CriticalLineXi.lean) | Hardy's real function `Ξ(t) = ξ(1/2 + it)`, its reality and differentiability, and **Rolle's theorem on the critical line**: between two zeroes of `ξ` on the line there is a zero of `ξ′` on the line |
| [`RiemannHypothesis/SpeiserRolle.lean`](RiemannHypothesis/SpeiserRolle.lean) | the counting consequence, unconditionally: `N₀ᵐ(T₁,T₂) ≤ N₀ᵐ_{ξ′}(T₁,T₂) + 1` — with multiplicity, `ξ′` has at least as many zeroes on the critical line as `ζ` has, up to one |
| [`RiemannHypothesis/SpeiserEquivalence.lean`](RiemannHypothesis/SpeiserEquivalence.lean) | the off-line and on-line forms of the Speiser transfer are **equivalent**; the easy direction `N_offᵐ_{ξ′} ≤ N_offᵐ + O(log T)` is proved unconditionally, and the hypothesis already implies `86.864 %` of the zeroes of `ζ` on the critical line |
| [`RiemannHypothesis/SpeiserRH.lean`](RiemannHypothesis/SpeiserRH.lean) | the easy half of Speiser's theorem in quantitative form: the hypothesis implies that `ξ′` has `O(log T)` zeroes off the critical line in each dyadic window, and it implies the transfer `Prop` of the conditional route |
| [`RiemannHypothesis/PrimeNumberTheorem.lean`](RiemannHypothesis/PrimeNumberTheorem.lean) | **the prime number theorem**, proved: `ψ(x)/x → 1`, `θ(x)/x → 1`, `π(x)/(x/log x) → 1` |
| [`RiemannHypothesis/ExplicitFormula.lean`](RiemannHypothesis/ExplicitFormula.lean) | the smoothed Perron formula and **Weil's explicit formula** for `ζ` in test-function form |
| [`RiemannHypothesis/WeilPositivity.lean`](RiemannHypothesis/WeilPositivity.lean) | the Weil functional, the class of positive test functions, and the forward implication of **Weil's positivity criterion** (the hypothesis implies the positivity) |
| [`RiemannHypothesis/WeilTestFunctions.lean`](RiemannHypothesis/WeilTestFunctions.lean) | convolution squares `k = g ⋆ g^*` are positive test functions, their transform being `\|𝓕g\|²`; in particular the class is not reduced to `0` |
| [`RiemannHypothesis/MeanSquare.lean`](RiemannHypothesis/MeanSquare.lean) | the **mean value theorem** for an absolutely convergent Dirichlet series, and its specializations `(1/T) ∫₀ᵀ \|ζ(σ + i t)\|² dt → ζ(2σ)` and `(1/T) ∫₀ᵀ \|1/ζ(σ + i t)\|² dt → ∑ μ(n)² n^(−2σ)` for `σ > 1` |
| [`RiemannHypothesis/DirichletPolyMeanSquare.lean`](RiemannHypothesis/DirichletPolyMeanSquare.lean) | the mean square of a Dirichlet *polynomial*: the diagonal term `T ∑ \|a n\|² n^(−2σ)` plus off-diagonal terms `2\|a m\|\|a n\|(mn)^(−σ)/\|log(n/m)\|` |
| [`RiemannHypothesis/StripMeanSquare.lean`](RiemannHypothesis/StripMeanSquare.lean) | the mean square **inside the critical strip**: `∫₀ᵀ \|ζ(σ + i t)\|² dt = O_σ(T)` for `2/3 < σ < 1`, with the first moment and a large values estimate as consequences |
| [`RiemannHypothesis/StripMeanSquareTrapezoid.lean`](RiemannHypothesis/StripMeanSquareTrapezoid.lean) | the same bound for `3/5 < σ < 1`, by the first-order (trapezoidal) Euler–Maclaurin correction |
| [`RiemannHypothesis/StripMeanSquareBernoulli.lean`](RiemannHypothesis/StripMeanSquareBernoulli.lean) | the same bound for `4/7 < σ < 1`, by the second-order (`B₃`) Euler–Maclaurin correction |
| [`RiemannHypothesis/StripMeanSquareBohrLandau.lean`](RiemannHypothesis/StripMeanSquareBohrLandau.lean) | the same bound for **every** `1/2 < σ < 1`, by the Euler–Maclaurin expansion of arbitrary order |
| [`RiemannHypothesis/StripMeanSquareAsymptotic.lean`](RiemannHypothesis/StripMeanSquareAsymptotic.lean) | the mean square as an **asymptotic** with a power saving for `3/5 < σ < 1`: `(1/T) ∫₀ᵀ \|ζ(σ + i t)\|² dt → ζ(2σ)` |
| [`RiemannHypothesis/StripMeanSquareAsymptoticHalf.lean`](RiemannHypothesis/StripMeanSquareAsymptoticHalf.lean) | the same asymptotic, with a power saving, for every `1/2 < σ < 1` |
| [`RiemannHypothesis/StripMeanSquareUniform.lean`](RiemannHypothesis/StripMeanSquareUniform.lean) | the mean square with a constant **uniform in the abscissa**: one `C` serves every `σ ≥ σ₀ > 1/2` at once, which is what a circle average needs |
| [`RiemannHypothesis/ZetaCircleAverage.lean`](RiemannHypothesis/ZetaCircleAverage.lean) | the circle averages of `log \|ζ\|` about `3 + i y`, bounded by those of `\|ζ\|²/2` and integrated in `y` by Fubini: `∫ₐᵇ circleAverage (\|ζ\|²/2) (3 + i y) R dy = O_R(b)` |
| [`RiemannHypothesis/BohrLandau.lean`](RiemannHypothesis/BohrLandau.lean) | the **Bohr–Landau zero-density theorem** `N(σ, T) = O_σ(T)` for `σ > 1/2`, the Riemann–von Mangoldt lower bound `N(0, T) ≫ T log T`, and hence that almost all zeroes lie within `δ` of the critical line |
| [`RiemannHypothesis/LindelofDensity.lean`](RiemannHypothesis/LindelofDensity.lean) | **Backlund's criterion, the direction from growth to zeroes**: the Lindelöf hypothesis (recorded as a `Prop`) implies that for every fixed `σ > 1/2` a window of unit height at height `T` carries `o(log T)` zeroes with `re ρ ≥ σ`; the two-sided form follows by reflection, and the one-disc Jensen estimate against the maximum of `‖ζ‖`, together with the `O(log T)` comparison, is unconditional |
| [`RiemannHypothesis/ThreeCircles.lean`](RiemannHypothesis/ThreeCircles.lean) | **Hadamard's three-circles theorem**, transported from Mathlib's three-*lines* theorem along the exponential map: `log M(r)` is a convex function of `log r` for `f` analytic on a neighbourhood of a closed annulus |
| [`RiemannHypothesis/LindelofFromRH.lean`](RiemannHypothesis/LindelofFromRH.lean) | **Littlewood's theorem away from the critical line**: under the Riemann hypothesis, for every fixed `δ > 0` and `ε > 0`, `‖ζ(s)‖ ≤ C (im s)^ε` for `re s ≥ 1/2 + δ` and `im s` large, by Borel–Carathéodory on two discs about `3 + i t` and Hadamard's three circles |
| [`RiemannHypothesis/CriticalLineMeanSquare.lean`](RiemannHypothesis/CriticalLineMeanSquare.lean) | the first moment bounds **on** the critical line: `∫₀ᵀ \\|ζ(1/2 + i t)\\|² dt = O_ε(T^(1+ε))`, with the first moment and a large values estimate as consequences |
| [`RiemannHypothesis/VanDerCorput.lean`](RiemannHypothesis/VanDerCorput.lean) | **van der Corput's derivative tests for exponential integrals**: `‖∫ₐᵇ e^(iF)‖ ≤ 4/m` when `\\|F'\\| ≥ m` and `F'` is monotone, and `≤ 12/√r` when `F'' ≥ r`, both independent of `b − a` — the engine of the approximate functional equation and of the Weyl bound |
| [`RiemannHypothesis/KusminLandau.lean`](RiemannHypothesis/KusminLandau.lean) | **The Kusmin–Landau inequality**: the first-derivative test for exponential *sums*. `‖∑_{j ≤ K} e(f(c+j))‖ ≤ 1 + 2/λ` whenever `f'` is monotone and stays in `[k + λ, k + 1 − λ]` for one integer `k` — independent of `K`, by summation by parts against `1/(e(f') − 1)` and a telescoping cotangent |
| [`RiemannHypothesis/KusminLandauGeneral.lean`](RiemannHypothesis/KusminLandauGeneral.lean) | **Kusmin–Landau over a general range**: the same test when `f'` is monotone or antitone and at distance `≥ λ` from every integer but sweeps across arbitrarily many of them. Splitting the range into the blocks where `⌊f'⌋` is constant gives `‖∑_{j ≤ K} e(f(c+j))‖ ≤ (⌊f'(c+K)⌋ − ⌊f'(c)⌋ + 1)(1 + 2/λ) ≤ (V + 2)(1 + 2/λ)`, with `V = |f'(c+K) − f'(c)|` the total variation of the derivative |
| [`RiemannHypothesis/VanDerCorputSums.lean`](RiemannHypothesis/VanDerCorputSums.lean) | **van der Corput's second-derivative test for exponential *sums***: if `f'` increases at speed at least `r` on `[a, a+L]` then `‖∑_{j<L} e(f(a+j))‖ ≤ 2(V+2)((1+2/λ) + (2λ/r+1))` with `V = f'(a+L) − f'(a)`; balancing at `λ = √r/2` and feeding in `r ≤ f'' ≤ R` gives `≤ 2(RL+2)(2 + 5/√r)`, the classical `≪ L√r + 1/√r`. The range is split by the position of `f'` relative to the integers: Kusmin–Landau on the good blocks, a trivial count on the `2λ/r + 1` indices near each integer |
| [`RiemannHypothesis/WeylDifferencing.lean`](RiemannHypothesis/WeylDifferencing.lean) | **van der Corput's A process (Weyl differencing)**: `H ‖∑ z‖² ≤ (N + H − 1) ∑_{\\|k\\| < H} ‖corr z k‖` for a sequence supported in `[0, N)`, the weighted (Fejér) form with `H − \\|k\\|`, and the arithmetic form bounding `∑ e(f(n))` by its differenced sums `∑ e(f(n+k) − f(n))` |
| [`RiemannHypothesis/WeylQuadratic.lean`](RiemannHypothesis/WeylQuadratic.lean) | **Weyl's bound for a quadratic exponential sum**: the differenced phase of `α n²` is linear, so the differenced sums are geometric series, `‖∑_{j<M} e(θj + c)‖ ≤ 1/(2‖θ‖)`; if `‖2αk‖ ≥ δ` for `0 < k < H` then `‖∑_{n<N} e(α n²)‖² ≤ (N + H − 1)(N + (H−1)/δ)/H` — square-root cancellation against the trivial `N²` |
| [`RiemannHypothesis/WeylEquidistribution.lean`](RiemannHypothesis/WeylEquidistribution.lean) | **Cancellation in quadratic Weyl sums**: for `α` irrational the multiples `2αk`, `0 < k < H`, are uniformly away from the integers, so Weyl's inequality applies with an explicit constant and `‖∑_{n<N} e(α n²)‖ / N → 0` — the family of estimates Weyl's criterion asks for |
| [`RiemannHypothesis/WeylQuadraticQuantitative.lean`](RiemannHypothesis/WeylQuadraticQuantitative.lean) | **the diophantine input to Weyl's inequality, and an explicit rate**: a fraction with denominator `q` that is not an integer is at distance at least `1/q` from `ℤ`, and `θ ↦ ‖θ‖` is `1`-Lipschitz, so a rational approximation `|2α − a/q| ≤ 1/q²` with `gcd(a,q) = 1` forces `‖2αk‖ ≥ 1/(2q)` for all `0 < 2k ≤ q`; taking `H = q/2` in the previous module gives `‖∑_{n<N} e(α n²)‖² ≤ 4(N+q)(N+q²)/q`, and a denominator `q` of the size of `√N` gives the effective bound **`‖∑_{n<N} e(α n²)‖ ≤ 7 N^(3/4)`** |
| [`RiemannHypothesis/WeylMinSum.lean`](RiemannHypothesis/WeylMinSum.lean) | **the counting lemma of Weyl's method, and the exponent `1/2`**: with `|β − a/q| ≤ 1/q²` and `gcd(a,q) = 1`, the multiples `βk` over a block of `q` consecutive integers land, up to one grid step, on the `q` points of a progression of step `1/q`, so `∑_{0 < k ≤ H} min(N, 1/(2‖βk‖)) ≤ (H/q + 1)(4N + q(1 + log q))`; this lets the differencing run to `H = N` instead of `H = q/2`, and a denominator `N ≤ q ≤ 2N` gives **`‖∑_{n<N} e(α n²)‖ ≤ 9 √(N(1 + log 2N))`** |
| [`RiemannHypothesis/WeylBadlyApproximable.lean`](RiemannHypothesis/WeylBadlyApproximable.lean) | **an unconditional rate, for a badly approximable coefficient**: Dirichlet's theorem gives a coprime `a/q` with `q ≤ N` and `|2α − a/q| ≤ 1/(q(N+1))`, and if `|2α − a/q| ≥ c/q²` always holds then that forces `q ≥ c(N+1)`, so the denominator is automatically large and the previous module applies with no hypothesis left to the caller: `‖∑_{n<N} e(α n²)‖ ≤ √((16/c + 26) N(1 + log N))`.  every quadratic irrational is badly approximable, by Liouville's argument, and `√2` is so with `c = 1/4`, giving **`‖∑_{n<N} e((√2/2) n²)‖ ≤ √(90 N(1 + log N))`** |
| [`RiemannHypothesis/WeylCubic.lean`](RiemannHypothesis/WeylCubic.lean) | **Weyl's bound for a cubic exponential sum**: the A process iterated twice.  the first differencing turns `α n³` into a quadratic phase, the second turns that into the linear phase `(6αkl)n`, and the pairs `(k,l)` are folded onto `m = kl` so that the counting lemma of the previous module applies; with `H = ⌊√N⌋ + 1` and a coprime `|6α − a/q| ≤ 1/q²`, `q ≤ 4N`, this gives **`‖∑_{n<N} e(α n³)‖⁸ ≤ 2²² (4N/q + 1)² N⁷ (1 + log 4N)²`**, and for `6α` badly approximable the unconditional form, e.g. **`‖∑_{n<N} e((√2/6) n³)‖⁸ ≤ 2³¹ N⁷ (1 + log 4N)²`**.  the exponent is `7/8`, not the classical `3/4` |
| [`RiemannHypothesis/WeylGeneral.lean`](RiemannHypothesis/WeylGeneral.lean) | **Weyl's inequality in arbitrary degree**: the A process iterated `d − 1` times.  `weylMulti` is the `r`-fold shifted majorant sum and `IsPolyPhase.diff` says that differencing lowers the degree by one; induction on `d` gives **`‖∑_{n<N} e(f n)‖^{2^{d−1}} H^{d−1}(N+H) ≤ 8^{2^{d−1}} (N+H)^{2^{d−1}} W_{d−1}(d! α)`** for every polynomial phase `f` of degree `d`, and folding the tuples of shifts onto their product feeds the same counting lemma, giving **`‖∑_{n<N} e(α n^d)‖^{2^{d−1}} H ≤ 16^{2^{d−1}} N^{2^{d−1}} (d + 9 + 2 log N)`** whenever `H^{d−1} ≤ q ≤ N`.  the exponent is `1 − 1/((d−1)2^{d−1})`, not the classical `1 − 1/2^{d−1}` |
| [`RiemannHypothesis/WeylCriterion.lean`](RiemannHypothesis/WeylCriterion.lean) | **Weyl's criterion and equidistribution of `α n²`**: a sequence is equidistributed modulo one (averages of continuous functions on `ℝ/ℤ` converge to the mean) iff `‖∑_{n<N} e(m xₙ)‖/N → 0` for every nonzero integer `m`; combined with the quadratic Weyl bound, the fractional parts of `α n²` are equidistributed for every irrational `α` |
| [`RiemannHypothesis/WeylCount.lean`](RiemannHypothesis/WeylCount.lean) | **Equidistribution in its counting form**: squeezing the indicator of `[a, b) ⊆ (0,1)` between trapezoids on the circle turns the test-function statement into `#{n < N : {xₙ} ∈ [a,b)} / N → b − a`, and hence Weyl's theorem for `α n²` with `α` irrational in its classical form |
| [`RiemannHypothesis/WeylCountGeneral.lean`](RiemannHypothesis/WeylCountGeneral.lean) | **the counting form for an arbitrary subinterval of `[0,1]`**: equidistribution is invariant under translation, so rotating an interval that meets the glueing point `0` into `(0,1)` removes the restriction `0 < a < b < 1`, giving `#{n < N : {xₙ} ∈ [a,b)} / N → b − a` for all `0 ≤ a < b ≤ 1` |
| [`RiemannHypothesis/WeylLinear.lean`](RiemannHypothesis/WeylLinear.lean) | **Weyl's theorem for the linear sequence `α n`**: the exponential sum at a nonzero frequency is geometric, so the bound `1/(2‖mα‖)` is uniform in `N`; hence the fractional parts of `α n` are equidistributed for every irrational `α`, and `#{n < N : {α n} ∈ [a,b)} / N → b − a` for all `0 ≤ a < b ≤ 1` |
| [`RiemannHypothesis/WeylCountArc.lean`](RiemannHypothesis/WeylCountArc.lean) | **the counting form for an arbitrary arc of the circle**: the wrap-around arc `[a,1) ∪ [0,b)` with `b ≤ a` splits into two disjoint intervals, so `#{n < N : {xₙ} ∈ [a,1) ∪ [0,b)} / N → (1 − a) + b`; with the previous module this covers every arc of `ℝ/ℤ` |
| [`RiemannHypothesis/WeylPortmanteau.lean`](RiemannHypothesis/WeylPortmanteau.lean) | **Weyl's criterion in its counting form**: the converse of the two previous modules — if `#{n < N : {xₙ} ∈ [a,b)} / N → b − a` for *every* subinterval of `[0,1]` then every exponential sum vanishes, by cutting `[0,1)` into `K > |m|` equal cells, replacing each phase by its value at the left endpoint of its cell (an error of at most `2π|m|/K` per term) and using that the mean of `e(m ·)` over the `K`-th roots of unity is `0`; hence equidistribution, the vanishing of the exponential sums and the counting statement are equivalent, and the criterion is available with no test function and no measure |
| [`RiemannHypothesis/WeylDiscrepancy.lean`](RiemannHypothesis/WeylDiscrepancy.lean) | **A rate of convergence for equidistribution modulo one**, an inequality of Erdős–Turán type: with the Fejér-type kernel `K_M(t) = |∑_{j<M} e(tj)|²/M`, of mass one and with tail `≤ 1/(2Mδ)` outside `[−δ,δ]`, a `1`-periodic `L`-Lipschitz test function with values in `[0,1]` satisfies `|(1/N)∑_{n<N} g(xₙ) − ∫₀¹ g| ≤ Lδ + 1/(2Mδ) + 2∑_{m<M} ‖∑_{n<N} e(m xₙ)‖/N`; squeezing the indicator of `[a,b)` between two trapezoids gives `|#{n<N : {xₙ} ∈ [a,b)}/N − (b−a)| ≤ 4/K + 2∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N`, and for a badly approximable `α` an explicit rate `O(N^(−1/9))` for the sequence `α n` |
| [`RiemannHypothesis/WeylDiscrepancyGeneral.lean`](RiemannHypothesis/WeylDiscrepancyGeneral.lean) | **The discrepancy bound for every subinterval of `[0,1]`**: the inequality of the previous module is proved with no condition on the position or the length of `[a,b)`, so its left-hand side is the discrepancy itself — `|#{n<N : {xₙ} ∈ [a,b)}/N − (b−a)| ≤ 20/K + 4∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N` for `K ≥ 8`, `N ≥ 1` and every `0 ≤ a ≤ b ≤ 1`. Three devices: a rotation, which multiplies each exponential sum by a unimodular factor and centres the interval in `(0,1)`; an enlargement of the short intervals, which only increases the count; and the complement identity `#[0,a) + #[a,b) + #[b,1) = N` for the intervals too long to be enlarged. The rates `O(N^(−1/9))` for `α n` and the quadratic rate for `α n²` with `2α` badly approximable are carried over to all intervals |
| [`RiemannHypothesis/Discrepancy.lean`](RiemannHypothesis/Discrepancy.lean) | **The discrepancy, and a power saving for `α n`**: `D_N(x) = sup_{0 ≤ a ≤ b ≤ 1} |#{n<N : {xₙ} ∈ [a,b)}/N − (b−a)|`, the supremum of a nonempty set bounded by `1`; the constant sequence `0` has `D_N ≥ 1/2`, so the definition is not vacuous. The Erdős–Turán inequality of the previous module reads `D_N ≤ 20/K + 4∑_{m<K⁴} ‖∑_{n<N} e(m xₙ)‖/N`, and the choice `K = ⌊N^(1/9)⌋` turns it, for a badly approximable `α`, into `D_N(α n) ≤ 2(20 + 2/c) N^(−1/9)` for `N ≥ 8⁹`, hence `D_N(α n) → 0` |
| [`RiemannHypothesis/DiscrepancyCriterion.lean`](RiemannHypothesis/DiscrepancyCriterion.lean) | **Weyl's criterion in discrepancy form**: a sequence is equidistributed modulo one exactly when `D_N → 0`. The forward direction is not a repackaging of the pointwise limits — a supremum of infinitely many null sequences need not be null — but follows from the uniform Erdős–Turán inequality: choose `K` with `20/K < ε/2` first, then pass to the limit in the remaining `K⁴ − 1` exponential sums. Corollaries: `D_N(α n²) → 0` for every irrational `α`, and the constant sequence `0`, with `D_N ≥ 1/2`, shows the criterion separates sequences |
| [`RiemannHypothesis/Koksma.lean`](RiemannHypothesis/Koksma.lean) | **Koksma's inequality**: the discrepancy is what controls numerical integration along the sequence — `|(1/N)∑_{n<N} f({xₙ}) − ∫₀¹ f| ≤ (f 1 − f 0)·D_N(x)` for a nondecreasing `f` (no continuity required — jumps are allowed), `≤ ((g 1 − g 0)+(h 1 − h 0))·D_N(x)` for a difference `f = g − h` of two such, and `≤ 3L·D_N(x)` for an `L`-Lipschitz `f`. Quantitative, no limit taken: the proof cuts `[0,1)` into `K` cells, sandwiches both the average and the integral between the step sums and the Riemann sums built from the cell endpoints, and applies summation by parts to the cell deviations, whose tails are exactly the interval deviations bounded by `D_N`; the boundary terms vanish because the full interval and the empty interval have deviation `0`. Corollaries: a sequence of vanishing discrepancy integrates every monotone function correctly, in particular `α n²` for irrational `α` |
| [`RiemannHypothesis/KoksmaVariation.lean`](RiemannHypothesis/KoksmaVariation.lean) | **Koksma's inequality with the total variation**: with `V(f) = (eVariationOn f [0,1]).toReal`, every integrand of bounded variation on `[0,1]` — no continuity, no chosen decomposition — satisfies `|(1/N)∑_{n<N} f({xₙ}) − ∫₀¹ f| ≤ (2V(f) − |f 1 − f 0|)·D_N(x)`, in particular `≤ 2V(f)·D_N(x)`. Proved by feeding the two Jordan decompositions `f = V_f − (V_f − f)` and `f = (V_f + f) − V_f` into the difference form of Koksma's inequality; for a nondecreasing `f` the constant is exactly `f 1 − f 0 = V(f)`. The Lipschitz constant improves from `3L` to `2L`, and every sequence of vanishing discrepancy integrates *every* function of bounded variation correctly in the limit. The sharp constant `V(f)` is not obtained — it needs Riemann–Stieltjes integration by parts |
| [`RiemannHypothesis/KoksmaSharp.lean`](RiemannHypothesis/KoksmaSharp.lean) | **Koksma's inequality for a Lipschitz integrand, with the sharp constant**: `|(1/N)∑_{n<N} f({xₙ}) − ∫₀¹ f| ≤ L·D_N(x)` for every `L`-Lipschitz `f` on `[0,1]`, replacing the `3L` of `Koksma.lean` and the `2L` of `KoksmaVariation.lean`. The proof drops the detour through monotone functions: the summation-by-parts step is proved for an arbitrary weight sequence (`abs_sum_weight_cellDev_le`, with `∑_j |a_{j+1} − a_j|` in place of a rise), and the two discretisation errors — average versus cell-step average, integral versus Riemann sum — are each at most `L/K`, so the error is `≤ L·D_N(x) + 2L/K` for every `K ≥ 1` |
| [`RiemannHypothesis/VanDerCorputSequence.lean`](RiemannHypothesis/VanDerCorputSequence.lean) | **An explicit sequence of low discrepancy**: the van der Corput sequence `vdc n`, the base-two radical inverse (`0, 1/2, 1/4, 3/4, 1/8, 5/8, 3/8, 7/8, …`), satisfies `D_N(vdc) ≤ 2 (log₂ N + 1)/N` for every `N ≥ 1` — the logarithmic rate, against the `N^(−1/9)` of `Discrepancy.lean`. The proof is combinatorial: the first `j` binary digits of `vdc n` are the lowest `j` digits of `n` reversed, so on *any* `2^j` consecutive indices each dyadic cell of length `2^(−j)` receives exactly one point; cutting a block of `N` indices along the binary digits of `N` gives a counting error at most `log₂ N + 1`. Hence `D_N(vdc) → 0`, and with the Koksma inequalities the quadrature error of an `L`-Lipschitz integrand at these points is at most `L·2(log₂ N + 1)/N`. In the other direction, every sequence satisfies `D_N ≥ 1/(2N)` (pigeonhole on the `2N` cells of length `1/(2N)`), so the rate is optimal up to the logarithm; the sharp optimality (Schmidt's theorem) is not proved |
| [`RiemannHypothesis/WeylDifferenceTheorem.lean`](RiemannHypothesis/WeylDifferenceTheorem.lean) | **van der Corput's difference theorem**: the A process, restated for a sequence indexed by `ℕ`, gives `H ‖∑_{n<N} e(m xₙ)‖² ≤ (N + H − 1)(N + 2 ∑_{k=1}^{H−1} ‖∑_{n<N−k} e(m (x(n+k) − xₙ))‖)`, and hence: if every difference sequence `n ↦ x(n+k) − xₙ`, `k ≥ 1`, is equidistributed modulo one, then so is `x` |
| [`RiemannHypothesis/WeylPolynomial.lean`](RiemannHypothesis/WeylPolynomial.lean) | **Weyl's theorem for an arbitrary polynomial**: the forward difference `p(X+k) − p(X)` has degree `d − 1` and leading coefficient `d·a_d·k` (computed through the Hasse derivatives), so induction on the degree with the difference theorem shows that `n ↦ p(n)` is equidistributed modulo one whenever `deg p ≥ 1` and `a_d` is irrational; with the counting form `#{n < N : {p(n)} ∈ [a,b)} / N → b − a`, and the special case `α n^d` |
| [`RiemannHypothesis/WeylPolynomialGeneral.lean`](RiemannHypothesis/WeylPolynomialGeneral.lean) | **Weyl's exact criterion for a polynomial sequence**: gluing arithmetic progressions (`x` is equidistributed as soon as each `k ↦ x(vk+r)`, `r < v`, is) and invariance under an integer shift, a strong induction on the degree removes the hypothesis that the *leading* coefficient be irrational — if `a_d = u/v` is rational then along `n = vm+r` the top term is constant modulo one and the degree drops; hence `n ↦ p(n)` is equidistributed modulo one **iff** some coefficient `a_j` with `j ≥ 1` is irrational, the converse being the periodicity of `p` modulo one when all of them are rational |
| [`RiemannHypothesis/SqrtHarmonic.lean`](RiemannHypothesis/SqrtHarmonic.lean) | the two elementary square-root sums used by the approximate functional equation and by the third-derivative test: `∑_{1 ≤ n ≤ N} 1/√n ≤ 2√N` and `∑_{n < N} √n ≤ N√N` |
| [`RiemannHypothesis/ZetaChi.lean`](RiemannHypothesis/ZetaChi.lean) | **the `χ` factor of the functional equation**: `χ(s) = 2(2π)^(s−1) Γ(1−s) sin(πs/2)` with `ζ(s) = χ(s) ζ(1−s)`, `χ(s̄) = conj χ(s)`, `χ(s)χ(1−s) = 1`, and hence **`‖χ(1/2+it)‖ = 1`** — the reason the two Dirichlet polynomials of the approximate functional equation contribute equally |
| [`RiemannHypothesis/ApproximateFunctionalEquation.lean`](RiemannHypothesis/ApproximateFunctionalEquation.lean) | the Dirichlet polynomials `∑_{n ≤ N} n^(−s)` and `∑_{n ≤ N} n^(s−1)`, their conjugacy and trivial bound `2√N` on the critical line, and **the approximate functional equation recorded as a `Prop`** `AFECriticalLine C` (a classical theorem of Hardy–Littlewood, not proved in this file; proved with `C = 250` in `AFECriticalLineProof.lean`); from it, the convexity bound `‖ζ(1/2+it)‖ ≤ (C+4) t^(1/4)` |
| [`RiemannHypothesis/VanDerCorputThird.lean`](RiemannHypothesis/VanDerCorputThird.lean) | **van der Corput's third-derivative test**, the composition of the A process with the second-derivative test: the differenced phase `f(·+k) − f(·)` has second derivative `≍ k f'''`, so `H‖∑_{n<N} e(f(a+n))‖² ≤ (N+H)(N + 8RNH² + 16H + 20RNH√H/√r + 80√H/√r)` when `r ≤ f''' ≤ R` and `Hr ≤ 1` — the exponent pair `(1/6, 2/3)` |
| [`RiemannHypothesis/AFESubconvexity.lean`](RiemannHypothesis/AFESubconvexity.lean) | **the exponent `1/6`**: the third-derivative test applied to the phase `−(t/2π) log x` on a block, Abel summation against the weight `n^(−1/2)`, and a dyadic decomposition give the *unconditional* `‖∑_{n ≤ N} n^(−1/2−it)‖ ≤ 60 t^(1/6)(log₂N + 1)` for `N ≤ √t`; conditionally on `AFECriticalLine C` this is the Hardy–Littlewood subconvexity bound `‖ζ(1/2+it)‖ ≤ C + 120 t^(1/6)(log t + 1)` |
| [`RiemannHypothesis/SubconvexityUnconditional.lean`](RiemannHypothesis/SubconvexityUnconditional.lean) | **the exponent `1/6`, unconditionally**: `‖ζ(1/2+it)‖ ≤ 200 t^(1/6)(log t + 1)` for `t ≥ 10⁹`, with no hypothesis.  The approximate functional equation is not needed if the Dirichlet polynomial is taken of length `t²` — the Euler–Maclaurin error is then `O(1)` — and every dyadic block of it is bounded: the third-derivative test up to `t^(2/3)`, the second-derivative test up to `2t`, and Kusmin–Landau beyond, where the phase derivative `t/2πx` is itself the distance to the nearest integer |
| [`RiemannHypothesis/SubconvexityStrip.lean`](RiemannHypothesis/SubconvexityStrip.lean) | **the exponent `(1−σ)/3` inside the strip**: the same blocks, with the weight `n^(−σ)` in place of `n^(−1/2)`, give `‖ζ(σ+it)‖ ≤ 400 t^((1−σ)/3)(log t + 1)` for `1/2 ≤ σ ≤ 1` and `t ≥ 10⁹`, unconditionally — for `σ > 1/2` a fixed power of `t` better than the convexity bound `t^((1−σ)/2)` |
| [`RiemannHypothesis/HalaszMontgomery.lean`](RiemannHypothesis/HalaszMontgomery.lean) | **the Halász–Montgomery inequality**: if `Δ` bounds every Gram row sum `∑_j ‖⟪φ i, φ j⟫‖` then `∑_i ‖⟪φ i, ξ⟫‖² ≤ Δ‖ξ‖²`, in coordinates and in a Hilbert space; specialized to `n ↦ n^(it)` it gives `∑_i \|D(t_i)\|² ≤ Δ ∑_{n ≤ N} \|a_n\|²` for a Dirichlet polynomial and the **large-values count** `R ≤ Δ‖a‖²/V²`; with a **ceiling**: the orthonormal configuration attains the inequality, so no constant better than `1` is admissible |
| [`RiemannHypothesis/LargeSieve.lean`](RiemannHypothesis/LargeSieve.lean) | **the large sieve inequality**: for points pairwise `δ`-separated modulo one, `∑_i \|∑_{n<N} a_n e(n t_i)\|² ≤ (N + δ⁻¹(1 + log (2δ)⁻¹)) ∑_n \|a_n\|²`, by the Halász–Montgomery bound applied to the Dirichlet kernel, whose row sums are controlled by Jordan's inequality `2‖θ‖ ≤ \|sin πθ\|` and a bucket injection; the sharp constant `N + δ⁻¹` needs Selberg's majorant and is not claimed; with a **ceiling**: every admissible constant is at least `max N (2δ)⁻¹`, so both terms are necessary; the logarithm is removed in [`LargeSieveGallagher.lean`](RiemannHypothesis/LargeSieveGallagher.lean) |
| [`RiemannHypothesis/LargeSieveGallagher.lean`](RiemannHypothesis/LargeSieveGallagher.lean) | **the large sieve inequality, Gallagher's form**, which removes the logarithm: `∑_i \|∑_{n<N} a_n e(n t_i)\|² ≤ (δ⁻¹ + π N) ∑_n \|a_n\|²` for pairwise `δ`-separated points, by Gallagher's lemma (a window average against the derivative, with the cross term kept) applied to the exponential polynomial recentred at `c = (N−1)/2`, whose Parseval identity and derivative mean square `≤ (π N)² ∑ \|a_n\|²` are proved here; only the factor `π` separates this from the sharp `δ⁻¹ + N` |
| [`RiemannHypothesis/LargeSieveFarey.lean`](RiemannHypothesis/LargeSieveFarey.lean) | **the arithmetic large sieve**: two distinct rationals in `[0,1)` with denominators at most `Q` differ by a nonzero rational of denominator at most `Q²`, hence are `Q⁻²`-separated modulo one, so the Gallagher form gives `∑_{q ≤ Q} ∑*_{b mod q} \|∑_{n<N} a_n e(n b/q)\|² ≤ (Q² + π N) ∑_n \|a_n\|²`; the character form, which needs Gauss sums, is not claimed |
| [`RiemannHypothesis/LargeSieveDual.lean`](RiemannHypothesis/LargeSieveDual.lean) | **the dual large sieve**, and the **duality principle** behind it: for a finite matrix, a bound `∑_i \|∑_n a_n φ_{i,n}\|² ≤ C ∑_n \|a_n\|²` transfers to the adjoint, `∑_n \|∑_i x_i conj(φ_{i,n})\|² ≤ C ∑_i \|x_i\|²`, by exchanging the order of summation and applying Cauchy–Schwarz to the vector it produces; hence `∑_{n<N} \|∑_i x_i e(n t_i)\|² ≤ (δ⁻¹ + π N) ∑_i \|x_i\|²` at `δ`-separated points, and `Q² + π N` at Farey fractions of order `Q` |
| [`RiemannHypothesis/LargeSieveSifted.lean`](RiemannHypothesis/LargeSieveSifted.lean) | **the large sieve for sifted sets**: with the indicator of `A ⊆ [0,N)` as coefficients, orthogonality of the additive characters gives Parseval, `∑_{b<q} ‖∑_{n∈A} e(nb/q)‖² = q ∑_r (#{n ∈ A : n ≡ r})²`, whose `b = 0` term is `\|A\|²`; Cauchy–Schwarz over the classes met bounds the reduced sums from below, and comparing with the Farey large sieve over the primes `p ≤ Q` gives **Montgomery's inequality `\|A\| ∑_{p≤Q} (p − ω_p)/ω_p ≤ Q² + π N`** — so a set meeting at most half the classes modulo every prime `p ≤ Q` has `\|A\| #{p ≤ Q} ≤ Q² + π N`, and the squares, which meet `(p+1)/2` classes, satisfy the sieve hypothesis |
| [`RiemannHypothesis/Mollifier.lean`](RiemannHypothesis/Mollifier.lean) | **mollifier zero detection**: with `M_y(s) = ∑_{n ≤ y} μ(n) n^(−s)`, the coefficients of `ζ M_y` are `c_n = ∑_{d ∣ n, d ≤ y} μ(d)`, which vanish for `2 ≤ n ≤ y`, so `ζ(s)M_y(s) = 1 + ∑_{n>y} c_n n^(−s)` for `re s > 1` — a zero of `ζ` forces the tail, which has no short terms, to equal `−1`; the same identity is also given in a finite form valid for **every** `s` |
| [`RiemannHypothesis/MollifiedZetaMeanSquare.lean`](RiemannHypothesis/MollifiedZetaMeanSquare.lean) | **the mollified mean square inside the strip**: `∫_a^b \|ζ M_y − 1\|² dt ≤ ε b` for a mollifier length `y = y(ε)`, uniformly for `σ₀ ≤ σ ≤ 6` with `σ₀ > 1/2`; the truncation `ζ ≈ ∑_{k ≤ K} k^(−s)` is taken as long as `K = ⌈b^α⌉` with `α > 1`, which is affordable only because the mean value theorem of `GaussianMeanValue.lean` keeps its error term inside the sum |
| [`RiemannHypothesis/MollifiedZetaCircle.lean`](RiemannHypothesis/MollifiedZetaCircle.lean) | the same bound on **circles**, which is what Jensen's counting inequality consumes, together with `\|ζ M_y − 1\| ≤ 1/y` on `re s ≥ 3` and the majorant `log \|z\| ≤ (λ/2)\|z − 1\|² + 1/(2λ)` whose additive constant, unlike `log x ≤ x²/2`, can be made arbitrarily small |
| [`RiemannHypothesis/CarlsonDensity.lean`](RiemannHypothesis/CarlsonDensity.lean) | **Carlson's density theorem `N(σ, T) = o(T)`**, the mollified form of the Bohr–Landau counting argument, and with it the `Prop` `AlmostAllZerosNearCriticalLine` of `Partial.lean`; the power saving `O(T^{4σ(1−σ)} log T)` is *not* claimed |
| [`RiemannHypothesis/CarlsonPowerSaving.lean`](RiemannHypothesis/CarlsonPowerSaving.lean) | the same mean squares **with an explicit rate**, for a mollifier length that may grow with the height: `∫_a^b ‖ζ M_y − 1‖² ≤ C (b y^{−(σ₀−1/2)} + b^{1−c})` whenever `y ≤ 4 b^γ`, and its circle-average form |
| [`RiemannHypothesis/CarlsonDensityPowerSaving.lean`](RiemannHypothesis/CarlsonDensityPowerSaving.lean) | **the power saving `N(σ, T) = O(T^{1−(σ−1/2)²/64})`**, obtained by running the Jensen counting inequality with `y = ⌈T^γ⌉` and `λ = T^{c'}` and tracking every exponent in `θ = σ₀ − 1/2`; the exponent is explicit and degrades to `0` as `σ ↓ 1/2`, but the constant is not effective and the saving is `256` times worse than Carlson's `4(σ−1/2)²` |
| [`RiemannHypothesis/MethodCeiling.lean`](RiemannHypothesis/MethodCeiling.lean) | **the ceilings of the counting routes, as theorems**: a proportion `p` is derivable from the budgets `N_d ≥ c·N`, `N_off ≤ b·N` if and only if `p ≤ c − b`, and from `N_offᵐ ≤ b·N` if and only if `p ≤ 1 − b`; with the repository's own constants this reproduces its `70.197 %` and `86.864 %` exactly, and shows `80 %` is not derivable on the first route |
| [`RiemannHypothesis/CorpusCeiling.lean`](RiemannHypothesis/CorpusCeiling.lean) | **the ceiling of the whole corpus, as theorems**: `ZeroCorpus θ` collects every unconditional fact this repository proves about the counting functions — the mollifier proportion, the Riemann–von Mangoldt formula, the Carlson power saving, the quadruple symmetry, the `O(log γ)` multiplicity bound, the classical zero-free region — and `corpus_window_ceiling` proves that the best proportion on the critical line derivable from all of them together is exactly `1 − θ`, the `67 %` already proved; `rh_not_derivable_from_corpus` and `density_not_sufficient` exhibit a configuration satisfying every one of those facts, with boundedly many off-line zeroes at each fixed distance `δ` from the critical line, in which a positive proportion of the zeroes is off the line |
| [`RiemannHypothesis/CorpusInstance.lean`](RiemannHypothesis/CorpusInstance.lean) | **the corpus of `ζ`**: `zetaCorpus : ZeroCorpus 0.33` builds the constraint system of `CorpusCeiling.lean` out of the repository's own counting functions of `ζ`, every field discharged from a theorem about the zeroes (additivity of the window counts, the evenness of the off-line count under `ρ ↦ 1 − ρ̄`, the cumulative `O(log T)` multiplicity bound, the classical zero-free region in counting form); `zetaStripForm_iff_rhCounts_zetaCorpus` identifies the Riemann hypothesis with the vanishing of the corpus's off-line count, and `rh_not_derivable_from_zeta_corpus` records the resulting independence statement relative to the formalized corpus |
| [`RiemannHypothesis/CorpusRich.lean`](RiemannHypothesis/CorpusRich.lean) | **a thicker corpus**: `RichZeroCorpus` extends `ZeroCorpus` by four further unconditional facts — the simple-and-on-the-line count with its `67 %`, Theorem C's `N_d ≥ (5/6 − ε) N`, the local Riemann–von Mangoldt bound `N(T+1) − N(T) = O(log T)`, and the containment of every zero in the open critical strip — and `rich_corpus_window_ceiling` shows the ceiling is still exactly `1 − θ` |
| [`RiemannHypothesis/CorpusRichInstance.lean`](RiemannHypothesis/CorpusRichInstance.lean) | **the thicker corpus of `ζ`**: `zetaRichCorpus : RichZeroCorpus 0.33`, every field discharged from a theorem about the zeroes, and `rh_not_derivable_from_zeta_rich_corpus` — the enlarged list of facts still does not entail the Riemann hypothesis |
| [`RiemannHypothesis/MeanValueWellSpaced.lean`](RiemannHypothesis/MeanValueWellSpaced.lean) | **the mean value theorem for well-spaced frequencies**: `∫₋ᵀᵀ ‖∑_r x_r e^{i λ_r t}‖² dt ≤ 18 (T + 1/δ) ∑ ‖x_r‖²` for `δ`-separated real frequencies, by the Gaussian majorant method — the estimate for which the literature uses Montgomery and Vaughan's generalized Hilbert inequality, with an explicit but non-optimal constant |
| [`RiemannHypothesis/HilbertInequality.lean`](RiemannHypothesis/HilbertInequality.lean) | **Hilbert's inequality** with the constant `π`: `‖∑_{r ≠ s} x_r conj(x_s)/(k_r − k_s)‖ ≤ π ∑ ‖x_r‖²` for distinct integer frequencies, by the Fourier coefficients `1/m` of the sawtooth `π − θ`; rescaled to `π/δ` for frequencies in a lattice `δ ℤ` — the Montgomery–Vaughan bound in the lattice case, the general theorem being recorded as an unproved `Prop` |
| [`RiemannHypothesis/MontgomeryVaughan.lean`](RiemannHypothesis/MontgomeryVaughan.lean) | **Montgomery and Vaughan's generalized Hilbert inequality**, with the sharp constant: `‖∑_{r ≠ s} x_r conj(x_s)/(λ_r − λ_s)‖ ≤ (π/δ) ∑ ‖x_r‖²` for arbitrary `δ`-separated real frequencies (`generalizedHilbertInequality`, proving `Hilbert.GeneralizedHilbertInequality`), by Montgomery and Vaughan's eigenvector argument, the spectral theorem and Basel's sum |
| [`RiemannHypothesis/MontgomeryVaughanMeanValue.lean`](RiemannHypothesis/MontgomeryVaughanMeanValue.lean) | **the Montgomery–Vaughan mean value theorem**: `∫₀ᵀ ‖∑_r a_r e^{i λ_r t}‖² dt` differs from `T ∑ ‖a_r‖²` by at most `(2π/δ) ∑ ‖a_r‖²` for `δ`-separated frequencies, and `∫₀ᵀ ‖∑_{n ≤ N} a_n n^{−it}‖² dt = (T + O(N)) ∑ ‖a_n‖²` with the constant `2πN` |
| [`RiemannHypothesis/HilbertCosecant.lean`](RiemannHypothesis/HilbertCosecant.lean) | **the cosecant form of the Montgomery–Vaughan inequality**: `‖∑_{r ≠ s} u_r conj(u_s) / sin π(α_r − α_s)‖ ≤ δ⁻¹ ∑ ‖u_r‖²` for points `δ`-separated modulo one (`cosecantHilbertInequality`), by Montgomery and Vaughan's eigenvector argument with the kernel `csc π(α_r − α_s)`; the column sums use the partial-fraction expansion `∑_{m ∈ ℤ} (x + m)⁻² = π² / sin² πx` (`hasSum_inv_sq_int`), derived here from Mathlib's cotangent expansion |
| [`RiemannHypothesis/LocalSpacingMaximal.lean`](RiemannHypothesis/LocalSpacingMaximal.lean) | **a discrete maximal inequality for locally spaced points**: for real `λ_r`, indexed by any finite type, and weights `δ_r > 0` with `δ_r ≤ |λ_r − λ_s|` (`s ≠ r`), `δ_s ∑_{t ≠ s} δ_t/(λ_s − λ_t)² ≤ 6` (`delta_mul_sum_delta_div_sq_le`) and `∑_{s ≠ t} a_s a_t δ_s^{3/2} δ_t^{1/2}/(λ_s − λ_t)² ≤ 2√120 ∑ a_t²` for `a ≥ 0` (`sum_sum_mul_div_sq_le`), by a Vitali covering and a layer-cake estimate for the maximal ball averages; the input of the weighted Montgomery–Vaughan inequality |
| [`RiemannHypothesis/MontgomeryVaughanWeighted.lean`](RiemannHypothesis/MontgomeryVaughanWeighted.lean) | **the weighted Montgomery–Vaughan inequality**: `‖∑_{r ≠ s} u_r conj(u_s)/(λ_r − λ_s)‖ ≤ 5√2 ∑ ‖u_r‖²/δ_r` for any weights `δ_r > 0` with `δ_r ≤ |λ_r − λ_s|` for every `s ≠ r` (`weightedHilbertInequality`; Montgomery and Vaughan's constant is `3π/2 ≈ 4.712`, the one proved here is `5√2 ≈ 7.071 ≈ 2.251π`), by Montgomery and Vaughan's eigenvector argument for the kernel `√(δ_r δ_s)/(λ_r − λ_s)` (`weighted_eigen_identity`, `weighted_eigenvalue_sq_le`: `μ² ≤ 50`) and the spectral theorem; the uniform case gives `5√2/δ` (`hilbertInequality_of_uniform`), weaker than the sharp `π/δ` |
| [`RiemannHypothesis/MontgomeryVaughanWeightedMeanValue.lean`](RiemannHypothesis/MontgomeryVaughanWeightedMeanValue.lean) | **the weighted Montgomery–Vaughan mean value theorem**: `|∫₀ᵀ ‖∑_r a_r e^{i λ_r t}‖² dt − T ∑ ‖a_r‖²| ≤ 10√2 ∑ ‖a_r‖²/δ_r` for locally spaced frequencies (`abs_integral_normSq_expSum_sub_le_weighted`), and `|∫₀ᵀ ‖∑_{n ≤ N} a_n n^{−it}‖² dt − T ∑ ‖a_n‖²| ≤ 10√2 ∑_{n ≤ N} (n + 1) ‖a_n‖²`, i.e. `∑ ‖a_n‖² (T + O(n))` (`abs_integral_normSq_dirichletPoly_sub_le_weighted`), from the local spacing `|log n − log m| ≥ 1/(n + 1)` (`log_local_spacing`) |
| [`RiemannHypothesis/HilbertCosecantWeighted.lean`](RiemannHypothesis/HilbertCosecantWeighted.lean) | **the weighted cosecant inequality**: `‖∑_{r ≠ s} u_r conj(u_s) / sin π(α_r − α_s)‖ ≤ (5√2/π) ∑ ‖u_r‖²/δ_r` for weights `δ_r > 0` with `δ_r ≤ intDist(α_r − α_s)` for every `s ≠ r` (`weightedCosecantInequality`, `weightedCosecantInequality_finset`; Montgomery and Vaughan have `3/2`, `5√2/π ≈ 2.251`), by the weighted eigenvector argument with the kernel `√(δ_r δ_s) csc π(α_r − α_s)` and the maximal bounds of `LocalSpacingMaximal.lean` transferred to the circle by periodization (`delta_mul_sum_delta_cscSq_le`, `sum_sum_cscSq_le`) |
| [`RiemannHypothesis/LargeSieveWeighted.lean`](RiemannHypothesis/LargeSieveWeighted.lean) | **the weighted large sieve**: `∑_i (N + (5√2/π) δ_i⁻¹)⁻¹ ‖∑_{n<N} a_n e(n t_i)‖² ≤ ∑ ‖a_n‖²` for points with local spacings `δ_i ≤ intDist(t_i − t_j)` (`large_sieve_weighted`), with its dual form (`large_sieve_weighted_dual`), by the route of `large_sieve_mv` |
| [`RiemannHypothesis/LargeSieveMV.lean`](RiemannHypothesis/LargeSieveMV.lean) | **the large sieve with the sharp constant `N + δ⁻¹`** (Montgomery–Vaughan): `∑_i ‖∑_{n<N} a_n e(n t_i)‖² ≤ (N + δ⁻¹) ∑_n ‖a_n‖²` under the hypotheses of `large_sieve_gallagher` (`large_sieve_mv`), its dual form, and `admissibleConstant_large_sieve_mv`; Selberg's `N − 1 + δ⁻¹` is not proved |
| [`RiemannHypothesis/BrunTitchmarshTwo.lean`](RiemannHypothesis/BrunTitchmarshTwo.lean) | **Brun–Titchmarsh with the constant `2 + ε`**: the sharp large sieve `N + δ⁻¹` carried down the chain — Farey large sieve with `Q² + N` (`large_sieve_farey_mv`), Montgomery's sieve with `Q² + N` (`card_le_sifted_squarefree_mv`), the level bound `(Q² + y)/log Q + Q + 1` (`card_primes_Ico_le_of_level_mv`), and `#{p prime : x ≤ p < x + y} ≤ (2 + ε) y / log y` for `y ≥ Y(ε)` and all `x` (`card_primes_Ico_le_two`), also in progressions with `(2 + ε)(q/φ(q)) Y / log Y` (`card_primes_Ico_mod_le_two`); Montgomery–Vaughan's exact `2` for all `y > 1` is not proved |
| [`RiemannHypothesis/VanDerCorputSumIntegral.lean`](RiemannHypothesis/VanDerCorputSumIntegral.lean) | **van der Corput's sum-versus-integral lemma** (Titchmarsh, Lemma 4.8): for real `f` on `[a, a + N]` with `f'` monotone and `\|f'\| ≤ θ < 1`, `‖∑_{n<N} e(f(a+n)) − ∫_a^{a+N} e(f(u)) du‖ ≤ 5/2 + 4πθ + 5κ(θ)/2` with `κ(θ) = 1/(πθ) − cot(πθ)` (`norm_sum_e2pi_sub_integral_le`), and with a nonnegative decreasing weight `g` the error `(5/2 + 4πθ + 5κ(θ)/2) g(a)` (`norm_sum_mul_e2pi_sub_integral_le`, `…_of_antitone`; Lemma 4.10), by linear interpolation on unit intervals and Abel summation against `cot(πΔ) − 1/(πΔ)`, which is decreasing on `(−1, 1)` |
| [`RiemannHypothesis/ZetaPartialSum.lean`](RiemannHypothesis/ZetaPartialSum.lean) | **`ζ` and its partial sums** (Titchmarsh, Theorem 4.11): `‖ζ(s) − ∑_{n ≤ x} n^(−s) + x^(1−s)/(1 − s)‖ ≤ 11 x^(−σ)` for `σ > 0`, `s ≠ 1` and real `x > 0` with `\|t\| ≤ x` (`norm_riemannZeta_sub_partialSum_le`; on the critical line `norm_riemannZeta_criticalLine_sub_partialSum_le`), from the Euler–Maclaurin representation and the weighted sum-versus-integral lemma |
| [`RiemannHypothesis/HardyLittlewoodMeanSquare.lean`](RiemannHypothesis/HardyLittlewoodMeanSquare.lean) | **the Hardy–Littlewood mean square on the critical line**: `\|∫_T^{2T} \|ζ(1/2 + it)\|² dt − T log T\| ≤ 584 T` for `T ≥ 1` (`abs_integral_block_zeta_sub_le`), `∫₀ᵀ \|ζ(1/2 + it)\|² dt = T log T + O(T)` for `T ≥ 1` (`exists_abs_integral_normSq_riemannZeta_sub_le`, existential constant) and `(∫₀ᵀ \|ζ(1/2 + it)\|² dt)/(T log T) → 1` (`tendsto_integral_normSq_riemannZeta_div`), by Theorem 4.11 with `x = 2T` and the weighted mean value theorem (Montgomery–Vaughan's route); Ingham's second term `(2γ − 1 − log 2π) T` is not proved |
| [`RiemannHypothesis/OscillatoryIntegral.lean`](RiemannHypothesis/OscillatoryIntegral.lean) | **oscillatory integrals by parts**: the exact first- and second-order identities `∫ g e^{iΦ} = −i[h e^{iΦ}] + [k e^{iΦ}] − ∫ k' e^{iΦ}` with `g = hΦ'`, `h' = kΦ'` (`integral_eq_first_order`, `integral_eq_second_order`), the first-derivative test with a monotone ratio, and its second-order refinement `norm_integral_add_boundary_le_of_monotone` |
| [`RiemannHypothesis/PoissonSummationInterval.lean`](RiemannHypothesis/PoissonSummationInterval.lean) | **Poisson summation on an interval** (exact): `∑_{a<n≤b} G(n) = ∫_a^b G + ψ(a)G(a) − ψ(b)G(b) + ∑_{n≥1} S_n`, a convergent series, for `0 ≤ a ≤ b` and `G` of class `C²` (`hasSum_sum_Ioc_sub_integral`), from the Fourier series of the periodic Bernoulli function; at half-integer endpoints `∑_{A<n≤B} G(n) − ∫ G = ∑_{ν≥1} 2∫ G(x) cos(2πνx) dx` (`hasSum_sum_Ioc_halfInt`) |
| [`RiemannHypothesis/LaplaceGamma.lean`](RiemannHypothesis/LaplaceGamma.lean) | **the Laplace transform at a complex frequency**: `∫_0^∞ u^(a−1) e^(−ru) du = r^(−a) Γ(a)` for `re a > 0` and every complex `r` with `re r > 0` (`integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`), extending Mathlib's real-`r` statement by analytic continuation |
| [`RiemannHypothesis/ZetaMellinPhase.lean`](RiemannHypothesis/ZetaMellinPhase.lean) | **the complete stationary-phase integral of `ζ`**: `∫_0^B u^(−s) e^{iωu} du → Γ(1−s)(i/ω)^(1−s)` for `s = 1/2 + it`, `ω > 0` (`tendsto_integral_mellin`), by letting the damping of the Laplace transform tend to `0⁺` (no Fresnel integral), and `Γ(1−s)(i/2πν)^(1−s) = χ(s)ν^(s−1) + O(ν^(−1/2) e^(−πt))` (`norm_mellinMain_sub_zetaChi_le`, no Stirling formula) |
| [`RiemannHypothesis/ZetaStationaryPhase.lean`](RiemannHypothesis/ZetaStationaryPhase.lean) | **stationary phase for `ζ`** (the B process, R2): for `0 < a < t/(2πν) < b`, `∫_a^b u^(−1/2−it) e(νu) du = χ(s)ν^(s−1) − i[h e^{iΦ}]_a^b` up to `2(‖k(a)‖ + ‖k(b)‖) + ν^(−1/2)e^(−πt)` with `h = √u/(2πνu − t)` and `k = h'/Φ'` (`norm_integral_sub_zetaChi_add_boundary_le`); the initial piece and the tail to second order |
| [`RiemannHypothesis/AFEIntegrals.lean`](RiemannHypothesis/AFEIntegrals.lean) | the remaining integral bounds of the approximate functional equation: the reflected frequency `−2πν` to second order (`norm_mI_neg_add_boundary_le`) and the integral near the stationary point by the second-derivative test (`norm_mI_le_of_near`) |
| [`RiemannHypothesis/AFEProof.lean`](RiemannHypothesis/AFEProof.lean) | **the approximate functional equation, the estimate** (R3): Poisson summation of `n^(−s)` between half-integers (`hasSum_Fν`), Theorem 4.11 at the far end (`norm_zeta_sub_zetaSum_sub_le`), the frequencies below, near and above the stationary range with alternating endpoint sums (`norm_poisson_sub_main_le`), and the numerical bookkeeping (`afe_bound_numeric`): total error `≤ 80/√(N + 1/2)` (`N ≥ 5`, truncation `B + 1/2 ≥ t²`) |
| [`RiemannHypothesis/AFECriticalLineProof.lean`](RiemannHypothesis/AFECriticalLineProof.lean) | **the approximate functional equation of Hardy and Littlewood, proved**: `afeCriticalLine : AFECriticalLine 250`, i.e. `‖ζ(1/2+it) − ∑_{n≤N} n^(−1/2−it) − χ(1/2+it)∑_{n≤N} n^(−1/2+it)‖ ≤ 250 t^(−1/4)` for `t ≥ 2`, `N = ⌊√(t/2π)⌋` (error `≤ 80/√(N + 1/2)` for `t ≥ 200`, `norm_afe_error_le_large`), and unconditionally `‖ζ(1/2+it)‖ ≤ 254 t^(1/4)` for `t ≥ 2` (`norm_riemannZeta_criticalLine_le`) |
| [`RiemannHypothesis/VaughanIdentity.lean`](RiemannHypothesis/VaughanIdentity.lean) | **Vaughan's identity**: `Λ = Λ_{≤U} + log ∗ μ_{≤V} − Λ_{≤U} ∗ ζ ∗ μ_{≤V} + Λ_{>U} ∗ ζ ∗ μ_{>V}` in the Dirichlet convolution ring, with the three terms written out as divisor sums and summed against an arbitrary weight — the combinatorial input of Bombieri–Vinogradov; no bilinear estimate is proved |
| [`RiemannHypothesis/VinogradovMeanValue.lean`](RiemannHypothesis/VinogradovMeanValue.lean) | **the Vinogradov system**: the solution count `J_{s,k}(X)`, its translation and dilation invariances, the diagonal lower bound `X^s ≤ J` and the non-vacuity check `J_{1,1}(X) = X`; the mean value theorem itself is recorded as a `Prop` and is not proved |
| [`RiemannHypothesis/VinogradovCongruencing.lean`](RiemannHypothesis/VinogradovCongruencing.lean) | **the congruencing step**: the descent `vinogradovEq_of_affine` (if `(r + q u, r + q v)` solves the Vinogradov system, so does `(u, v)`), the decomposition of `J_{s,k}(X)` along the residue profiles modulo `q`, and the congruencing lemma `C_{s,k}(X; q, r) ≤ J_{s,k}(X/q + 1)` with its summed and iterated forms; the induction of efficient congruencing, and hence the mean value theorem, is not formalized |
| [`RiemannHypothesis/VinogradovConditioning.lean`](RiemannHypothesis/VinogradovConditioning.lean) | **the conditioning input**: Newton's identities evaluated at a tuple, hence `esymm_eq_of_powerSum_eq` (equal power sums of degrees `1, …, k` force equal elementary symmetric functions) and `multiset_map_eq_of_powerSum_eq_zmod` (modulo a prime `p > k`, two solutions of the Vinogradov congruence system are rearrangements of one another), and the conditioning bound `card_congruenceSolutions_le_factorial`: at most `k !` residue tuples share a prescribed vector of power sums; the induction that interleaves this with the descent is not formalized |
| [`RiemannHypothesis/MeanFluctuation.lean`](RiemannHypothesis/MeanFluctuation.lean) | what a mean value says about fluctuation: `\|ζ(σ+it)\|²` comes arbitrarily close to `ζ(2σ)` from above and from below, for arbitrarily large `t` and `σ > 1` |
| [`RiemannHypothesis/FourthMoment.lean`](RiemannHypothesis/FourthMoment.lean) | `∑ d(n) n^(−s) = ζ(s)²` for `re s > 1`, and the **fourth moment** `(1/T) ∫₀ᵀ \|ζ(σ + i t)\|⁴ dt → ∑ d(n)² n^(−2σ)` for `σ > 1` |
| [`RiemannHypothesis/HigherMoments.lean`](RiemannHypothesis/HigherMoments.lean) | `∑ d_k(n) n^(−s) = ζ(s)^k` for `re s > 1`, and **every even moment** `(1/T) ∫₀ᵀ \|ζ(σ + i t)\|^(2k) dt → ∑ d_k(n)² n^(−2σ)` for `σ > 1` |
| [`RiemannHypothesis/PartialProved.lean`](RiemannHypothesis/PartialProved.lean) | the `Partial.lean` statements that are now *theorems*: `HardyTheorem`, `PositiveProportionOnCriticalLine`, `TwoFifthsOnCriticalLine`, and `liminf N₀(T)/N(T) ≥ 2/3` |
| [`RiemannHypothesis/Main.lean`](RiemannHypothesis/Main.lean) | the three equivalence theorems |
| [`comparator.json`](comparator.json) | the statements Solution is checked against |
| [`scripts/audit.sh`](scripts/audit.sh) | checks no unproved statement outside `Challenge.lean`, that the theorems use only `propext`, `Classical.choice`, `Quot.sound`, that the closed task-board rows are pinned, that the conditional theorems are the recorded ones, and that the board validates |
| [`scripts/axiom_audit.lean`](scripts/axiom_audit.lean) | the axiom check, exhaustively: the axioms of **every** theorem of the library are collected from the environment and compared with `propext`, `Classical.choice`, `Quot.sound`, so a new theorem needs no new line anywhere |
| [`scripts/list_theorems.lean`](scripts/list_theorems.lean), [`scripts/audit_coverage.py`](scripts/audit_coverage.py) | coverage of the hand-maintained list of `#print axioms` lines in `audit.sh`, and a hard failure if it names a theorem the library no longer exports |
| [`scripts/conditional_theorems.lean`](scripts/conditional_theorems.lean) | lists every theorem of the library one of whose hypotheses mentions a `Prop` that the repository states but does not prove — the conditional/unconditional boundary, computed from the environment |
| [`scripts/revalidation.lean`](scripts/revalidation.lean) | statement pinning: every claim of every closed task-board row, written out in full, with the repository's declaration as the proof term |

## Building

```bash
elan toolchain install leanprover/lean4:v4.33.1
lake exe cache get   # Mathlib's prebuilt oleans; without this Mathlib is compiled from source
lake build
./scripts/audit.sh
```

The vendored [`Zeta23`](vendor/zeta23) library and this repository are compiled from source
(there is no cache for them), which takes a while on a first build.

## The alpo.ge tree: a claimed proof, vendored for verification

[`vendor/alpo`](vendor/alpo) holds a Lean tree published on 2026-11-20 at
`https://alpo.ge/lean.tar.gz.part01` … `part14`, together with the announcement that came with it
([`remark.pdf`](vendor/alpo/remark.pdf)). It claims a proof of the Riemann hypothesis
(`theorem riemannHypothesis : RiemannHypothesis`, Mathlib's statement, which is our `ZetaForm`)
and of GRH for Dirichlet `L`-functions. **It is not verified, and nothing in this repository
depends on it.** The tree is kept byte-identical to the published archive (checked by
`vendor/alpo/tools/provenance.sh` against the recorded SHA-256 hashes), passes a static scan,
and has 175,187 modules, all of which `Main` imports, so only a full build can decide it
(estimated 290–460 core-hours). This repository uses the same pins as the tree (Lean v4.33.1,
Mathlib `0df444a3`), so that [`vendor/alpo/Bridge.lean`](vendor/alpo/Bridge.lean) can check the
tree's theorem against `ZetaForm`, `ZetaStripForm` and `EtaForm`. Where the code comes from, what
has been checked, and how to finish the check: [`vendor/alpo/README.md`](vendor/alpo/README.md);
CI: the manual workflow [`alpo-verify`](.github/workflows/alpo-verify.yml); task board:
`M3-ALPO-VERIFICATION`. Do not run `lake build` inside `vendor/alpo/lean`: Lake cannot cap its
parallelism, and on this tree an unthrottled build crashed the machine.

## Goal task board

The long-term goal of this repository is a Lean proof of the Riemann hypothesis.
`docs/goal/task-board.yaml` is the executable queue (24 tasks across milestones
M0–M4, modelled on the pcc project's board): M0 statement/equivalence/foundations
(done), M1 classical results (PNT, zero-free region, Hardy, Bohr–Landau), M2 modern
partial results (Selberg, Levinson, Conrey, density), M3 research (the step beyond
the known results), M4 the conjecture itself. The board's dependency graph is honest:
nothing implies the conjecture, so M4 depends on the research row M3-GAP.

```bash
python3 scripts/goal_state.py validate   # board sanity
python3 scripts/goal_state.py next       # next dependency-ready task
python3 scripts/goal_state.py render     # regenerate docs/current-goal-state.md
```

## Growth of `ζ` in the critical strip

[`RiemannHypothesis/Growth.lean`](RiemannHypothesis/Growth.lean) carries the estimates from
the half-plane of absolute convergence into the strip, where the Dirichlet series diverges,
using the paired eta series:

```lean
theorem norm_dirichletEta_le {s : ℂ} (hs : 0 < s.re) :
    ‖dirichletEta s‖ ≤ ‖s‖ * (1 + 1 / s.re)

theorem norm_riemannZeta_le_of_mem_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ * (1 + 1 / s.re) / ((2 : ℝ) ^ (1 - s.re) - 1)

theorem norm_riemannZeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 *
      riemannZeta (1 + x + 2 * I * y)‖
```

So `ζ` grows at most linearly in the height on every vertical line strictly inside the
strip — in particular it is of finite order there — with the explicit constant
`C(σ) = (1 + 1/σ)/(2^(1−σ) − 1)`.  The classical convexity bound
`O(|t|^((1−σ)/2+ε))` is *not* proved in this file; it is proved by Phragmén–Lindelöf in
`Convexity.lean` and `ConvexityLogFree.lean` (`M1-CONVEXITY`, `M1-GROWTH`), and on the critical line also from
the approximate functional equation in `AFECriticalLineProof.lean`.  The last theorem is the
Mertens `3-4-1` positivity input to the classical zero-free region; it is obtained by
specializing Mathlib's Dirichlet-character product bound to modulus `1`.

## The mean square of a Dirichlet series, of `ζ`, and of `1/ζ`

[`RiemannHypothesis/MeanSquare.lean`](RiemannHypothesis/MeanSquare.lean) proves the first
moment computation of the theory, once and for all, for any Dirichlet series that converges
absolutely on the line:

```lean
theorem meanSquareAvg_tendsto_tsum_of_summable {A : ℕ → ℂ} {σ : ℝ}
    (hA : Summable (dirichletWeight A σ)) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖dirichletLineSum A σ t‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, dirichletWeight A σ n ^ 2))
```

Squaring the series against its own conjugate gives the absolutely convergent double series

`|D(σ + i t)|² = ∑_{(m,n)} aₘ conj(aₙ) ((m+1)(n+1))^(−σ) e^{i t log((n+1)/(m+1))}`,

which may be integrated term by term over `[0, T]`.  Every off-diagonal frequency is nonzero,
so `‖∫₀ᵀ e^{iθt} dt‖ ≤ 2/|θ|` and its average dies; only the diagonal survives, with average
`1`.  Two specializations, both for `σ > 1`:

```lean
theorem meanSquareAvg_tendsto_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (linePoint σ t)‖ ^ 2) / T) atTop
      (𝓝 (riemannZeta ((2 * σ : ℝ) : ℂ)).re)

theorem meanSquareAvg_tendsto_tsum_moebius {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖(riemannZeta (linePoint σ t))⁻¹‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) ^ 2 *
        ((n : ℝ) + 1) ^ (-(2 * σ))))
```

the first with `aₙ = 1`, so that the diagonal is `∑ (n+1)^(−2σ) = ζ(2σ)`, the second with
`aₙ = μ(n)`, the Möbius series being `1/ζ` there.  Only the half-plane of absolute convergence
is covered here: the second moment on the critical line, `∫₀ᵀ |ζ(1/2 + i t)|² dt ∼ T log T`, is
proved by another route in
[`RiemannHypothesis/HardyLittlewoodMeanSquare.lean`](RiemannHypothesis/HardyLittlewoodMeanSquare.lean),
without the approximate functional equation.

## The fourth moment of `ζ`

[`RiemannHypothesis/FourthMoment.lean`](RiemannHypothesis/FourthMoment.lean) feeds one more
series into the same machine.  The Dirichlet convolution of the constant-one function with
itself is the divisor counting function `d(n) = #n.divisors`, so `ζ²` is itself a Dirichlet
series, absolutely convergent for `re s > 1`:

```lean
theorem lseries_divisorCount {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (divisorCount n : ℂ)) s = riemannZeta s ^ 2
```

Applying the mean value theorem to it, and using `‖ζ(s)²‖² = ‖ζ(s)‖⁴`, gives the fourth
moment on any line of absolute convergence:

```lean
theorem fourthMomentAvg_tendsto_tsum_divisorCount {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (linePoint σ t)‖ ^ 4) / T) atTop
      (𝓝 (∑' n : ℕ, ((divisorCount (n + 1) : ℝ)) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ))))
```

As with the second moment, the critical strip is untouched: Ingham's asymptotic
`∫₀ᵀ |ζ(1/2 + i t)|⁴ dt ∼ T (log T)⁴/(2π²)` is not proved here, and the limit is left as a
series rather than evaluated as `ζ(2σ)⁴/ζ(4σ)`.

## All even moments

[`RiemannHypothesis/HigherMoments.lean`](RiemannHypothesis/HigherMoments.lean) iterates the
same idea.  Writing `d_k(n)` (`divisorCountK k n`) for the number of ordered factorizations of
`n` into `k` factors — the `k`-th convolution power of the constant-one function, so
`d_1 = 1` and `d_2 = d` — induction on the convolution recursion `d_{k+1} = 1 ⋆ d_k` gives

```lean
theorem lseries_divisorCountK (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (divisorCountK k n : ℂ)) s = riemannZeta s ^ k

theorem momentAvg_tendsto_tsum_divisorCountK (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (linePoint σ t)‖ ^ (2 * k)) / T)
      atTop
      (𝓝 (∑' n : ℕ, ((divisorCountK k (n + 1) : ℝ)) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * σ))))
```

`k = 1` is the second moment above and `k = 2` the fourth.  Again nothing is claimed inside
the critical strip, where the moment problem is genuinely hard.

## The mean square inside the critical strip

Everything above lives in the half-plane `re s > 1`, where the Dirichlet series converges
absolutely.  Four files carry the second moment *into* the strip, where `ζ` has to be
approximated before it can be averaged.

The mechanism is always the same.  Euler–Maclaurin summation replaces `ζ(σ + i t)` by a
Dirichlet polynomial `∑_{n ≤ N} n^(−s)` plus an explicit main term and a tail; the mean square
of the polynomial is the diagonal `T ∑ n^(−2σ)` plus off-diagonal terms of size
`O(N^(2−2σ) (1 + log N))`; and `N` is chosen to balance the two.  A longer expansion of `ζ`
makes the tail smaller, so `N` may be taken smaller, and the off-diagonal condition
`N^(2−2σ) = O(T^(1−ε))` then holds for smaller `σ`.  With `k` Bernoulli corrections the tail is
`O(‖s‖^(k+1) N^(−k−σ))`, the optimal length is `N ≍ T^((k+1)/(k+σ))`, and the condition reads
`σ > (k + 2)/(2k + 3)`.  Three files formalize `k = 0, 1, 2`:

```lean
theorem exists_integral_normSq_riemannZeta_le {σ : ℝ} (h0 : 2 / 3 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T

theorem exists_integral_normSq_riemannZeta_le_three_fifths {σ : ℝ}
    (h0 : 3 / 5 < σ) (h1 : σ < 1) : ...

theorem exists_integral_normSq_riemannZeta_le_four_sevenths {σ : ℝ}
    (h0 : 4 / 7 < σ) (h1 : σ < 1) : ...
```

The correction terms are built by hand rather than taken from a general Bernoulli expansion.
In [`StripMeanSquareTrapezoid.lean`](RiemannHypothesis/StripMeanSquareTrapezoid.lean),
`trapTerm n s` is the trapezoid-rule error for `x^(−s)` on `[n+1, n+2]`, written as an integral
against the Green's function `P(x) = ((x−a)² − (x−a))/2`, whence
`‖trapTerm n s‖ ≤ (1/8)‖s‖‖s+1‖(n+1)^(−(2+σ))`.  In
[`StripMeanSquareBernoulli.lean`](RiemannHypothesis/StripMeanSquareBernoulli.lean) the
expansion is carried one term further: `bern3Green a z = B₃(z − a)/6` with
`B₃(u) = u(u − 1/2)(u − 1)`, whose third derivative is `1`, so that the primitive
`Q f″ − Q′ f′ + Q″ f` differentiates to `Q f‴ + f`.  Removing the resulting explicit `B₂` term
from the trapezoidal error leaves `bernTerm`, with

```lean
theorem norm_bernTerm_le (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖bernTerm n s‖ ≤ 1 / 48 * ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((n : ℝ) + 1) ^ (-(3 + s.re))
```

and hence the representation `riemannZeta_eq_bernApprox`,

`ζ(s) = ∑_{n ≤ N} n^(−s) + (N+1)^(1−s)/(s−1) + (N+1)^(−s)/2 + s(N+1)^(−s−1)/12 + ∑_{n ≥ N} bernTerm n s`,

whose tail is `O(‖s‖³ N^(−2−σ))`.  Each of the three ranges comes with the two standard
consequences: the first moment `∫₀ᵀ |ζ(σ + i t)| dt = O(T)`, and the large values estimate that
`{t ∈ (0, T] : |ζ(σ + i t)| ≥ V}` has measure at most `C T / V²` — the shape in which a mean
square enters the zero-density estimates.

[`StripMeanSquareAsymptotic.lean`](RiemannHypothesis/StripMeanSquareAsymptotic.lean) upgrades
the upper bound to an asymptotic with a power saving.  Two changes suffice: a *two-sided* mean
value theorem for Dirichlet polynomials (`abs_integral_normSq_dirichletPoly_sub_diag_le`, using
`|re z| ≤ ‖z‖` where the upper bound used `re z ≤ ‖z‖`), and a polynomial slightly longer than
the optimum of the upper bound, `N ≍ T^e` with `2/(1+σ) < e < 1/(2−2σ)` — an interval which is
nonempty exactly when `σ > 3/5`.  Then

```lean
theorem exists_integral_normSq_riemannZeta_asymptotic {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
          - (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ))) * T| ≤ C * T ^ (1 - c)

theorem tendsto_integral_normSq_riemannZeta_div {σ : ℝ} (h0 : 3 / 5 < σ) (h1 : σ < 1) :
    Filter.Tendsto
      (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T)
      Filter.atTop (nhds (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * σ))))
```

the limit being `ζ(2σ)` by `ofReal_tsum_natAddOne_rpow_neg_eq_riemannZeta`.  The whole range
`σ > 1/2` is then reached by letting the order of the Euler–Maclaurin expansion grow with `σ`
instead of writing out a fixed number of Bernoulli corrections:
[`StripMeanSquareBohrLandau.lean`](RiemannHypothesis/StripMeanSquareBohrLandau.lean) gives the
upper bound and [`StripMeanSquareAsymptoticHalf.lean`](RiemannHypothesis/StripMeanSquareAsymptoticHalf.lean)
the asymptotic, for every `1/2 < σ < 1`.  On the critical line these files prove nothing;
there `(1/T) ∫₀ᵀ |ζ(1/2 + i t)|² dt ∼ log T` is proved in
[`HardyLittlewoodMeanSquare.lean`](RiemannHypothesis/HardyLittlewoodMeanSquare.lean), without the
approximate functional equation.

## The Bohr–Landau zero-density theorem

The mean square finally says something about the *zeroes*.  The route is Jensen's inequality,
not the argument principle, and it needs the mean square in a form the previous section does
not supply: **uniformly in the abscissa**, because a circle of radius `R` about `3 + i y` meets
every abscissa between `3 − R` and `3 + R` at once.
[`StripMeanSquareUniform.lean`](RiemannHypothesis/StripMeanSquareUniform.lean) provides it, by
fixing the order `m` of the expansion once and for all by `σ₀` rather than by `σ`:

```lean
theorem exists_integral_normSq_riemannZeta_le_uniform {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T
```

There is no upper bound on `σ`: one constant covers the whole half-plane `re s ≥ σ₀`.
[`ZetaCircleAverage.lean`](RiemannHypothesis/ZetaCircleAverage.lean) turns it into a statement
about circles.  Since `log x ≤ x²/2`, the circle average of `log ‖ζ‖` is at most that of
`‖ζ‖²/2`, and Tonelli and Fubini over `[0, 2π] × [a, b]` — the integrand being continuous there,
the pole at `s = 1` lying outside every circle of radius `R < 5/2` about `3 + i y` with `y ≥ 4`
— reduce the vertical integral of those averages to the uniform mean square:

```lean
theorem exists_integral_circleAverage_normSq_riemannZeta_le {R : ℝ} (hR0 : 0 < R)
    (hR : R < 5 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 4 ≤ a → a ≤ b →
      (∫ y in a..b,
          circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) ((3 : ℂ) + (y : ℂ) * I) R)
        ≤ C * b
```

[`BohrLandau.lean`](RiemannHypothesis/BohrLandau.lean) assembles the count.  With
`κ = (σ − 1/2)/4`, `r = 3 − σ + κ` and `R = 3 − σ + 2κ`, a zero with `re ρ ≥ σ` and
`|im ρ − y| ≤ κ` lies in the closed disc of radius `r` about `3 + i y`, because
`(3 − σ)² + κ² ≤ r²`; the Jensen counting inequality then bounds the number of such zeroes by
`(circleAverage (‖ζ‖²/2) (3 + i y) R + log 2) / log (R/r)`, using `‖ζ(3 + i y)‖ ≥ 1/2`.
Integrating a window indicator in `y` converts that local count into the global one:

```lean
theorem exists_ncard_zerosRightOf_le {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ((zerosRightOf σ T).ncard : ℝ) ≤ C * T
```

where `zerosRightOf σ T = {ρ | ζ ρ = 0 ∧ σ ≤ re ρ ∧ 0 < im ρ ≤ T}`.  Reflecting in the critical
line through `ρ ↦ 1 − conj ρ` gives the two-sided form
`exists_ncard_zerosOffCriticalLine_le`.  Against it stands the Riemann–von Mangoldt **lower**
bound, read off the dyadic window `(T/2, T]`,

```lean
theorem exists_mul_le_windowCount_zero :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (T * Real.log T) ≤ (windowCount 0 T : ℝ)
```

and dividing one by the other gives the classical conclusion: **almost all zeroes of `ζ` lie
within `δ` of the critical line**, for every fixed `δ > 0`,

```lean
theorem tendsto_zerosOffCriticalLine_div_windowCount {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    Tendsto (fun T : ℝ => ((zerosOffCriticalLine δ T).ncard : ℝ) / (windowCount 0 T : ℝ))
      atTop (𝓝 0)
```

at the rate `O_δ(1 / log T)`.  Everything here is unconditional.

Replacing `ζ` by the mollified function `ζ M_y`, `M_y(s) = ∑_{n ≤ y} μ(n) n^(−s)`, in the same
counting argument sharpens the `O(T)` above to `o(T)`; this is Carlson's density theorem, and
it is proved in `CarlsonDensity.lean`, so the `Prop` `AlmostAllZerosNearCriticalLine` of
`Partial.lean` — which normalizes by `T` rather than by `N(0, T)` — is now a theorem:

```lean
theorem tendsto_ncard_zerosRightOf_div_atTop {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    Tendsto (fun T : ℝ => ((zerosRightOf σ T).ncard : ℝ) / T) atTop (𝓝 0)

theorem almostAllZerosNearCriticalLine : AlmostAllZerosNearCriticalLine
```

Letting the mollifier length grow with the height, `y = ⌈T^γ⌉`, and quantifying every step of
the same argument turns the `o(T)` into a genuine power saving; this is
`CarlsonPowerSaving.lean` and `CarlsonDensityPowerSaving.lean`:

```lean
theorem exists_ncard_zerosRightOf_le_rpow {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧ (σ - 1 / 2) ^ 2 / 64 ≤ c ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosRightOf σ T).ncard : ℝ) ≤ C * T ^ (1 - c)
```

Tracking the constants through that chain — the Montgomery–Vaughan exponent is exactly
`1 − θ/2`, the Euler–Maclaurin exponent at most `1 − θ`, the mollifier length `T^{θ/8}` and the
mean-square saving `3θ/8`, all in `θ = σ₀ − 1/2` — names the saving, and the bound can be
stated with the exponent written out:

```lean
theorem ncard_zerosRightOf_le_rpow_explicit {σ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ((zerosRightOf σ T).ncard : ℝ) ≤ C * T ^ (1 - (σ - 1 / 2) ^ 2 / 64)
```

The exponent now degrades continuously to `0` as `σ ↓ 1/2`.  What is still *not* proved is
Carlson's quantitative form `N(σ, T) = O(T^{4σ(1−σ)} log T)`, whose saving `4(σ − 1/2)²` has
the same shape but a constant `256` times better, nor the linear saving
`O(T^{1−c(σ−1/2)})` of the Selberg and Ingham density theorems, which needs a sharp mean value
theorem or the fourth moment.  The constant `C(σ)` is not effective.  No zero-free region and
no location of any individual zero follows, and the Riemann hypothesis is untouched.

## Backlund's criterion: from the Lindelöf hypothesis to the zeroes

The same Jensen disc, with the mean square replaced by a pointwise bound, gives the
zero-counting half of a classical *equivalence*.  Backlund proved that the Lindelöf hypothesis
— `ζ(σ + i t) = O(t^ε)` for every `ε > 0`, uniformly for `σ ≥ 1/2` — holds if and only if, for
every fixed `σ > 1/2`, a window of unit height carries `o(log T)` zeroes with real part at least
`σ`.  Unconditionally such a window carries `O(log T)` zeroes, so the content is the saving of
the whole logarithm.
[`LindelofDensity.lean`](RiemannHypothesis/LindelofDensity.lean) proves the direction from the
growth hypothesis to the zeroes.  The hypothesis is recorded as a `Prop`,

```lean
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ s.im → ‖riemannZeta s‖ ≤ C * s.im ^ ε
```

and is never proved here — it is open, and is implied by the Riemann hypothesis.  The
unconditional half of the file is the one-disc estimate against the *maximum* of `‖ζ‖`:
writing the circle average of `log ‖ζ‖` down to `log M`,

```lean
theorem card_filter_le_log_max {σ κ r R M : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hrR : r < R)
    (hR : R < 5 / 2) (hgeom : (3 - σ) ^ 2 + κ ^ 2 ≤ r ^ 2) (hM : 1 ≤ M)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ σ ≤ ρ.re) {y : ℝ} (hy : 4 ≤ y)
    (hbd : ∀ z ∈ Metric.sphere ((3 : ℂ) + (y : ℂ) * I) R, ‖riemannZeta z‖ ≤ M) :
    ((S.filter fun ρ => |ρ.im - y| ≤ κ).card : ℝ) * Real.log (R / r)
      ≤ Real.log M + Real.log 2
```

The geometry is that of the Bohr–Landau section: with `κ = (σ − 1/2)/4`, `r = 3 − σ + κ` and
`R = 3 − σ + 2κ` the larger disc stays inside `re s > 1/2`, where the Lindelöf bound applies,
while the smaller one already contains every zero with `re ρ ≥ σ` and `|im ρ − y| ≤ κ`.  Under
the hypothesis each such disc therefore carries at most
`(log C + log 2 + ε log (y+3))/log (R/r)` zeroes, a window of unit height is covered by
`⌈κ⁻¹/2⌉` of them — a number depending only on `σ` — and `ε > 0` is arbitrary:

```lean
theorem exists_ncard_zerosRightOfWindow_le (hLH : LindelofHypothesis) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 5 ≤ T →
      ((zerosRightOfWindow σ T (T + 1)).ncard : ℝ) ≤ A + ε * Real.log T

theorem tendsto_ncard_zerosRightOfWindow_div_log (hLH : LindelofHypothesis) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (fun T : ℝ => ((zerosRightOfWindow σ T (T + 1)).ncard : ℝ) / Real.log T)
      atTop (𝓝 0)
```

Reflecting in the critical line — the zeroes of `ζ` in the strip are symmetric about `re s = 1/2`
by `ρ ↦ 1 − conj ρ` — turns this one-sided statement into a two-sided one, at the cost of a
factor `2`:

```lean
def zerosOffCriticalLineWindow (δ T₁ T₂ : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ δ ≤ |ρ.re - 1 / 2| ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

theorem tendsto_ncard_zerosOffCriticalLineWindow_div_log (hLH : LindelofHypothesis) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    Tendsto (fun T : ℝ => ((zerosOffCriticalLineWindow δ T (T + 1)).ncard : ℝ) / Real.log T)
      atTop (𝓝 0)
```

So under the Lindelöf hypothesis all but `o(log T)` of the zeroes of a unit window lie within
`δ` of the critical line, for every fixed `δ > 0`.  This is still far weaker than the Riemann
hypothesis, which asserts `δ = 0` for *every* zero.

The unconditional comparison is recorded in the same file, so that the content of the criterion is
visible: restricting the local Riemann–von Mangoldt bound of
[`ZeroCountLocal.lean`](RiemannHypothesis/ZeroCountLocal.lean) to the zeroes right of `re s = σ`
gives

```lean
theorem exists_ncard_zerosRightOfWindow_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ) (T : ℝ), 25 ≤ T →
      ((zerosRightOfWindow σ T (T + 1)).ncard : ℝ) ≤ C * Real.log T
```

with an absolute constant — so what the Lindelöf hypothesis buys is the whole logarithm.

Only this direction is formalized.  The converse — that `o(log T)` zeroes per unit window force
the Lindelöf bound — needs Littlewood's lemma together with the Borel–Carathéodory estimate for
`log ζ`, and is not in the repository.  Zeroes are counted without multiplicity, and nothing
here is unconditional beyond `card_filter_le_log_max` and
`exists_ncard_zerosRightOfWindow_le_log`.

## Hadamard's three circles

Mathlib has the three-*lines* theorem — a bounded function holomorphic on a vertical strip and
continuous on its closure obeys the logarithmically convex interpolation of its bounds on the two
boundary lines — but not the three-*circles* theorem.
[`ThreeCircles.lean`](RiemannHypothesis/ThreeCircles.lean) supplies the latter by transporting the
former along `w ↦ exp w`, which carries the closed strip `log r₁ ≤ re w ≤ log r₃` onto the closed
annulus `r₁ ≤ |z| ≤ r₃`:

```lean
theorem three_circles {f : ℂ → ℂ} {r₁ r₃ a b : ℝ}
    (hr₁ : 0 < r₁) (hr : r₁ < r₃) (hf : AnalyticOnNhd ℂ f (closedAnnulus r₁ r₃))
    (ha : ∀ z : ℂ, ‖z‖ = r₁ → ‖f z‖ ≤ a) (hb : ∀ z : ℂ, ‖z‖ = r₃ → ‖f z‖ ≤ b)
    {z : ℂ} (hz : z ∈ closedAnnulus r₁ r₃) :
    ‖f z‖ ≤ a ^ (Real.log (r₃ / ‖z‖) / Real.log (r₃ / r₁))
      * b ^ (Real.log (‖z‖ / r₁) / Real.log (r₃ / r₁))
```

Equivalently, `log M(r)` is convex in `log r`, where `M(r)` bounds `‖f‖` on the circle of radius
`r`.  The three hypotheses of the three-lines theorem come out of compactness of the annulus
(boundedness), analyticity of `f ∘ exp` on the closed strip (`DiffContOnCl`), and
`‖exp w‖ = exp (re w)` (the boundary bounds).

The file itself says nothing about `ζ`; it is the analytic tool that the two open boundaries of
the previous section — the converse direction of Backlund's criterion, and the deduction of the
Lindelöf hypothesis from the Riemann hypothesis — both require.  The next section applies it,
together with Mathlib's Borel–Carathéodory theorem, to the second of the two.

## Littlewood's theorem away from the critical line

Littlewood's theorem is that the Riemann hypothesis implies the Lindelöf hypothesis.
[`LindelofFromRH.lean`](RiemannHypothesis/LindelofFromRH.lean) proves the part of it that does not
need the radii of the three circles to shrink with the height: for every *fixed* `δ > 0`,

```lean
theorem exists_bound_riemannZeta_of_zetaStripForm (h : ZetaStripForm) {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → T₀ ≤ s.im →
      ‖riemannZeta s‖ ≤ C * s.im ^ ε
```

Under the hypothesis `(s − 1) ζ(s)` has no zero in `re s > 1/2`, so it has a holomorphic logarithm
`F` there; normalizing at the centre `s₀ = 3 + i t` of a disc of radius `5/2` makes the branch
constant cancel, `re (F(s₀ + z) − F(s₀)) = log ‖(s−1)ζ(s)‖ − log ‖(s₀−1)ζ(s₀)‖`.  The real part is
`O(1)` on the disc of radius `1` and `≤ 6 log t` on the disc of radius `5/2`; Borel–Carathéodory
turns the two into bounds for the modulus on the circles `|z| = 1/2` and `|z| = 5/2 − δ/2`, and
Hadamard's three circles interpolates between them with an exponent
`λ₀ = log(5 − 2δ)/log(5 − δ) < 1`.  Exponentiating gives `‖ζ(σ + i t)‖ ≤ 3 e^{4(60 log t/δ)^{λ₀}}`,
which is `O_ε(t^ε)` because `λ₀ < 1`.

The critical line itself is *not* covered: as `δ → 0` the exponent `λ₀` tends to `1` and the
threshold `T₀` tends to infinity, so `LindelofHypothesis` of the previous section, which asks for
the bound uniformly for `re s ≥ 1/2`, is not proved.  Reaching the line is Littlewood's
`log ζ(1/2 + i t) = O(log t / log log t)`, which needs the radii to shrink with `t`.  Everything in
the file is conditional on the Riemann hypothesis and is listed as such in
[`docs/goal/conditional-theorems.txt`](docs/goal/conditional-theorems.txt).

## The Euler–Maclaurin representation and the logarithmic bound

The eta route above cannot reach the bound the zero-free region needs, because the factor
`1 − 2^(1−s)` vanishes on the line `re s = 1` at arbitrarily large heights.
[`RiemannHypothesis/EulerMaclaurin.lean`](RiemannHypothesis/EulerMaclaurin.lean) supplies it
by first-order Euler–Maclaurin summation.  With
`eulerTerm n s = (n+1)^(−s) − ∫_{n+1}^{n+2} x^(−s) dx`:

```lean
theorem riemannZeta_eq_zetaApprox (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = zetaApprox N s
-- zetaApprox N s = ∑_{n<N} (n+1)^(-s) + (N+1)^(1-s)/(s-1) + ∑' n, eulerTerm (n+N) s

theorem norm_riemannZeta_le_log {s : ℂ} (h1 : 1 ≤ s.re) (h2 : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 6 + Real.log (1 + |s.im|)
```

The representation is proved on `re s > 1` only, by an elementary telescoping argument — no
analytic continuation and no differentiation under the integral sign.  Choosing
`N = ⌈|t|⌉` turns it into the bound above for `1 < re s ≤ 2`; the line `re s = 1` is then
reached by continuity of `σ ↦ ζ(σ+it)`.  The constants are explicit, and the bound is
uniform in `σ` (there is no `1/(σ−1)` factor).

## A quantitative lower bound to the right of `re s = 1`

Feeding the `3-4-1` inequality with the two upper bounds above gives, in
[`RiemannHypothesis/ZeroFree.lean`](RiemannHypothesis/ZeroFree.lean),

```lean
theorem norm_riemannZeta_pow_four_ge {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy : 1 ≤ |y|) :
    x ^ 3 / (8 * (6 + Real.log (1 + 2 * |y|))) ≤ ‖riemannZeta (1 + x + I * y)‖ ^ 4
```

Mathlib's `riemannZeta_ne_zero_of_one_le_re` already gives nonvanishing on `re s ≥ 1`, but
only qualitatively; this is the quantitative form the de la Vallée Poussin argument starts
from.

## A zero-free region to the left of `re s = 1`

Transferring that bound across the line needs an estimate for `ζ'`.  Continuing the
Euler–Maclaurin representation to the punctured right half-plane
([`RiemannHypothesis/Continuation.lean`](RiemannHypothesis/Continuation.lean)) gives the
logarithmic bound `‖ζ(s)‖ ≤ 18 log|t|` on the strip `1 − 1/(2 log|t|) ≤ re s ≤ 2`
([`RiemannHypothesis/NearLine.lean`](RiemannHypothesis/NearLine.lean)), Cauchy's estimate on
a disc of radius `1/(8 log|t|)` turns it into `‖ζ'(s)‖ ≤ 288 (log|t|)²`, and the mean value
inequality along a horizontal segment then contradicts the lower bound above at a
hypothetical zero.  The result, in
[`RiemannHypothesis/ZeroFreeRegion.lean`](RiemannHypothesis/ZeroFreeRegion.lean), is

```lean
theorem riemannZeta_ne_zero_of_near_one {s : ℂ} (ht : 4 ≤ |s.im|)
    (hre : 1 - (1 / 2 ^ 45) / Real.log |s.im| ^ 9 < s.re) : riemannZeta s ≠ 0
```

This is a genuine zero-free region, with a completely explicit constant, but it is *weaker in
shape* than de la Vallée Poussin's: the exponent is `9`, not `1`.  Reflecting it in the
critical line — a zero in the strip forces `ζ(1−s) = 0`, by
[`RiemannHypothesis/Symmetry.lean`](RiemannHypothesis/Symmetry.lean) — confines the zeroes to
a strip strictly inside the critical strip
([`RiemannHypothesis/ZeroLocation.lean`](RiemannHypothesis/ZeroLocation.lean)):

```lean
theorem zero_abs_re_sub_half_le {s : ℂ} (hz : riemannZeta s = 0) (ht : 4 ≤ |s.im|) :
    |s.re - 1 / 2| ≤ 1 / 2 - (1 / 2 ^ 45) / Real.log |s.im| ^ 9
```

### The classical exponent one

[`RiemannHypothesis/ZeroFreeClassical.lean`](RiemannHypothesis/ZeroFreeClassical.lean) then
replaces the exponent `9` by the classical exponent `1`:

```lean
theorem zeroFreeRegion : ZeroFreeRegion
-- ∃ c > 0, ∀ s, 3 ≤ |s.im| → 1 - c / Real.log |s.im| < s.re → riemannZeta s ≠ 0
```

Write `f(s) = −Re ζ'/ζ(s)`.  Three inequalities are combined: Mertens' `3-4-1` inequality
`0 ≤ 3f(σ) + 4f(σ+it) + f(σ+2it)` for `σ > 1`; the sharp real-axis bound
`f(σ) ≤ 1/(σ−1−a) + (σ−1)/a`, i.e. `(1+o(1))/(σ−1)`, proved from the Dirichlet series in
[`RiemannHypothesis/DirichletSeriesBounds.lean`](RiemannHypothesis/DirichletSeriesBounds.lean);
and the Hadamard expansion `f(σ+it) ≤ ½ log|t| + C − ∑_ρ Re 1/(s−ρ)`, whose zero terms are all
nonnegative for `σ > 1`, taken from the vendored `Zeta23` library together with its Stirling
estimates for the archimedean factors.  Evaluating at `σ = 1 + δ/log|t|` gives
`β ≤ 1 − c/log|γ|` for every nontrivial zero `ρ = β + iγ` of large ordinate, and the finitely
many zeroes of small ordinate are absorbed into the constant.  The constant obtained is
`c = 1/125` above a height `t₀` that the argument does not make explicit, so the region has the
classical *exponent* but an ineffective constant.

Reflecting this region in the critical line in the same way
([`RiemannHypothesis/ZeroLocationClassical.lean`](RiemannHypothesis/ZeroLocationClassical.lean))
gives the classical location of the zeroes:

```lean
theorem exists_zero_mem_shrinking_strip_classical :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, riemannZeta s = 0 → 3 ≤ |s.im| →
      c / Real.log |s.im| ≤ s.re ∧ s.re ≤ 1 - c / Real.log |s.im|

theorem exists_zero_abs_re_sub_half_le_classical :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, riemannZeta s = 0 → 3 ≤ |s.im| →
      |s.re - 1 / 2| ≤ 1 / 2 - c / Real.log |s.im|
```

The strip still widens to the full critical strip as `|im s| → ∞`, so this is very far from the
Riemann hypothesis — but it is the correct quantitative shape, and it is what the density
theorems sharpen.

## Growth inside the critical strip

The same continued Euler–Maclaurin representation, truncated at `N = ⌈|t|⌉`, gives the
classical *trivial bound* inside the strip
([`RiemannHypothesis/StripGrowth.lean`](RiemannHypothesis/StripGrowth.lean)):

```lean
theorem norm_riemannZeta_le_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re ≤ 1) (ht : 3 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8 / s.re * |s.im| ^ (1 - s.re) * (1 + Real.log |s.im|)
```

This improves on the linear bound `C(σ)(1+|t|)` of
[`RiemannHypothesis/Growth.lean`](RiemannHypothesis/Growth.lean): at `σ = 1/2` it reads
`O(√|t| log|t|)`.

## The convexity bound

The exponent above is halved by interpolating between the two edges of the strip.  On the
line `re s = 1` the logarithmic bound of
[`RiemannHypothesis/EulerMaclaurin.lean`](RiemannHypothesis/EulerMaclaurin.lean) applies; on
the imaginary axis, [`RiemannHypothesis/ImaginaryAxis.lean`](RiemannHypothesis/ImaginaryAxis.lean)
computes the modulus of the functional equation's `Γ`-factor *exactly*,

```lean
lemma norm_Gamma_one_sub_mul_I_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 - (t : ℂ) * I)‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t)

theorem norm_riemannZeta_mul_I_le {t : ℝ} (ht : 2 ≤ |t|) :
    ‖riemannZeta ((t : ℂ) * I)‖
      ≤ Real.sqrt (|t| / (2 * Real.pi)) * (6 + Real.log (1 + |t|))
```

from Euler's reflection formula, avoiding Stirling's formula (which mathlib does not provide
in a usable vertical-line form).  Phragmén–Lindelöf applied to
`((s−1)/(s+3))² ζ(s) (s(1−s)+4)^(−(1−s)/4−ε/2)` then gives, in
[`RiemannHypothesis/Convexity.lean`](RiemannHypothesis/Convexity.lean):

```lean
theorem norm_riemannZeta_le_convexity {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ ((1 - s.re) / 2 + e)

theorem norm_riemannZeta_le_critical_line {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ (1 / 4 + e)
```

The `ε` *can* be traded for a logarithm.  Running the same argument with `ε = 0` and dividing
in addition by the analytic function `log u(s)` — whose modulus lies between `log 4` and
`3(1 + log|t|)` on the closed strip, so that it absorbs the logarithm of the two boundary
bounds — gives, in
[`RiemannHypothesis/ConvexityLog.lean`](RiemannHypothesis/ConvexityLog.lean):

```lean
theorem norm_riemannZeta_le_convexity_log :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 3 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + Real.log |s.im|) * |s.im| ^ ((1 - s.re) / 2)
```

with one absolute constant, i.e. `O(|t|^(1/4) log|t|)` on the critical line.  The
logarithm-free bound `O(|t|^((1−σ)/2))`, and a fortiori the Lindelöf hypothesis (exponent `ε`
for every `σ ≥ 1/2`), are *not* proved; the board records both gaps under `M1-GROWTH`.

## The prime number theorem, reduced to one input

Mathlib does not contain the prime number theorem, but it does contain the two elementary
steps around it: `|ψ(x) − θ(x)| ≤ 2√x log x` and the Abel-summation identity
`π⌊x⌋ = θ(x)/log x + O(x/(log x)²)`.  Putting them together
([`RiemannHypothesis/PrimeCounting.lean`](RiemannHypothesis/PrimeCounting.lean)):

```lean
theorem primeCounting_tendsto_of_chebyshev_psi
    (h : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1)
```

This is an *implication*: the hypothesis `ψ(x) ~ x` is as hard as the prime number theorem
itself and is **not** proved here.  What the file does is isolate it — after this, the whole
remaining content of the board row `M1-PNT` is that one statement.

## Chebyshev's bounds `π(x) ≍ x/log x`

Mathlib proves Chebyshev's *upper* bounds `θ(x) ≤ x log 4` and `π(⌊x⌋) ≤ (log 4 + ε)x/log x`,
and lists the matching lower bound as a TODO.
[`RiemannHypothesis/ChebyshevLower.lean`](RiemannHypothesis/ChebyshevLower.lean) proves the
lower bound, by Chebyshev's central-binomial argument: every prime power occurring in
`C(2n, n)` is at most `2n`, so `log C(2n,n) ≤ ψ(2n)`, while `4ⁿ < n·C(2n,n)` for `n ≥ 4`.

```lean
theorem psi_ge_half_log_two_mul {x : ℝ} (hx : 12 ≤ x) :
    Real.log 2 / 2 * x ≤ Chebyshev.psi x

theorem primeCounting_asymptotic_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      c * (x / Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
        (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * (x / Real.log x)
```

These are two-sided bounds of the right order of magnitude, with the explicit constants
`c = log 2/4` and `C = log 4 + 1`; they are *not* the prime number theorem, which asserts
that the ratio tends to `1`.

## Mertens' first theorem

[`RiemannHypothesis/Mertens.lean`](RiemannHypothesis/Mertens.lean) proves
`∑_{n ≤ x} Λ(n)/n = log x + O(1)` with an explicit constant, from the identity
`∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d)⌊N/d⌋` and the sandwich `N log N − N ≤ ∑_{n ≤ N} log n ≤ N log N`:

```lean
theorem mertens_first {x : ℝ} (hx : 1 ≤ x) :
    |mertensSum x - Real.log x| ≤ Real.log 4 + 4 + Real.log 2

theorem mertens_first_prime {x : ℝ} (hx : 1 ≤ x) :
    |primeLogSum x - Real.log x| ≤ Real.log 4 + 12 + Real.log 2
```

The second is the prime form `∑_{p ≤ x} log p / p = log x + O(1)`: the proper prime powers
`p^k`, `k ≥ 2`, contribute at most `8` in total, by a geometric tail and the telescoping
bound `∑_{m ≥ 2} 1/(m√m) ≤ 2`.

Mathlib contains none of Mertens' three theorems.  The sharper form, with the error tending
to `−γ`, and Mertens' third theorem are not proved here.

## Mertens' second theorem

[`RiemannHypothesis/MertensSecond.lean`](RiemannHypothesis/MertensSecond.lean) proves
`∑_{p ≤ x} 1/p = log log x + O(1)` with an explicit constant:

```lean
theorem mertens_second_nat {N : ℕ} (hN : 2 ≤ N) :
    |primeRecipSum N - Real.log (Real.log N)| ≤ 50

theorem mertens_second {x : ℝ} (hx : 4 ≤ x) :
    |primeRecipSum x - Real.log (Real.log x)| ≤ 52
```

The proof is Abel summation (`sum_by_parts_Ioc`) applied to the prime form of the first
theorem: with `A(n) = ∑_{p ≤ n} log p/p = log n + O(1)` and `f(n) = 1/log n`,

```
∑_{p ≤ N} 1/p = A(N) f(N) + ∑_{n < N} A(n) (f(n) − f(n+1)),
```

the main term `∑_n log n (f(n) − f(n+1))` telescopes against `log log(n+1) − log log n` up to
an error controlled by `∑_{n ≥ 2} 1/n² ≤ 1`, and the error term is controlled by
`∑_n (f(n) − f(n+1)) = f(2) − f(N)`.  Mathlib has the divergence of `∑_p 1/p`
(`Nat.Primes.not_summable_one_div`) but not the rate.

Only boundedness of the error is proved: the existence of the Meissel–Mertens constant
`M ≈ 0.2615`, i.e. the convergence of `∑_{p ≤ x} 1/p − log log x`, is not.  The constants are
not sharp — almost all of `50` is twice the constant of the first theorem in prime form.

## Mertens' third theorem, in bounded form

[`RiemannHypothesis/MertensThird.lean`](RiemannHypothesis/MertensThird.lean) deduces from the
second theorem that the Mertens product is comparable to `log x`:

```lean
theorem mertens_third {x : ℝ} (hx : 4 ≤ x) :
    |Real.log (primeProd x) - Real.log (Real.log x)| ≤ 54

theorem mertens_third_bounds {x : ℝ} (hx : 4 ≤ x) :
    Real.exp (-54) * Real.log x ≤ primeProd x ∧
      primeProd x ≤ Real.exp 54 * Real.log x
```

The bridge is the elementary estimate `t ≤ −log(1 − t) ≤ t + 2t²` for `0 < t ≤ 1/2`, summed
over the primes `p ≤ x` with `t = 1/p`; the quadratic error is absorbed by `∑_{n ≥ 2} 1/n² ≤ 1`.

The sharp form `∏_{p ≤ x} (1 − 1/p)⁻¹ ∼ e^γ log x` is *not* proved: that needs the
convergence of `∑_{p ≤ x} 1/p − log log x`, which is not proved here either.

## The heat-kernel origin of the functional equation

[`RiemannHypothesis/Spectral.lean`](RiemannHypothesis/Spectral.lean) makes the classical
chain `theta modularity → Mellin → functional equation` explicit.  `θ(it) = ∑_{n∈ℤ} e^{−πn²t}`
is the trace of the heat semigroup on `ℝ/ℤ`, and

```lean
theorem jacobiTheta_imaginary_axis {t : ℝ} (ht : 0 < t) :
    jacobiTheta (I * (1 / t : ℝ)) = (Real.sqrt t : ℂ) * jacobiTheta (I * (t : ℝ))

theorem completedRiemannZeta_eq_mellin_jacobiTheta {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s
      = mellin (fun t : ℝ => (jacobiTheta (I * (t : ℝ)) - 1) / 2) (s / 2)
```

so the completed zeta function is the Mellin transform of the heat trace, and the symmetry
`s ↦ 1 − s` is the symmetry `t ↦ 1/t` of that trace.  The two ends of the chain — Poisson
summation and `Λ(1−s) = Λ(s)` — are Mathlib's, and the file marks them as cited rather than
reproved.  This is the geometric reading of the *functional equation* only: the spectral
reading of the *zeroes* (Hilbert–Pólya) remains conjectural.

## The `Ξ` function: the hypothesis as a reality statement

[`RiemannHypothesis/Xi.lean`](RiemannHypothesis/Xi.lean) defines

```lean
def xiPoint (z : ℂ) : ℂ := 1 / 2 + z * I

def riemannXi (z : ℂ) : ℂ :=
  (xiPoint z * (xiPoint z - 1) * completedRiemannZeta₀ (xiPoint z) + 1) / 2
```

which is `½ s(s−1)Λ(s)` at `s = ½ + iz` written so that it is *manifestly* entire: the two
simple poles of `Λ` are cleared by `s(s−1)`, and Mathlib's entire `Λ₀` makes the cancellation
an identity, `s(s−1)Λ(s) = s(s−1)Λ₀(s) + 1`.  Since `Λ(s) = Γ_ℝ(s)ζ(s)` is zero-free for
`re s ≥ 1`, and `Λ(1−s) = Λ(s)` carries this to `re s ≤ 0`,

```lean
theorem riemannXi_eq_zero_iff {z : ℂ} :
    riemannXi z = 0 ↔
      0 < (xiPoint z).re ∧ (xiPoint z).re < 1 ∧ riemannZeta (xiPoint z) = 0

theorem zeta_iff_xi : ZetaForm ↔ XiForm
```

where `XiForm` is `∀ z, Ξ(z) = 0 → im z = 0`.  So the Riemann hypothesis is exactly the
assertion that this one entire function has only real zeroes.

## The de Bruijn–Newman family

[`RiemannHypothesis/DeBruijnNewman.lean`](RiemannHypothesis/DeBruijnNewman.lean) defines the
weight

```
Φ(u) = ∑_{n ≥ 1} (2π²n⁴e^{9u} − 3πn²e^{5u}) e^{−πn²e^{4u}}
```

and the heat flow applied to the Fourier representation of the completed zeta function,

```lean
def dbnH (t : ℝ) (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ),
  ((Real.exp (t * u ^ 2) * dbnPhi u : ℝ) : ℂ) * Complex.cos ((u : ℂ) * z)

theorem differentiable_dbnH (t : ℝ) : Differentiable ℂ (dbnH t)
```

The analytic content is the decay estimate `|Φ(u)| ≤ C e^{9u} e^{−πe^{4u}}` for `u ≥ 0`
(`abs_dbnPhi_le`), which dominates both the Gaussian factor `e^{tu²}` and the exponential
growth `e^{u|Im z|}` of the cosine; differentiating under the integral sign then makes `H_t`
entire for every real `t`.  The de Bruijn–Newman constant is
`Λ = inf {t | every zero of H_t is real}` (`dbnLambda`), and the two results of the
literature — `RH ↔ Λ ≤ 0` (de Bruijn 1950, Newman 1976) and `Λ ≥ 0` (Rodgers–Tao 2018) — are
recorded as `Prop`s, `DeBruijnNewmanEquivRH` and `DeBruijnNewmanNonnegative`, and are *not*
proved here.

## `H_0` really is `Ξ`

[`RiemannHypothesis/ThetaW.lean`](RiemannHypothesis/ThetaW.lean) and
[`RiemannHypothesis/FourierXi.lean`](RiemannHypothesis/FourierXi.lean) supply the missing
identification of `H_0` with the Riemann `Ξ` function.  Write

```
ω(x) = ∑_{n ≥ 1} e^{−πn²x},        W(u) = e^u ω(e^{4u}).
```

The theta functional equation becomes `W(−u) = W(u) + sinh u` (`wFun_neg`), and
differentiating it at `0` gives `W'(0) = −1/2` (`wFun'_zero`).  Differentiating the series
twice termwise identifies the de Bruijn–Newman weight: `Φ = (W'' − W)/8` (`dbnPhi_eq`).

On the `Ξ` side, folding the Mellin integral of Mathlib's modified theta kernel from `(0,1]`
onto `(1,∞)` and substituting `x = e^{4u}` gives Riemann's representation

```lean
theorem riemannXi_eq_integral (z : ℂ) :
    riemannXi z = 1 / 2 - (4 * z ^ 2 + 1) * ∫ u in Ioi (0 : ℝ), (wFun u : ℂ) * cos (2 * u * z)
```

On the `H_0` side, `u ↦ W'(u)cos(uz) + zW(u)sin(uz)` is an explicit antiderivative of
`(W'' + z²W)(u)cos(uz)`, so integrating over `(0,∞)` leaves only the boundary term
`−W'(0) = 1/2`.  Combining the two halves:

```lean
theorem dbnH_zero_eq_riemannXi (z : ℂ) : dbnH 0 z = riemannXi (z / 2) / 8

theorem zeta_iff_dbnH_zero : ZetaForm ↔ ∀ z : ℂ, dbnH 0 z = 0 → z.im = 0
```

The second statement has **no hypotheses**: it is an unconditional reformulation of the
Riemann hypothesis as the `t = 0` case of the de Bruijn–Newman reality question.  (The
earlier conditional theorem `zeta_iff_dbnH_zero_of_eq` in `Xi.lean` assumed `H_0 = Ξ` on the
nose, which is *false* — the correct normalisation halves the variable and divides by `8` —
so that statement is vacuous; it is kept, with a docstring recording the correction.)

It bears repeating that this is an *equivalence*, not a proof: the Riemann hypothesis is
open, and no term of type `ZetaForm` exists anywhere in this repository.

## Counting the zeroes: `N(T) = O(T log T)`

[`RiemannHypothesis/ZeroCountingLemma.lean`](RiemannHypothesis/ZeroCountingLemma.lean) proves a
Jensen-type counting lemma without going through Jensen's formula.  If `f` is holomorphic on the
closed disc of radius `3r` about `c`, bounded there by `M`, and `f c ≠ 0`, then dividing out the
zeroes one at a time with `dslope` and applying the maximum modulus principle gives

```lean
theorem pow_three_card_mul_norm_le : 3 ^ Z.card * ‖f c‖ ≤ M

theorem card_le_log_div_log_three : (Z.card : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log 3
```

for any finite set `Z` of zeroes of `f` in the disc of radius `r`; `finite_setOf_zeros` and
`ncard_setOf_zeros_le` then bound the whole zero set.  Zeroes are counted *without* multiplicity.

[`RiemannHypothesis/XiGrowth.lean`](RiemannHypothesis/XiGrowth.lean) supplies the growth input.
It writes `ξ(s) = (s(s−1)Λ₀(s) + 1)/2`, which is the same entire function as `Xi.lean`'s
`riemannXi ∘ xiPoint`, proves the functional equation `ξ(1−s) = ξ(s)` and, combining the
repository's convexity and near-line bounds for `ζ` with `‖Γ(s)‖ ≤ Γ(re s)` and a crude
`Γ(x) ≤ e^{x log x}`, the order-one bound

```lean
theorem norm_xiFn_le :
    ∃ C > 0, ∀ s : ℂ, ‖xiFn s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))
```

Feeding this into the counting lemma at centre `2` and radius `4(T+2)`,
[`RiemannHypothesis/ZeroCount.lean`](RiemannHypothesis/ZeroCount.lean) obtains

```lean
def nontrivialZeros (T : ℝ) : Set ℂ :=
  {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T}

theorem finite_nontrivialZeros (T : ℝ) : (nontrivialZeros T).Finite

theorem ncard_nontrivialZeros_le :
    ∃ C > 0, ∀ T ≥ 2, ((nontrivialZeros T).ncard : ℝ) ≤ C * T * Real.log T
```

What is *not* proved: the matching lower bound, the sharp asymptotic
`N(T) = (T/2π)log(T/2πe) + O(log T)`, counting with multiplicity, and any explicit value for
`C` — the constant is produced by an existential and is far from optimal.  The sharp form needs
Stirling asymptotics for `Γ` on vertical lines, which Mathlib does not yet have.

## Summing over the zeroes: `∑_ρ 1/(1+γ²) < ∞`

The counting bound has an immediate analytic consequence, the convergence statement that is the
input to the Hadamard product for `ξ` and to the explicit formula.
[`RiemannHypothesis/ZeroSum.lean`](RiemannHypothesis/ZeroSum.lean) proves

```lean
def nontrivialZeroSet : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

theorem countable_nontrivialZeroSet : nontrivialZeroSet.Countable

theorem summable_inv_one_add_im_sq :
    Summable (fun ρ : nontrivialZeroSet => 1 / (1 + ((ρ : ℂ).im) ^ 2))

theorem summable_inv_norm_sq :
    Summable (fun ρ : nontrivialZeroSet => 1 / ‖(ρ : ℂ)‖ ^ 2)
```

The proof is a dyadic decomposition against `N(T) ≤ C·T·log T`: the zeroes with
`2^k ≤ |γ| < 2^(k+1)` number at most `C·2^(k+1)·(k+1)` and each contributes at most `4^(−k)`, so
the `k`-th block contributes `O((k+1)2^(−k))` and `∑_k (k+1)2^(−k) = 4`.  A decomposition into
unit bands would not converge with only the global counting bound available.  Summability is
obtained from the resulting uniform bound `∑_{ρ ∈ S} 1/(1+γ²) ≤ 8C`, valid for every *finite*
set `S` of nontrivial zeroes.

What is *not* proved: multiplicities are ignored throughout; the Hadamard product itself is not
constructed; and nothing in that file asserts that a nontrivial zero exists — that is proved
separately, in the next section.

The same decomposition, run with a sharper weight, gives the exponent of convergence of the zero
set.  [`RiemannHypothesis/ZeroExponent.lean`](RiemannHypothesis/ZeroExponent.lean) proves

```lean
theorem summable_inv_norm_rpow {e : ℝ} (he : 0 < e) :
    Summable (fun ρ : nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-(1 + e)))
```

with the uniform bound over finite subsets `sum_inv_norm_rpow_le`: the `k`-th dyadic block still
has `O(2^k k)` elements, but each now contributes at most `2^(−k(1+e))`, and
`∑_k (k+1) 2^(−k e)` converges for every `e > 0`.  So the exponent of convergence of the
nontrivial zeroes is at most `1`, which is the analytic input for a Hadamard product of genus
`1` for `ξ`.

That the exponent is *exactly* `1` is now proved as well, in
[`RiemannHypothesis/ZeroExponentOne.lean`](RiemannHypothesis/ZeroExponentOne.lean):

```lean
theorem not_summable_inv_norm : ¬ Summable (fun ρ : nontrivialZeroSet => ‖(ρ : ℂ)‖⁻¹)

theorem sInf_exponent_summable_eq_one :
    sInf {e : ℝ | Summable (fun ρ : nontrivialZeroSet => ‖(ρ : ℂ)‖ ^ (-e))} = 1
```

The missing input used to be the lower bound `N(T) ≫ T log T`; it is now available (the
Riemann–von Mangoldt lower bound `exists_mul_le_windowCount_zero`), and combined with "at least
five sixths of the zeroes are distinct" it gives the same bound for the number of *distinct*
zeroes of ordinate in `(0, T]` (`exists_mul_le_windowCountDistinct_zero`).  Each of them has
`‖ρ‖ ≤ 1 + T`, so for `0 < e ≤ 1` the partial sum of `‖ρ‖^(−e)` over that window is at least
`c·(T log T)/(1+T) ≥ (c/2) log T`, which tends to infinity; a summable family has all its finite
partial sums bounded by its sum, so no exponent `e ≤ 1` converges.  The set of admissible
exponents is therefore exactly `(1, ∞)`.

## How fast does `∑_ρ 1/‖ρ‖` diverge?  Like `(log T)²`

[`RiemannHypothesis/ZeroSumLogSq.lean`](RiemannHypothesis/ZeroSumLogSq.lean) pins down the rate:

```lean
theorem exists_sum_inv_norm_asymptotic :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c * (Real.log T) ^ 2 ≤ ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹ ∧
        ∑ ρ ∈ (windowZeros_finite 0 T).toFinset, ‖ρ‖⁻¹ ≤ C * (Real.log T) ^ 2
```

Both halves are the same dyadic decomposition of the window `(0, T]` into the ranges
`2^k < γ ≤ 2^(k+1)`, which carry pairwise disjoint sets of zeroes.  A zero of that range has
`2^k < ‖ρ‖ ≤ 1 + 2^(k+1)`, so the block contributes `≍ 2^(−k)·N(2^k, 2^(k+1))`, and the
Riemann–von Mangoldt count — the lower bound from the vendored formula, the upper bound from the
Jensen-type `ncard_nontrivialZeros_le` — puts `N(2^k, 2^(k+1)) ≍ 2^k k`.  Each of the `≍ log T`
blocks therefore contributes `≍ k ≍ log T`, and the total is `≍ (log T)²`.  The classical
asymptotic `∑_{0 < γ ≤ T} 1/‖ρ‖ ~ (log T)²/(4π)`, with its constant, is not claimed: the two
constants here are not explicit and do not match.

## How many zeroes are there?  `N(T) ~ (T/2π) log T`

The counting results above are one-sided or up to an unspecified constant: the Jensen-type
`ncard_nontrivialZeros_le` gives `N(T) = O(T log T)`, and `exists_mul_le_windowCount_zero` gives
`N(T) ≫ T log T`.  [`RiemannHypothesis/RvMCumulative.lean`](RiemannHypothesis/RvMCumulative.lean)
determines the constant:

```lean
theorem tendsto_windowCount_zero_div :
    Tendsto (fun T : ℝ => (windowCount 0 T : ℝ) / (T * Real.log T)) atTop
      (𝓝 (1 / (2 * Real.pi)))
```

quantitatively `|N(0, T) − (T/2π) log T| ≤ A(T + (log T)²)`.  The vendored `Zeta23` development
proves Riemann–von Mangoldt on a *dyadic window*, `|N(T, 2T) − (T/2π)(log T − κ)| ≤ C log T` with
`κ = log 2π − 2 log 2 + 1`; writing a large `T` as `2^n s` with `s` in a fixed bounded range and
telescoping `N(0, 2^n s) = N(0, s) + ∑_{j<n} N(2^j s, 2^(j+1) s)` reduces the cumulative count to
the two geometric sums `∑_{j<n} 2^j` and `∑_{j<n} j 2^j`, whose closed forms produce the main
term `(T/2π) log T` plus `O(T)`.  The `n ≍ log T` windows each carry an error `O(log T)`, for a
total `O((log T)²)`.  Zeroes are counted here *with* multiplicity.  Only the leading term is
pinned down: the classical secondary term `−(T/2π)(1 + log 2π)` and the sharp error `O(log T)`
are not claimed.

## How multiple can a zero be?  `O(log |γ|)`

Every counting statement above counts zeroes *without* multiplicity, and nothing in them excluded
a nontrivial zero of enormous order.
[`RiemannHypothesis/MultiplicityCountingLemma.lean`](RiemannHypothesis/MultiplicityCountingLemma.lean)
supplies the missing estimate, in the same style as the counting lemma: if `f` is holomorphic on
`B(c, R)`, bounded by `M` on the boundary circle, and vanishes to order at least `m a` at each
point `a` of a finite set inside the concentric disc of radius `R/4`, then

```lean
theorem pow_three_sum_mul_norm_le {c : ℂ} {R : ℝ} (hR : 0 < R) (S : Finset ℂ) :
    ∀ (f : ℂ → ℂ) (M : ℝ) (m : ℂ → ℕ), DiffContOnCl ℂ f (ball c R) →
      (∀ z ∈ sphere c R, ‖f z‖ ≤ M) → (∀ a ∈ S, dist a c ≤ R / 4) →
      (∀ a ∈ S, (m a : ℕ∞) ≤ analyticOrderAt f a) →
      3 ^ (∑ a ∈ S, m a) * ‖f c‖ ≤ M
```

Each zero is divided out with its full multiplicity: `G = f / (· − a)^(m a)` extends
holomorphically across `a`, the maximum principle bounds `‖G c‖` by `M / (3R/4)^(m a)`, and
`‖G c‖ = ‖f c‖ / ‖c − a‖^(m a)`, so each point gains a factor `3^(m a)`.  Taking `S = {a}` gives
the single-zero form `pow_three_pow_mul_norm_le : 3 ^ m * ‖f c‖ ≤ M`.

Applied to `ξ` in the disc of radius `20` about `4 + iT` — the disc that produced the local count
— [`RiemannHypothesis/ZeroMultiplicityBound.lean`](RiemannHypothesis/ZeroMultiplicityBound.lean)
gives the classical bound on the order of a zero of `ζ`, and, in the large disc that produced
`N(T) = O(T log T)`, the Riemann–von Mangoldt bound *with* multiplicity — at the same order:

```lean
theorem analyticOrderAt_xiFn_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderAt xiFn s = analyticOrderAt riemannZeta s

theorem zeroMultiplicity_le_log_abs_im {ρ : ℂ} (hρ : ρ ∈ nontrivialZeroSet) (him : 25 ≤ |ρ.im|) :
    (zeroMultiplicity ρ : ℝ) ≤ 41 * Real.log |ρ.im|

theorem sum_zeroMultiplicity_zerosNearHeight_le {T : ℝ} (hT : 25 ≤ T) :
    ((∑ᶠ ρ ∈ zerosNearHeight T, zeroMultiplicity ρ : ℕ) : ℝ) ≤ 41 * Real.log T

theorem multCount_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (multCount T : ℝ) ≤ C * T * Real.log T
```

What is *not* proved: these are upper bounds only — no zero of `ζ` is known to be multiple, and
nothing here produces one.  `O(T log T)` is the right order of magnitude, but the constant is not
explicit, and neither the asymptotic `N(T) ~ (T/2π) log(T/2π)` nor any lower bound follows.

## The critical strip is not empty of zeroes

Every other result above about the zeroes in the strip — the counting bounds, the symmetries, the
summability — remains true if the strip contains no zero at all.
[`RiemannHypothesis/ZeroExists.lean`](RiemannHypothesis/ZeroExists.lean) closes that gap:

```lean
theorem exists_xiFn_eq_zero : ∃ s : ℂ, xiFn s = 0

theorem nontrivialZeroSet_nonempty : nontrivialZeroSet.Nonempty

theorem exists_riemannZeta_eq_zero_of_mem_strip :
    ∃ s : ℂ, riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1
```

The argument is Hadamard's, cut down to what a single zero needs. If `ξ` had no zero then, `ℂ`
being convex, the entire function `ξ'/ξ` would have a primitive and `ξ = e^g` with `g` entire; the
order-one bound `‖ξ(s)‖ ≤ exp(C(1+‖s‖)log(2+‖s‖))` then bounds `re g`, and Borel–Carathéodory
turns that into `‖g‖ = O(R^{3/2})` on `|z| ≤ R/2`, whence Cauchy's estimate for the second
derivative gives `g'' ≡ 0` and `g(z) = a + bz`. So `‖ξ‖` would grow at most exponentially along
the real axis. But it does not: `ξ(2n+2) = (n+1)(2n+1)π^{−(n+1)}Γ(n+1)ζ(2n+2)` and `ζ ≥ 1/2` for
real arguments `≥ 3`, so `‖ξ(2n+2)‖ ≥ π^{−(n+1)}·n!`, and `n!` beats every `B·Lⁿ`. A zero of `ξ`
is a zero of `ζ` in the open strip by `riemannXi_eq_zero_iff`.

What is *not* proved: the argument is by contradiction, so it locates nothing — no bound on the
height of the zero, and of course nothing about its real part.

## Infinitely many zeroes

[`RiemannHypothesis/ZeroInfinite.lean`](RiemannHypothesis/ZeroInfinite.lean) pushes the same
argument to its conclusion:

```lean
theorem exists_rootMultiset_factorization {f : ℂ → ℂ} (hf : Differentiable ℂ f) {w : ℂ}
    (hw : f w ≠ 0) (S : Finset ℂ) (hS : ∀ z, f z = 0 → z ∈ S) :
    ∃ (m : Multiset ℂ) (g : ℂ → ℂ), (∀ ρ ∈ m, ρ ∈ S) ∧ Differentiable ℂ g ∧ (∀ z, g z ≠ 0) ∧
      ∀ z, f z = rootProd m z * g z

theorem infinite_nontrivialZeroSet : nontrivialZeroSet.Infinite
```

If the strip held only finitely many zeroes, `ξ` would be `∏(z − ρ)` times a nowhere-vanishing
entire function — the factorization is an induction on the total order of vanishing, dividing out
one root at a time through `dslope`, with `analyticOrderAt_mul` to see the order drop. The
nowhere-vanishing factor is again `exp G`, and `re G` still obeys the order-one bound: the
product factor has modulus `≥ 1` outside a disc containing all the roots, and `G` is bounded on
that disc by compactness. So `G` is linear, the polynomial factor contributes only
`(2+M)^d e^{d(n+1)}`, and `‖ξ‖` would again be at most exponential along the real axis — which
the factorial lower bound forbids.

What is *not* proved: nothing is located or counted — no bound on the height of the `n`-th zero
and no lower bound for `N(T)`; and multiplicities are not counted in the statement.

## The counting function is unbounded

[`RiemannHypothesis/ZeroCountLower.lean`](RiemannHypothesis/ZeroCountLower.lean) puts the two
previous sections together with the upper bound. Write
`N(T) = #{ρ : ζ ρ = 0, 0 < re ρ < 1, |im ρ| ≤ T}`; each `N(T)` is finite
(`finite_nontrivialZeros`) while the whole zero set is infinite, so:

```lean
theorem monotone_ncard_nontrivialZeros : Monotone fun T : ℝ => (nontrivialZeros T).ncard

theorem exists_mem_nontrivialZeroSet_lt_abs_im (T : ℝ) :
    ∃ s ∈ nontrivialZeroSet, T < |s.im|

theorem tendsto_ncard_nontrivialZeros_atTop :
    Tendsto (fun T : ℝ => ((nontrivialZeros T).ncard : ℝ)) atTop atTop
```

In particular the nontrivial zeroes are not confined to any horizontal strip: above every height
there is another one.

What is *not* proved: no rate. The divergence inherits the non-effectivity of the infinitude
proof, so nothing here approaches the classical `N(T) ~ (T/2π)log(T/2πe)`, and it is only the
upper bound `N(T) = O(T log T)` that is quantitative.

## Conjugation symmetry of the zero set, and the parity of `N(T)`

[`RiemannHypothesis/ZeroSymmetryCount.lean`](RiemannHypothesis/ZeroSymmetryCount.lean) reads the
symmetries of [`Symmetry.lean`](RiemannHypothesis/Symmetry.lean) as statements about the zero set
itself. No nontrivial zero is real (`ζ` does not vanish on `(0,1)`), so the zero set splits into
its upper and lower halves; conjugation exchanges the two halves bijectively, and `s ↦ 1 − s`
preserves the set:

```lean
theorem im_ne_zero_of_mem_nontrivialZeroSet {s : ℂ} (hs : s ∈ nontrivialZeroSet) : s.im ≠ 0

theorem conj_image_upperNontrivialZeroSet :
    (starRingEnd ℂ) '' upperNontrivialZeroSet = lowerNontrivialZeroSet

theorem infinite_upperNontrivialZeroSet : upperNontrivialZeroSet.Infinite

theorem ncard_nontrivialZeros_eq_two_mul (T : ℝ) :
    (nontrivialZeros T).ncard = 2 * (upperNontrivialZeros T).ncard

theorem even_ncard_nontrivialZeros (T : ℝ) : Even (nontrivialZeros T).ncard
```

What is *not* proved: multiplicities are not tracked, so the parity statement counts *distinct*
zeroes; and nothing here says anything about the real parts, hence nothing about the hypothesis.

## Off-line zeroes come in quadruples

[`RiemannHypothesis/OffLineQuadruple.lean`](RiemannHypothesis/OffLineQuadruple.lean) composes the
two symmetries into the reflection `criticalReflect s = 1 − conj s` in the *critical line*, which
fixes the imaginary part and sends `re s` to `1 − re s`. A nontrivial zero off the critical line
therefore has three further companions of the same height, all distinct from it and from each
other, and the count of off-line zeroes up to height `T` is divisible by four:

```lean
theorem criticalReflect_mem_nontrivialZeros {T : ℝ} {s : ℂ} (hs : s ∈ nontrivialZeros T) :
    criticalReflect s ∈ nontrivialZeros T

theorem ncard_offLineNontrivialZeros_eq_four_mul (T : ℝ) :
    (offLineNontrivialZeros T).ncard = 4 * (leftUpperNontrivialZeros T).ncard

theorem four_dvd_ncard_offLineNontrivialZeros (T : ℝ) :
    4 ∣ (offLineNontrivialZeros T).ncard

theorem four_le_ncard_offLineNontrivialZeros {T : ℝ} {s : ℂ} (hs : s ∈ nontrivialZeros T)
    (hre : s.re ≠ 1 / 2) : 4 ≤ (offLineNontrivialZeros T).ncard
```

The last statement is the Riemann hypothesis read from the other side: *a counterexample never
comes alone*. What is *not* proved: nothing here says whether any off-line zero exists — that is
the hypothesis itself — and, multiplicities being untracked, the counts are of distinct zeroes.

## The symmetries preserve multiplicities

The two sections above count *distinct* zeroes.
[`RiemannHypothesis/ZeroMultiplicitySymmetry.lean`](RiemannHypothesis/ZeroMultiplicitySymmetry.lean)
removes that caveat. The key general fact is that vanishing order is preserved by conjugation,
and the key arithmetic fact is that inside the strip `ζ` and the completed zeta function `Λ`
vanish to the same order, so the functional equation `Λ(1 − s) = Λ(s)` transfers orders across
the critical line:

```lean
lemma analyticOrderAt_conj_conj (f : ℂ → ℂ) (z₀ : ℂ) :
    analyticOrderAt (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) ((starRingEnd ℂ) z₀)
      = analyticOrderAt f z₀

theorem zeroMultiplicity_conj {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zeroMultiplicity ((starRingEnd ℂ) s) = zeroMultiplicity s

theorem zeroMultiplicity_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zeroMultiplicity (1 - s) = zeroMultiplicity s

theorem even_multCount (T : ℝ) : Even (multCount T)

theorem four_dvd_offLineMultCount (T : ℝ) : 4 ∣ offLineMultCount T
```

Here `multCount T` and `offLineMultCount T` are the counting functions of the nontrivial zeroes
of height at most `T`, resp. of those off the critical line, counted **with multiplicity**.

## Two thirds of the zeroes are simple and on the critical line

[`RiemannHypothesis/Zeta23Bridge.lean`](RiemannHypothesis/Zeta23Bridge.lean) restates, in this
repository's vocabulary, the headline results of the `Zeta23` library vendored under
[`vendor/zeta23`](vendor/zeta23) (Apache 2.0; see [`vendor/zeta23/NOTICE`](vendor/zeta23/NOTICE)),
which formalizes *"More than two thirds of the zeros of the Riemann zeta function are simple and
on the critical line"*.  The counting is over the nontrivial zeroes with ordinate in a window
`(T₁, T₂]`: `windowCount` (`N`, with multiplicity), `windowCountDistinct` (`N_d`),
`windowCountOnLine` (`N₀*`) and `windowCountSimpleOnLine` (`N₀ˢ`).

```lean
theorem two_thirds_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (windowCount T (2 * T) : ℝ) ≤ windowCountSimpleOnLine T (2 * T)

theorem five_sixths_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (5 / 6 - ε) * (windowCount T (2 * T) : ℝ) ≤ windowCountDistinct T (2 * T)
```

Cumulative forms over `(0, T]`, the sharper Montgomery–Taylor window, and the same statements for
a primitive Dirichlet character are proved alongside.
[`RiemannHypothesis/EightyPercent.lean`](RiemannHypothesis/EightyPercent.lean) turns the `5/6`
bound into an `ε`-free statement, `0.8·N(T,2T) ≤ N_d(T,2T)` for all large `T`.

## Eighty per cent of the distinct zeroes are simple

[`RiemannHypothesis/EightyPercentSimple.lean`](RiemannHypothesis/EightyPercentSimple.lean) counts
the *simple* zeroes, `windowCountSimple` (`Nˢ`), against the number of distinct zeroes `N_d`.
Every non-simple zero contributes at least `2` to `N`, so `2·N_d ≤ Nˢ + N` in every window
(`two_mul_windowCountDistinct_le_add`); combined with the Montgomery–Taylor distinctness constant
`(3 − 1/c₁*)/2 = 0.83625…`, which exceeds `5/6` because `c₁* > 3/4`
(`mtConstant_gt_three_quarters`, proved from Mathlib's Taylor bounds for `sin` and `cos`), this
gives an `ε`-free eighty per cent:

```lean
theorem eighty_percent_simple_among_distinct :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.8 : ℝ) * (windowCountDistinct T (2 * T) : ℝ) ≤ windowCountSimple T (2 * T)
```

with a cumulative form over `(0, T]`, the ratio form
`4/5 ≤ liminf Nˢ(0,T)/N_d(0,T)` (the denominator tends to infinity, so the quotient is not
vacuous), the `ε`-form `Nˢ/N_d ≥ 4/5 − ε` coming from Theorem C alone, the `ξ'` analogue `0.92·N_{d,ξ'} ≤ Nˢ_{ξ'}`, and the Dirichlet analogue
`0.8·N_{d,χ} ≤ Nˢ_χ` for a primitive character `χ` modulo `q > 1`.

What is *not* proved: these are `liminf` statements, with no effective `T₀`, and a proportion
bound says nothing about the remaining zeroes — the hypothesis itself is untouched.  In
particular the proportion of zeroes *on the critical line* remains `2/3`; raising it to `80 %`
is an open research problem, and no such statement is proved here.  That target is written down
as a `Prop`, `EightyPercentOnCriticalLine`, in the style of
[`RiemannHypothesis/Partial.lean`](RiemannHypothesis/Partial.lean) — a statement, not a theorem —
together with what it would give: at most a fifth of the zeroes off the critical line.  A
*conditional* route past 80 % for the distinct zeroes is developed in the next section.

## Sixty-seven per cent on the critical line, without an `ε`

Theorem D gives `liminf N₀*(T,2T)/N(T,2T) ≥ 2 − 1/c₁* = 0.67250…`, but as an `ε`-statement.
[`RiemannHypothesis/SixtySevenPercent.lean`](RiemannHypothesis/SixtySevenPercent.lean) removes the
`ε` with a decimal constant strictly above `2/3`:

```lean
theorem sixty_seven_percent_on_critical_line :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.67 : ℝ) * (windowCount T (2 * T) : ℝ) ≤ windowCountOnLine T (2 * T)
```

with the simple-zero form, the cumulative form over `(0, T]`, and the complementary
`N_off(T,2T) ≤ 0.33·N(T,2T)`.  The numerical work is a sharper bound for the Montgomery–Taylor
constant, `c₁* > 88/117 = 0.75213…` (`mtConstant_gt_eightyEight_div_117`) — the `3/4` of
[`EightyPercentSimple.lean`](RiemannHypothesis/EightyPercentSimple.lean) only returns `2/3`.  It
rests on `tan(1/√2) > 44√2/73`, proved from Mathlib's `x − x³/6 < sin x` together with the quartic
bound `cos x ≤ 1 − x²/2 + x⁴/24`, which is proved in the same file by a monotonicity argument.
The margin is thin and exact: `0.67` needs `tan(1/√2) > 50√2/83`, and `44·83 = 3652 > 3650 = 50·73`.

This does not change the method or its constant: `0.6725…` is what Theorem D yields, and the
underlying analytic work is the vendored `Zeta23` library's.

## A route past eighty per cent on the critical line (conditional)

[`RiemannHypothesis/EightyPercentRoute.lean`](RiemannHypothesis/EightyPercentRoute.lean) records a
*route* to a proportion beyond 80 % on the critical line, and proves everything on it except one
classical input.  Unconditionally it proves that the zeroes of `ζ` and the zeroes of `ξ'` in the
dyadic window have the same Riemann–von Mangoldt main term `(T/2π)·ℓ₁(T)`, hence

```lean
lemma abs_xiDerivWindowCount_sub_windowCount_le :
    ∃ C S : ℝ, 0 ≤ C ∧ 1 ≤ S ∧ ∀ T ≥ S,
      |(xiDerivWindowCount T (2 * T) : ℝ) - (windowCount T (2 * T) : ℝ)| ≤ C * Real.log T

lemma xiDerivWindowCount_le_one_add_mul {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ T ≥ S,
      (xiDerivWindowCount T (2 * T) : ℝ) ≤ (1 + ε) * (windowCount T (2 * T) : ℝ)
```

using that `N(T,2T)/log T → ∞` (`exists_le_windowCount_mul_log`).  The missing input is a
*counting comparison between the off-line zeroes of `ζ` and the off-line zeroes of `ξ′`*, written
down as a `Prop` in the style of [`Partial.lean`](RiemannHypothesis/Partial.lean) and **not**
proved here:

```lean
def SpeiserTransfer : Prop :=
  ∃ C S : ℝ, ∀ T ≥ S,
    (windowCountOffLine T (2 * T) : ℝ) ≤ xiDerivWindowCountBad T (2 * T) + C * Real.log T
```

> **Correction (2026-08-23).**  Earlier versions of this section, and of the docstrings in
> `EightyPercentRoute.lean`, called this hypothesis "the counting form of Speiser's theorem
> (Levinson–Montgomery)".  That attribution is withdrawn.  The Levinson–Montgomery theorem is a
> statement about the zeroes of `ζ′`, not about the zeroes of `ξ′`, and it does not prove this
> `Prop`.  Moreover the hypothesis is *stronger* than the `80 %` target it was introduced to reach:
> with multiplicity it is equivalent to the reverse comparison of the on-line counts
> (`speiserOffLineTransfer_iff_xiDerivOnLineDominates`) and already yields `86.864 %` on the
> critical line, and the only proof of it available in this repository is from the Riemann
> hypothesis itself (`speiserOffLineTransfer_of_zetaStripForm`).  What *is* unconditional is the
> reverse inequality, by Rolle's theorem for Hardy's `Ξ`; see the two sections below.  The same
> correction is recorded on the task board (rows `M1-EIGHTY-CRITICAL-ROUTE`, `M1-SPEISER-ROLLE`)
> and in the module docstrings.

Under it, together with the unconditional `86.864 %` bound for the zeroes of `ξ'`, the route gives
`N_off ≤ (0.13136 + ε)·N`, and therefore

```lean
theorem eighty_four_percent_distinct_on_critical_line_of_speiserTransfer (h : SpeiserTransfer) :
    ∃ S : ℝ, ∀ T ≥ S,
      (0.84 : ℝ) * (windowCountDistinct T (2 * T) : ℝ) ≤ (windowCountOnLine T (2 * T) : ℝ)

theorem seventy_percent_on_critical_line_of_speiserTransfer (h : SpeiserTransfer) :
    ∃ S : ℝ, ∀ T ≥ S,
      (0.7 : ℝ) * (windowCount T (2 * T) : ℝ) ≤ (windowCountOnLine T (2 * T) : ℝ)
```

— at least 84 % of the *distinct* zeroes on the line (so the 80 % target for the distinct zeroes,
`EightyPercentOnCriticalLineDistinct`), and 70 % of the zeroes counted with multiplicity.

What this does **not** do: it does not move the unconditional proportion on the critical line,
which stays at `2/3` (`2 − 1/c₁* = 0.67250…` with the optimal window); it does not prove
`SpeiserTransfer`, which needs the argument principle for `ξ'/ξ` on the left half of the critical
strip; and even granting it, 80 % *with multiplicity* is out of reach on this route, because the
multiplicity budget `N_d ≥ (5/6)·N` caps it at 70 %.

## The part of Speiser's transfer that is unconditional

[`RiemannHypothesis/SpeiserMultiple.lean`](RiemannHypothesis/SpeiserMultiple.lean) proves the
part of that missing input which is *local*, and therefore needs no argument principle.  Inside
the critical strip `ξ` and `ζ` vanish to the same order (`analyticOrderAt_xiFn_eq`), so at a
nontrivial zero the derivative loses exactly one order of vanishing:

```lean
theorem xiDerivMultiplicity_add_one {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : xiDerivMultiplicity s + 1 = zeroMultiplicity s
```

Hence a *multiple* zero of `ζ` off the critical line is a zero of `ξ′` off the critical line
(`xiDerivFn_eq_zero_of_multiple`), while a *simple* one is not a zero of `ξ′` at all
(`xiDerivFn_ne_zero_of_simple`) — which is precisely why `SpeiserTransfer` needs a global
input.  Counting the transferred zeroes against the `ξ′` bad count gives the inequality of
`SpeiserTransfer`, restricted to the multiple zeroes and with no `O(log T)` term:

```lean
theorem ncard_windowZerosOffLineMultiple_le_bad (T₁ T₂ : ℝ) :
    ((windowZerosOffLineMultiple T₁ T₂).ncard : ℝ) ≤ xiDerivWindowCountBad T₁ T₂

theorem ncard_windowZerosOffLineMultiple_le_windowCount {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ T ≥ S,
      ((windowZerosOffLineMultiple T (2 * T)).ncard : ℝ) ≤
        (0.13136 + ε) * (windowCount T (2 * T) : ℝ)
```

The second is unconditional: at most `13.136 %` of the zeroes of `ζ` are both multiple and off
the critical line (Theorem C alone gives only `1/6 = 16.67 %` for all the multiple zeroes).  It
does **not** bound the off-line zeroes that are simple, which is the whole content of
`SpeiserTransfer` and remains unproved.

Because `m_{ξ′}(ρ) = m_ζ(ρ) − 1` is an *equality*, both bounds also hold in multiplicity-weighted
form, with each multiple off-line zero counted `m_ζ(ρ) − 1` times rather than once:

```lean
def windowMultipleOffLineExcess (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ windowZerosOffLineMultiple T₁ T₂, (zeroMultiplicity ρ - 1)

theorem windowMultipleOffLineExcess_le_windowCount {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ T ≥ S,
      (windowMultipleOffLineExcess T (2 * T) : ℝ) ≤
        (0.13136 + ε) * (windowCount T (2 * T) : ℝ)
```

## Rolle on the critical line, and what the Speiser transfer really costs

The three modules [`CriticalLineXi.lean`](RiemannHypothesis/CriticalLineXi.lean),
[`SpeiserRolle.lean`](RiemannHypothesis/SpeiserRolle.lean) and
[`SpeiserEquivalence.lean`](RiemannHypothesis/SpeiserEquivalence.lean), together with the
multiplicity bookkeeping of
[`EightyPercentMultiplicity.lean`](RiemannHypothesis/EightyPercentMultiplicity.lean), settle
what the hypothesis `SpeiserTransfer` is worth, and prove unconditionally the half of it that
real analysis alone can give.

On the critical line `ξ` is real: `ξ(conj s) = conj ξ(s)` and `conj(1/2 + it) = 1 - (1/2 + it)`
combine with the functional equation to give `Ξ(t) = ξ(1/2 + it) ∈ ℝ`.  Hardy's `Ξ` is
differentiable with `Ξ′(t) = Re(i·ξ′(1/2 + it))`, and the imaginary part of `i·ξ′(1/2 + it)`
vanishes identically, so a critical point of `Ξ` is a genuine zero of `ξ′`.  Rolle's theorem
then gives, with no hypothesis at all:

```lean
theorem exists_xiDerivFn_onLine_eq_zero {a b : ℝ} (hab : a < b)
    (ha : xiFn (onLine a) = 0) (hb : xiFn (onLine b) = 0) :
    ∃ c ∈ Ioo a b, xiDerivFn (onLine c) = 0
```

Counting the resulting zeroes — one strictly between each pair of consecutive on-line zeroes of
`ζ`, plus the multiplicity dropped by differentiation at the multiple ones — gives the on-line
comparison with multiplicity, again unconditionally:

```lean
theorem windowCountOnLineMult_le_xiDerivWindowCountOnLineMult (T₁ T₂ : ℝ) :
    windowCountOnLineMult T₁ T₂ ≤ xiDerivWindowCountOnLineMult T₁ T₂ + 1
```

Because `N_{ξ′}` and `N` agree up to `O(log T)`, the on-line and off-line comparisons are two
faces of the same statement:

```lean
def SpeiserOffLineTransfer : Prop :=
  ∃ C S : ℝ, ∀ T ≥ S,
    (windowCountOffLineMult T (2 * T) : ℝ) ≤
      (xiDerivWindowCountOffLineMult T (2 * T) : ℝ) + C * Real.log T

def XiDerivOnLineDominates : Prop :=
  ∃ C S : ℝ, ∀ T ≥ S,
    (xiDerivWindowCountOnLineMult T (2 * T) : ℝ) ≤
      (windowCountOnLineMult T (2 * T) : ℝ) + C * Real.log T

theorem speiserOffLineTransfer_iff_xiDerivOnLineDominates :
    SpeiserOffLineTransfer ↔ XiDerivOnLineDominates
```

What Rolle gives is exactly the *reverse* of each: `N₀ᵐ ≤ N₀ᵐ_{ξ′} + 1` above, and
equivalently

```lean
theorem xiDerivWindowCountOffLineMult_le_windowCountOffLineMult :
    ∃ C S : ℝ, ∀ T ≥ S,
      (xiDerivWindowCountOffLineMult T (2 * T) : ℝ) ≤
        (windowCountOffLineMult T (2 * T) : ℝ) + C * Real.log T
```

So `ξ′` has, on the critical line, at least as many zeroes as `ζ` and, off it, at most as many:
the transfer hypothesis asks for the two counts to be comparable in *both* directions, and only
one direction is elementary.  This also fixes the price of the hypothesis.  Under it the
`86.864 %` bound for `ξ′` transfers verbatim to `ζ`, counted with multiplicity:

```lean
theorem eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer
    (h : SpeiserOffLineTransfer) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 - ε) * (windowCount T (2 * T) : ℝ) ≤ (windowCountOnLineMult T (2 * T) : ℝ)
```

Hence the hypothesis of the conditional route is *stronger than the `80 %` target it is used to
reach*, and it is not the Levinson–Montgomery theorem, which is a statement about the zeroes of
`ζ′`, not of `ξ′`.  The docstrings in
[`EightyPercentRoute.lean`](RiemannHypothesis/EightyPercentRoute.lean) have been corrected
accordingly.  The unconditional proportion on the critical line in this repository is unchanged:
`2/3`, and `0.6725…` with the optimal window.

## The easy half of Speiser's theorem, quantitatively

Speiser's theorem states that the hypothesis is equivalent to `ξ′` having no zero with
`re s < 1/2`.  Its hard half is what `SpeiserOffLineTransfer` would supply.  Its *easy* half
follows from the Rolle machinery above, at the cost of the `O(log T)` error term of the two
Riemann–von Mangoldt formulas: if every nontrivial zero of `ζ` is on the critical line, then
`ξ′` has at least `N(T,2T) - 1` zeroes on the line and only `N(T,2T) + O(log T)` in total, so

```lean
theorem xiDerivWindowCountOffLineMult_le_log_of_zetaStripForm (h : ZetaStripForm) :
    ∃ C S : ℝ, ∀ T ≥ S,
      (xiDerivWindowCountOffLineMult T (2 * T) : ℝ) ≤ C * Real.log T

theorem not_zetaStripForm_of_xiDeriv_offLine_gt
    (h : ∀ C S : ℝ, ∃ T ≥ S,
      C * Real.log T < (xiDerivWindowCountOffLineMult T (2 * T) : ℝ)) :
    ¬ ZetaStripForm
```

— the second being the contrapositive, a criterion for *disproving* the hypothesis from off-line
zeroes of `ξ′`.  The same file records `speiserOffLineTransfer_of_zetaStripForm`: the transfer
hypothesis of the conditional route is itself implied by the Riemann hypothesis, trivially,
because then `ζ` has no off-line zeroes at all.

## The argument principle on a rectangle, and Littlewood's counting identity

Every remaining counting goal in this repository — Bohr–Landau (almost all zeroes near the
critical line), a density theorem for `N(σ,T)`, any zero count for `ζ`, `ξ` or `ξ′` — needs the
same tool, which mathlib does not have: a bridge between a contour integral around a rectangle
and the *number of zeroes inside it*, counted with multiplicity.
The repository builds it once, for an arbitrary function of a complex variable, rather than as a
component of one route.  It is split in two:
[`RectangleZeroCount.lean`](RiemannHypothesis/RectangleZeroCount.lean) holds everything that
needs mathlib only — the count, its finiteness, its monotonicity, and the layer-cake identity —
and [`RectangleArgumentPrinciple.lean`](RiemannHypothesis/RectangleArgumentPrinciple.lean) holds
the part that rests on the vendored `Zeta23` contour machinery.

```lean
noncomputable def rectZeroCount (f : ℂ → ℂ) (z w : ℂ) : ℕ :=
  ∑ᶠ ρ ∈ rectZeros f z w, analyticOrderNatAt f ρ

theorem rectangle_argument_principle (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleIntegral' (logDeriv f) z w = (rectZeroCount f z w : ℂ)

theorem rectangle_argument_principle_weighted (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w)) (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℂ) * g ρ
```

The analytic content is the vendored `Zeta23.Analytic.rectangleIntegral'_mul_logDeriv`; what is
added here is the counting form — the right-hand side is a natural number, the zero set is
produced rather than assumed, and no property of `ζ` appears anywhere.

The second half is the layer-cake identity behind **Littlewood's lemma**.  Write `N(σ)` for the
number of zeroes of `f`, with multiplicity, in the truncated rectangle `[σ, w.re] × [z.im, w.im]`.
Then

```lean
theorem integral_rectZeroCount_eq_finsum (hre : z.re ≤ w.re)
    (hfin : (rectZeros f z w).Finite) :
    (∫ σ in z.re..w.re, (rectZeroCount f (leftCorner σ z) w : ℝ))
      = ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re)
```

which is unconditional and needs no analyticity — only that the zero set is finite — and,
combined with the argument principle,

```lean
theorem integral_rectangleIntegral'_logDeriv_eq_finsum_of_border (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    (∫ σ in z.re..w.re, (RectangleIntegral' (logDeriv f) (leftCorner σ z) w).re)
      = ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re)
```

The zero-freeness assumed is only on the border of the rectangle itself; the border of a
truncation may well meet a zero.  An earlier form of this statement instead asked `f` to be
zero-free on the border of *every* truncation, and that hypothesis is vacuous: a zero `ρ` inside
the rectangle lies on the left edge of the truncation at `σ = re ρ`, so the hypothesis forces
`rectZeros f z w = ∅` and both sides to vanish.  This is now itself a theorem,
`rectZeros_eq_empty_of_forall_leftCorner_border`; the earlier statement is kept with a warning
in its docstring and superseded by the one above.  The corrected proof rests on
`rectangleBorder_leftCorner_subset` — the border of the truncation at `σ` sits inside the border
of the whole rectangle together with the line `re s = σ` — so the argument principle applies for
every `σ` outside the finite set of real parts of zeroes, which is enough for the integral.

**What is not proved here.**  Littlewood's lemma proper replaces the inner contour integral by
boundary data; that step is carried out below, in
[`ArgumentSegment.lean`](RiemannHypothesis/ArgumentSegment.lean) and
[`Littlewood.lean`](RiemannHypothesis/Littlewood.lean).  Nothing in these two files is a
statement about `ζ`, and nothing in them moves the unconditional proportion of zeroes on the
critical line.

### The modulus half of Littlewood's lemma

The *modulus* needs no branch of the logarithm, and
[`LogModulusSegment.lean`](RiemannHypothesis/LogModulusSegment.lean) proves that half outright.
For `g : ℝ → ℂ` differentiable and nonzero at `x`, `log ‖g‖` has derivative `re (g′/g)` there
(`hasDerivAt_log_norm_comp`, proved by differentiating `½ log (normSq g)`), whence the
fundamental theorem of calculus on each side of a rectangle:

```lean
theorem integral_re_logDeriv_horizontal {f : ℂ → ℂ} {a b t : ℝ}
    (hf : ∀ σ ∈ Set.uIcc a b, AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ σ ∈ Set.uIcc a b, f ((σ : ℂ) + t * I) ≠ 0) :
    (∫ σ in a..b, (logDeriv f ((σ : ℂ) + t * I)).re)
      = Real.log ‖f ((b : ℂ) + t * I)‖ - Real.log ‖f ((a : ℂ) + t * I)‖

theorem integral_im_logDeriv_vertical {f : ℂ → ℂ} {σ c d : ℝ}
    (hf : ∀ t ∈ Set.uIcc c d, AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (h0 : ∀ t ∈ Set.uIcc c d, f ((σ : ℂ) + t * I) ≠ 0) :
    (∫ t in c..d, -(logDeriv f ((σ : ℂ) + t * I)).im)
      = Real.log ‖f ((σ : ℂ) + d * I)‖ - Real.log ‖f ((σ : ℂ) + c * I)‖
```

[`RectangleLogModulus.lean`](RiemannHypothesis/RectangleLogModulus.lean) assembles the four
sides.  Around a closed border the increments of `log ‖f‖` telescope, so

```lean
theorem re_rectangleIntegral_logDeriv_eq_zero
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    (RectangleIntegral (logDeriv f) z w).re = 0

theorem im_rectangleIntegral'_logDeriv_eq_zero
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    (RectangleIntegral' (logDeriv f) z w).im = 0
```

the second saying that `(1/2πi) ∮_{∂R} f′/f` is a *real* number.  Only the border is
constrained: `f` may have zeroes inside, or fail to be analytic there, and the statements still
hold — which is what distinguishes them from the argument principle, which assumes analyticity
on the closed rectangle and then identifies that real number with a zero count.

### The argument half, and Littlewood's lemma

The *argument* half is where a logarithm is unavoidable, and
[`ArgumentSegment.lean`](RiemannHypothesis/ArgumentSegment.lean) builds one by integration
rather than by choosing a branch cut.  For `g : ℝ → ℂ` differentiable and nonvanishing on the
segment joining `a` and `b`, the primitive `F u = ∫_a^u g′/g` makes `u ↦ g u · exp (−F u)` have
derivative zero, so `exp (∫_a^b g′/g) = g b / g a`, and `θ u = arg (g a) + im (F u)` is a
continuous argument of `g` along the segment:

```lean
theorem exists_continuousOn_arg {g g' : ℝ → ℂ} {a b : ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x) (h0 : ∀ x ∈ Set.uIcc a b, g x ≠ 0)
    (hc : ContinuousOn (fun x => g' x / g x) (Set.uIcc a b)) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Set.uIcc a b) ∧
      (∀ u ∈ Set.uIcc a b, g u = (‖g u‖ : ℂ) * Complex.exp (θ u * I)) ∧
      ∀ u ∈ Set.uIcc a b, ∀ v ∈ Set.uIcc a b, θ v - θ u = (∫ x in u..v, g' x / g x).im
```

Around the four sides of a rectangle the ratios `g b / g a` telescope, so `exp (∮_{∂R} f′/f) = 1`
and the winding number is an **integer**:

```lean
theorem exists_int_rectangleIntegral'_logDeriv
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (h0 : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    ∃ n : ℤ, RectangleIntegral' (logDeriv f) z w = (n : ℂ)
```

again assuming nothing inside the rectangle, where `f` may have zeroes or poles.  Combined with
`im_rectangleIntegral'_logDeriv_eq_zero` above, this upgrades "the normalized contour integral is
real" to "it is an integer".

[`Littlewood.lean`](RiemannHypothesis/Littlewood.lean) supplies the remaining Fubini step and
assembles the lemma.  The double integral of `re (f′/f)` across the rectangle may be computed in
either order even though the integrand blows up at the zeroes inside — integrability comes from
[`LogDerivIntegrable.lean`](RiemannHypothesis/LogDerivIntegrable.lean), where the singularity is
bounded by `C/‖s − ρ‖`, integrable in the plane — and integrating first in `σ` gives the
increment of `log ‖f‖` along a horizontal line for all but the finitely many heights that meet a
zero.  With the counting identity above this gives **Littlewood's lemma**:

```lean
theorem littlewood_lemma (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    2 * Real.pi * ∑ᶠ ρ ∈ rectZeros f z w, (analyticOrderNatAt f ρ : ℝ) * (ρ.re - z.re)
      = (∫ t in z.im..w.im,
            (Real.log ‖f ((z.re : ℂ) + t * I)‖ - Real.log ‖f ((w.re : ℂ) + t * I)‖))
        + (∫ σ in z.re..w.re, (HIntegral (logDeriv f) σ w.re z.im).im)
        - (∫ σ in z.re..w.re, (HIntegral (logDeriv f) σ w.re w.im).im)
        + (w.re - z.re) * (VIntegral (logDeriv f) w.re z.im w.im).im
```

and `littlewood_lemma_arg` rewrites the two horizontal terms as increments `θb w.re − θb σ`,
`θt w.re − θt σ` of genuine continuous arguments of `f` along the bottom and the top side.

[`ZetaLittlewood.lean`](RiemannHypothesis/ZetaLittlewood.lean) specializes this to `ζ`: for a
rectangle inside the open critical strip carrying no zero of `ζ` on its border, the analyticity
hypothesis is discharged by `analyticOnNhd_riemannZeta_rectangle`, and the set summed over is
`Rectangle z w ∩ nontrivialZeroSet` — the nontrivial zeroes of `ζ` inside the rectangle and
nothing else (`zeta_littlewood_lemma`, `zeta_littlewood_lemma_arg`,
`zeta_littlewood_lemma_nontrivialZeros`).

[`RectangleLogModulusZeros.lean`](RiemannHypothesis/RectangleLogModulusZeros.lean) removes the
border hypothesis from the modulus half.  For a density estimate the rectangle must be allowed
to contain — and to touch — zeroes, so
`integral_integral_re_logDeriv_eq_integral_log_norm_of_zeros` assumes only that `f` is analytic
on an open set containing the closed rectangle, that `f` vanishes nowhere identically, and that
its zeroes in the rectangle are finitely many; zeroes on the two vertical sides are allowed, and
the heights at which a horizontal side meets a zero form a null set, so the height integral is
unaffected.  The integrability across the zeroes is transported from the plane to the coordinate
rectangle through `Complex.measurableEquivRealProd`.

Littlewood's lemma is an identity, not a bound: turning it into a zero-density estimate needs an
upper bound for `log ‖ζ‖` on the right edge and a lower bound on the left edge, and neither is
proved here.  The zero-density theorem of the previous section is obtained by the other
classical route, Jensen's inequality on discs, and does not use this identity.

### The same statements, for `ζ`

[`ZetaRectangleCount.lean`](RiemannHypothesis/ZetaRectangleCount.lean) attaches that machinery
to the object of the repository, discharging the hypotheses a counting argument for `ζ` would
otherwise have to carry.  The zeroes of `ξ` in a rectangle are exactly the nontrivial zeroes of
`ζ` inside it, `rectZeros_xiFn_eq`, and that set is finite for *every* rectangle with no side
hypothesis, `rectZeros_xiFn_finite`; inside the open strip `ζ` and `ξ` vanish to the same order,
so the counts agree, `rectZeroCount_riemannZeta_eq_xiFn`; and a rectangle inside the strip
avoids the pole at `s = 1`, so `ζ` is analytic on a neighbourhood of it,
`analyticOnNhd_riemannZeta_rectangle`.  Hence

```lean
theorem zeta_rectangle_argument_principle (hz0 : 0 < z.re) (hw1 : w.re < 1) (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0) :
    RectangleIntegral' (logDeriv riemannZeta) z w = (rectZeroCount riemannZeta z w : ℂ)

theorem integral_rectZeroCount_riemannZeta_eq_finsum (hz0 : 0 < z.re) (hw1 : w.re < 1)
    (hre : z.re ≤ w.re) :
    (∫ σ in z.re..w.re, (rectZeroCount riemannZeta (leftCorner σ z) w : ℝ))
      = ∑ᶠ ρ ∈ rectZeros riemannZeta z w, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)

theorem integral_rectangleIntegral'_logDeriv_riemannZeta_eq_finsum_of_border (hz0 : 0 < z.re)
    (hw1 : w.re < 1) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w, riemannZeta s ≠ 0) :
    (∫ σ in z.re..w.re, (RectangleIntegral' (logDeriv riemannZeta) (leftCorner σ z) w).re)
      = ∑ᶠ ρ ∈ rectZeros riemannZeta z w, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)
```

These are identities, not bounds: they give no estimate for the number of zeroes in a rectangle,
and every quantitative zero count in this repository still comes from the Jensen route of
[`ZeroCount.lean`](RiemannHypothesis/ZeroCount.lean).

> **Verification status (2026-08-24).**  All three files compile inside a full `lake build` of
> the repository, and their results depend only on `propext`, `Classical.choice` and
> `Quot.sound`; `./scripts/audit.sh` checks both, and is green.  (The earlier caveat, that
> `RectangleArgumentPrinciple.lean` had been checked only against restated `Zeta23` signatures,
> is discharged: the toolchain the repository pins is now the one the mathlib revision required
> by `lakefile.toml` needs, and the file is compiled against the real `Zeta23` declarations.)

## Hardy's theorem, and the ordinates of the zeroes on the line

[`RiemannHypothesis/CriticalLine.lean`](RiemannHypothesis/CriticalLine.lean) deduces from the
proportion results that the counting functions tend to infinity, hence:

```lean
theorem infinite_criticalLineZeroSet : criticalLineZeroSet.Infinite

theorem infinite_simpleCriticalLineZeroSet : simpleCriticalLineZeroSet.Infinite
```

[`RiemannHypothesis/CriticalLineOrdinates.lean`](RiemannHypothesis/CriticalLineOrdinates.lean)
sharpens this from "infinitely many" to "of arbitrarily large ordinate", using the finiteness of
each window, and transports it to the `Ξ`-variable:

```lean
theorem exists_mem_criticalLineZeroSet_lt_im (T : ℝ) : ∃ s ∈ criticalLineZeroSet, T < s.im

theorem exists_mem_simpleCriticalLineZeroSet_lt_im (T : ℝ) :
    ∃ s ∈ simpleCriticalLineZeroSet, T < s.im

theorem exists_mem_criticalLineZeroSet_im_lt (T : ℝ) : ∃ s ∈ criticalLineZeroSet, s.im < T

theorem infinite_setOf_riemannXi_ofReal_eq_zero : {t : ℝ | riemannXi (t : ℂ) = 0}.Infinite

theorem not_bddAbove_setOf_riemannXi_ofReal_eq_zero : ¬ BddAbove {t : ℝ | riemannXi (t : ℂ) = 0}

theorem not_bddBelow_setOf_riemannXi_ofReal_eq_zero : ¬ BddBelow {t : ℝ | riemannXi (t : ℂ) = 0}
```

The third-from-last is Hardy's theorem read as "`Ξ` has infinitely many real zeroes"; the
hypothesis is the statement that `Ξ` has *no other* zeroes.

[`RiemannHypothesis/PartialProved.lean`](RiemannHypothesis/PartialProved.lean) discharges the
corresponding `Prop`s of [`Partial.lean`](RiemannHypothesis/Partial.lean) — `HardyTheorem`,
Selberg's positive proportion, Levinson's `1/3` and Conrey's `2/5` — from the stronger bound
`liminf N₀(T)/N(T) ≥ 2/3` in the counting functions used there.

## At most a third of the zeroes lie off the critical line

[`RiemannHypothesis/OffLine.lean`](RiemannHypothesis/OffLine.lean) reads the same bound from the
other side, which is the side the hypothesis is about.  Splitting a window's zeroes according to
whether their real part is `1/2` gives `N_off + N₀* = N_d`, and `N_d ≤ N`, so the two-thirds
bound becomes an upper bound on the zeroes that could possibly violate the hypothesis:

```lean
theorem one_third_off_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (windowCountOffLine T (2 * T) : ℝ) ≤ (1 / 3 + ε) * windowCount T (2 * T)

theorem limsup_offCriticalZeroCount_div_le_one_third :
    limsup (fun T : ℝ => (offCriticalZeroCount T : ℝ) / (zeroCount T : ℝ)) atTop ≤ 1 / 3
```

The hypothesis is the statement that this count is *zero*; `1/3` is as far as the argument goes.

## The prime number theorem and the explicit formula

[`RiemannHypothesis/PrimeNumberTheorem.lean`](RiemannHypothesis/PrimeNumberTheorem.lean) closes
the reduction of [`PrimeCounting.lean`](RiemannHypothesis/PrimeCounting.lean) by supplying its one
remaining input, `ψ(x) ~ x`, from the vendored port of `PrimeNumberTheoremAnd`:

```lean
theorem chebyshev_psi_div_tendsto_one : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)

theorem prime_number_theorem :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1)
```

[`RiemannHypothesis/ExplicitFormula.lean`](RiemannHypothesis/ExplicitFormula.lean) records the
smoothed Perron formula and Weil's explicit formula: for `k ∈ C_c²(ℝ)` with `h = testTransform k`,
the sum `∑_ρ m_ρ h(γ_ρ)` over the nontrivial zeroes converges absolutely and equals the polar,
prime and archimedean terms.

## Five routes to the hypothesis

Besides the *equivalent reformulations* above, the repository proves five **sufficient
conditions**: classical statements, none of them known, each of which would imply the Riemann
hypothesis.  All five share one analytic skeleton,
[`RiemannHypothesis/AbelDirichlet.lean`](RiemannHypothesis/AbelDirichlet.lean): if the partial
sums `A(N) = ∑_{n ≤ N} a(n)` of an arithmetic function satisfy `A(N) = O(N^(θ+ε))` for every
`ε > 0`, then summation by parts turns the conditionally convergent Dirichlet series
`∑ a(n) n^(−s)` into the absolutely convergent `∑ A(n)(n^(−s) − (n+1)^(−s))`, holomorphic on
`re s > θ`; the identity theorem on the *convex* half-plane then propagates an identity valid
for `re s > 1` down to `re s > 1/2`, where it forbids `ζ` from vanishing.

| route | hypothesis (`∀ ε > 0`) | file | theorem |
|---|---|---|---|
| Mertens | `M(N) = ∑_{n ≤ N} μ(n) = O(N^(1/2+ε))` | [`MoebiusCriterion.lean`](RiemannHypothesis/MoebiusCriterion.lean) | `zeta_of_mertensBound` |
| Redheffer | `\|det (A n)\| = O(n^(1/2+ε))` for the Redheffer matrices | [`Redheffer.lean`](RiemannHypothesis/Redheffer.lean) | `zeta_of_redhefferBound` |
| Chebyshev | `ψ(N) − N = O(N^(1/2+ε))` | [`ChebyshevCriterion.lean`](RiemannHypothesis/ChebyshevCriterion.lean) | `zeta_of_chebyshevBound` |
| weighted Möbius | `∑_{n ≤ N} μ(n)/n = O(N^(−1/2+ε))` | [`MoebiusOverNCriterion.lean`](RiemannHypothesis/MoebiusOverNCriterion.lean) | `zeta_of_littleMertensBound` |
| Liouville | `L(N) = ∑_{n ≤ N} λ(n) = O(N^(1/2+ε))` | [`LiouvilleCriterion.lean`](RiemannHypothesis/LiouvilleCriterion.lean) | `zeta_of_liouvilleBound` |

The arithmetic inputs differ: the Möbius routes use `ζ(s)·L(μ,s) = 1`, the Chebyshev route uses
`−ζ'/ζ` and the rigidity lemma `f' = S·f ⇒ f ≠ 0` of
[`LogDerivCriterion.lean`](RiemannHypothesis/LogDerivCriterion.lean), and the Liouville route
uses `ζ(s)·L(λ,s) = ζ(2s)`, proved here from the identity `∑_{d ∣ n} λ(d) = 1` for `n` a square and `0` otherwise.
What is unconditional in this direction is much weaker: `\|∑_{n ≤ N} μ(n)/n\| ≤ 1`
([`MertensSums.lean`](RiemannHypothesis/MertensSums.lean)) and `∑_{n ≤ N} λ(n)⌊N/n⌋ = ⌊√N⌋`
([`LiouvilleSums.lean`](RiemannHypothesis/LiouvilleSums.lean)).

## Elementary Möbius sums

`RiemannHypothesis/MertensSums.lean` collects the two hyperbola reindexings of the pairs
`(d, e)` with `d·e ≤ m` — the bijection `(d, e) ↦ (d·e, e)`, stated for an arbitrary
`f : ℕ → ℤ` — and the two classical consequences:

```lean
theorem sum_moebius_mul_div {N : ℕ} (hN : 1 ≤ N) : ∑ n ∈ Icc 1 N, ((N / n : ℕ) : ℤ) * μ n = 1
theorem abs_littleMertens_le_one (N : ℕ) : |littleMertens N| ≤ 1
```

The second is Landau's inequality `|∑_{n ≤ N} μ(n)/n| ≤ 1`: it follows from the first by
replacing `⌊N/n⌋` with `N/n`, at the cost of `N − 1` fractional parts of absolute value at
most one.  It is unconditional, and very far from the `O(N^{-1/2+ε})` bound that the criterion
in `MoebiusOverNCriterion.lean` needs — that bound is equivalent to the hypothesis and is not
proved here.

## Redheffer's determinant: the hypothesis as linear algebra

`RiemannHypothesis/Redheffer.lean` turns the Mertens criterion into a statement about
determinants of `0/1` matrices.  The **Redheffer matrix** `A n` has `(i, j)` entry (rows and
columns standing for `1, …, n`) equal to `1` when `j = 1` or `i ∣ j`, and `0` otherwise, and

```lean
theorem det_redheffer {n : ℕ} (hn : 1 ≤ n) : (redheffer n).det = mertens n
```

is Redheffer's theorem: its determinant is the Mertens function `M(n) = ∑_{k ≤ n} μ(k)`.  The
proof is the factorisation `A = B · C` (`redheffer_eq_divisorMatrix_mul_mertensColumn`) into the
divisibility matrix `B` — unit upper triangular, so `det B = 1` — and the matrix `C` that agrees
with the identity off its first column, whose first column is `d ↦ M(⌊n/d⌋)`; `C` is lower
triangular with diagonal `(M(n), 1, …, 1)`.  Checking the first column of the product is exactly
the Möbius identity

```lean
theorem sum_mertens_div {m : ℕ} (hm : 1 ≤ m) : ∑ d ∈ Icc 1 m, mertens (m / d) = 1
```

which follows from `∑_{d ∣ k} μ(d) = [k = 1]` after the hyperbola reindexing of the pairs
`(d, e)` with `d·e ≤ m`.

Combining this with the Mertens criterion of `RiemannHypothesis/MoebiusCriterion.lean` gives a
purely linear-algebraic sufficient condition for the hypothesis:

```lean
theorem zeta_of_redhefferBound (h : RedhefferBoundForm) : ZetaForm
```

where `RedhefferBoundForm` says `|det (A n)| = O(n^{1/2+ε})` for every `ε > 0`.  As always in
this repository, that is an implication from an unproved hypothesis: no term of type
`RedhefferBoundForm` (nor of type `ZetaForm`) exists here.

## Weil's positivity criterion, and the test functions it is about

`RiemannHypothesis/WeilPositivity.lean` writes the right-hand side of the explicit formula as
the **Weil functional** `weilFunctional k`, defines the class

```lean
def IsPositiveTestFunction (k : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 k ∧ HasCompactSupport k ∧
    ∀ r : ℝ, ∃ c : ℝ, 0 ≤ c ∧ testTransform k r = (c : ℂ)
```

and states Weil's criterion `ZetaForm ↔ ∀ k, IsPositiveTestFunction k → 0 ≤ (weilFunctional k).re`
as a `Prop`.  Only the forward implication is proved there.

`RiemannHypothesis/WeilTestFunctions.lean` shows that the class is the classical one and that
it is not vacuous.  With `g^*(x) = conj (g (-x))` and `weilSquare g = g ⋆ g^*`, the paper's
transform is mathlib's Fourier integral,

```lean
theorem testTransform_ofReal (k : ℝ → ℂ) (r : ℝ) :
    testTransform k (r : ℂ) = 𝓕 k (-(r / (2 * Real.pi)))
```

so the convolution theorem and `𝓕 (g^*) = conj ∘ 𝓕 g` give

```lean
theorem testTransform_weilSquare {g : ℝ → ℂ} (hg : Integrable g) (r : ℝ) :
    testTransform (weilSquare g) (r : ℂ) = ((‖𝓕 g (-(r / (2 * Real.pi)))‖ ^ 2 : ℝ) : ℂ)
```

a nonnegative real.  Hence every convolution square of a `C²` compactly supported function is a
positive test function (`isPositiveTestFunction_weilSquare`), and since
`weilSquare g 0 = ∫ ‖g t‖²`, a bump function produces a nonzero one:

```lean
theorem exists_isPositiveTestFunction_ne_zero :
    ∃ k : ℝ → ℂ, IsPositiveTestFunction k ∧ k ≠ 0
```

The converse direction of Weil's criterion — positivity implies the hypothesis — remains
unproved, and no term of type `WeilPositivityCriterion` or `ZetaForm` exists here.

## Provenance and status

This repository is a *statement-and-equivalence* formalization: the Riemann hypothesis itself
is open and is stated, not proved.  What is proved is the equivalence of its formulations,
together with the unconditional theory around it — the growth and convexity bounds, the
zero-free region, Mertens' theorems, the prime number theorem, the zero-counting results,
the Bohr–Landau zero-density theorem, Hardy's theorem and the proportion results above, several
of which are restated from the vendored `Zeta23` library under
[`vendor/zeta23`](vendor/zeta23).  The
proofs depend on `propext`, `Classical.choice` and `Quot.sound` only.  See
[`formalization.yaml`](formalization.yaml) for the full provenance.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
