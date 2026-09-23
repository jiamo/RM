# Where the `2/3` in `vendor/zeta23` comes from

*A methodology report on the vendored `Zeta23` library, written from its Lean sources.*

This repository uses `Zeta23.two_thirds_on_critical_line` as a black box in some thirty places
(`RiemannHypothesis/Zeta23Bridge.lean` and everything downstream of it), but nowhere states what
method produces the constant. This note reconstructs the argument from the Lean sources, says
exactly where each constant in the chain comes from, and records what an audit of the statement
does and does not establish. File and declaration references are to `vendor/zeta23`.

## 0. What is actually claimed

```
theorem Zeta23.two_thirds_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)
```
(`Zeta23/Unconditional.lean`, definitionally `Zeta23.thmA₀`). Unfolding the counting functions
(`Zeta23/Statement.lean`, checked with `#print`):

* `IsNontrivialZero ρ  ↔  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1`;
* `zeroMult ρ = (analyticOrderAt riemannZeta ρ).toNat`;
* `Ncount T₁ T₂ = ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ` — zeros **with multiplicity**;
* `N0star T₁ T₂ = (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1/2}).ncard` — **distinct** zeros on the line.

So the numerator ignores multiplicity and the denominator counts it: the statement is *not*
weakened by a favourable normalisation; it is the harder direction of the two. Everything is
phrased in terms of Mathlib's `riemannZeta` and `analyticOrderAt` and nothing else.

## 1. The method in one paragraph

It is a **second-moment / Gram-matrix argument with an inertia (rank–trace) certificate**, in the
lineage of Montgomery's pair-correlation method — *not* a mollifier (Levinson–Conrey) argument, and
not a zero-density argument. One samples a band-limited taper `φ̂` at `d` equally spaced ordinates
`τ_k` in the window `(T, 2T]` and forms the Hermitian Gram matrix

```
A = Σ_{ρ ∈ 𝒵(I')} m_ρ · v_ρ v_ρᵀ,     v_ρ(k) = φ̂(γ_ρ − τ_k),   γ_ρ = (ρ − ½)/i
```

(`Zeta23/ZeroSide.lean`, `ZeroBlockData.blockA`). Two independent computations of `A` are
compared:

* the **zero side** bounds the *inertia* of `A` by the number of on-line zeros — zeros off the line
  can only contribute cheaply, because of the reflection symmetry `ρ ↦ 1 − ρ̄`;
* the **prime side** computes `tr A` and `‖A‖_F²` asymptotically from Weil's explicit formula.

The mismatch between the two is what forces zeros onto the line.

## 2. The zero side: why off-line zeros are penalised

The configuration is invariant under `reflect ρ = 1 − conj ρ`, which fixes exactly the points with
`Re ρ = 1/2` (`ZeroSide.reflect_eq_self_iff`) and acts on ordinates by `γ_ρ ↦ conj γ_ρ`
(`gammaOf_reflect`). Split the index set into on-line points (`onLine`, `s₁` simple and `s₂`
multiple) and `p` conjugate **pairs** `{ρ, 1 − ρ̄}` of off-line zeros. Then (all in
`Zeta23/ZeroSide.lean`):

* `onPart` — the on-line part — is positive semidefinite with `rank ≤ s₁ + s₂`
  (`onPart_posSemidef`, `rank_blockP_le`) and `tr P ≤ N_on` (`rtrace_blockP_le`, using the Poisson
  summation bound `Σ_k φ̂(γ − τ_k)² ≤ a L²`);
* the off-line part `Q` has **positive index at most `p`** (`posIndex_blockQ_le`): each conjugate
  pair contributes a `(1,1)`-hyperbolic block `2 x xᵀ − 2 y yᵀ`, so by Sylvester's law of inertia it
  can raise `n₊` by at most one, while costing at least two zeros in `N`;
* the counting fact `N_on + 2p ≤ N` (`Non_add_two_p_le_Ncount`).

The *rank–trace inequality* (`Zeta23/LinAlg/RankTrace.lean`, `rank_trace_ineq`, proved from the
Jordan decomposition of `Q` and the von Neumann trace inequality) says, for `P ⪰ 0` of rank ≤ r,
`Q` Hermitian with `n₊(Q) ≤ b`, and any `c > 0`,

```
c·tr P − (c²/4)·r + 2c·tr Q − c²·b  ≤  ‖P + Q‖_F² .
```

At `c = 2` this becomes the repository's counting inequality (`Zeta23/Assembly.lean`,
`zeroside_rank_core`):

```
s₁ + s₂  ≥  4·tr Â − 2·N − ‖Â‖_F²          (Â = A/(aL²), "hat units")
```

This is the whole conceptual content of the unconditionality: the argument never assumes the zeros
are on the line; it *charges* off-line zeros twice in `N` while allowing them to buy only one unit
of positive index.

## 3. The prime side: the constant `c`

Weil's explicit formula turns the entries of `A` into prime sums. `Zeta23/Defs.lean` records the
densities

```
μ(τ) = (1/2π)·Re (Γ'/Γ)(1/4 + iτ/2) − log π/(2π),
Π_X(τ) = 1/(2π(¼+τ²)) + (1/π)·Re((X^s − 1)/s),   s = ½ + iτ,
P_X(τ) = −(1/π)·Σ_{n ≤ X} Λ(n) n^{−1/2} cos(τ log n),      ν_X = μ + Π_X + P_X,
```

and the trace theorem [`thm:traces`] (`Zeta23/PrimeSideTemp.lean`, `TracesBounds`;
proved in `Zeta23/PrimeSideB/Final.lean`, `PrimeSide.thm_traces`) gives, with `X = T^λ`,
`L = log X`, `ℓ₁ = log(T/2π) + 2 log 2 − 1`, `λ₁ = L/ℓ₁`:

```
tr G̃  = L·N(T,2T)·(1 + O(𝓔_T)),
tr G̃² = (T L/2π)·(ℓ₁² + L²/3)·(1 + O(𝓔_T)),
(tr G̃)²/tr G̃² = F(λ₁)·N(T,2T)·(1 + O(𝓔_T)),      F(x) = x/(1 + x²/3).
```

The Montgomery–Vaughan generalized Hilbert inequality ([MV74]; `Zeta23/MV/`) is what controls the
off-diagonal prime terms — the same inequality this repository records as the unproved `Prop`
`RiemannHypothesis.Hilbert.GeneralizedHilbertInequality`.

Write `c` for the ratio `(tr Â)²/(‖Â‖_F²·N) ≈ F(λ₁)`. Then `tr Â ≈ N` and `‖Â‖_F² ≈ N/c`, and the
counting inequality of §2 reads

```
N₀*  ≥  s₁ + s₂  ≥  4N − 2N − N/c  =  (2 − 1/c)·N .
```

**That is the meaning of the shape `2 − 1/c`**: `4·tr − 2N` from the rank–trace inequality at
`c = 2`, minus the Frobenius norm `N/c` supplied by the prime side.

## 4. Where the numbers come from

| constant | source |
|---|---|
| `F(x) = x/(1 + x²/3)` | ratio `(tr G̃)²/tr G̃²`; the `x²/3` is the `L²/3` in `tr G̃²` (`Zeta23/Defs.lean`, `Ffun`) |
| `H(λ) = 2 − 1/λ − λ/3` | `Hfun`, and `H(λ) = 2 − 1/F(λ)` since `1/F(x) = 1/x + x/3` |
| `2/3` | `H(1) = 2/3` (`Hfun_one`); `F` increases on `(0, √3)`, so the flat window is optimised by pushing `λ = log X/log T → 1⁻`, the limit of the unconditional prime range |
| `1/2`, `3/4` | the Cauchy–Schwarz (rather than rank–trace) forms, `2c − 1` and `c` at `c = F(1) = 3/4` — Theorems B and C |
| `c₁* = √2·tan ϑ/(1 + ϑ·tan ϑ)`, `ϑ = 1/√2` | `ThmD.cStar 1`: the same ratio for the *optimal* (Montgomery–Taylor) taper instead of the flat window (`Zeta23/ThmD/Functional.lean`, `Zeta23/ThmD/Window.lean`) |
| `2 − 1/c₁* = 0.67250…` | `ThmD.HD 1` — Theorem D, the same inequality of §3 with `c = c₁*` |
| `5/6`, `(3 − 1/c₁*)/2` | the multiplicity-aware refinement `rank_trace_mult` ("Lemma R") at `c = 3` (`Zeta23/ZeroSide/Mult.lean`) |

So the `2/3` is a *limit* of a one-parameter family, not an isolated numerical accident, and the
whole family is the ratio `c` fed through the fixed algebraic shape `2 − 1/c`.

## 5. What the hypothesis chain looks like

`Zeta23/Final.lean` is layered, and each layer discharges one input:

```
thmA        (4 hypotheses: EF_lit, RvM, MVDiag, GammaFacts)
thmA₃/thmA₂ (Γ-facts proved: Zeta23/GammaFacts/, Stirling for Γ'/Γ)
thmA₁       (RvM proved: Zeta23/RvM/, argument principle + Backlund via Jensen)
thmA₀       = thmA₁ zetaEF
```

`EF.EF_lit zetaZeroConfig` is Weil's explicit formula for `ζ` in its literature form — the pairing
of a test function against the zeros equals the prime sum plus archimedean terms — and `zetaEF`
(`WeilEF.EF_lit_zetaZeroConfig`) proves it from Mathlib's functional equation by contour
integration. So the final theorem has no hypotheses at all: the "literature trust base" visible in
the intermediate statements is fully discharged inside the library.

## 6. Audit performed here

* No `sorry` or `admit` occurs in any `.lean` file under `vendor/zeta23` (the word appears only in
  prose comments describing *upstream* files that were deliberately truncated before their
  `sorry`s, e.g. `Zeta23/FromPNTPlus/Mertens.lean`).
* No `axiom` declaration occurs anywhere in the vendored library, and
  `#print axioms Zeta23.two_thirds_on_critical_line` (and `_cumulative`) reports exactly
  `[propext, Classical.choice, Quot.sound]`. No `native_decide`.
* The statement's vocabulary was unfolded with `#print` (quoted in §0) and is built from Mathlib's
  `riemannZeta`/`analyticOrderAt`, so there is no room for a non-standard reading of "zero",
  "multiplicity", or "on the critical line".
* The whole library compiles in this project's build (`lake build`, 9219 targets).

What the audit does **not** establish: that `2/3` agrees with the literature. It does not. The best
published *unconditional* proportions of zeros on the critical line are Conrey's 2/5 and the
Pratt–Robles–Zaharescu–Zeindler refinement ≈ 5/12, obtained by the Levinson–Conrey mollifier
method; the `2/3` here is larger, and (as §0 notes) is stated for the harder pair of counting
functions. Montgomery's pair-correlation method classically yields `2/3` *for simple zeros under
RH*, which is precisely the constant reappearing here; the library's claim is that the rank–trace /
inertia device of §2 removes the need for RH. That step — "an off-line conjugate pair buys at most
one unit of positive index but costs two zeros" — is the load-bearing novelty, and it is where a
reader who wants to understand (or doubt) the result should look: `ZeroSide.posIndex_blockQ_le`,
`Assembly.zeroside_rank_core`, and the Poisson trace bound `ZeroSide.rtrace_blockP_le`.

## 7. Consequences for this repository (the T7 question)

Can the `2/3` be rederived with this repository's own machinery? Not at present, and the obstruction
can be named exactly:

1. **The Hilbert inequality.** The prime side needs Montgomery–Vaughan's generalized Hilbert
   inequality with the constant `π δ⁻¹`. This repository proves it only for lattice frequencies
   (`RiemannHypothesis.Hilbert.hilbert_inequality_lattice`) and now also proves the *free* bound for
   arbitrary `δ`-separated frequencies (`RiemannHypothesis.Hilbert.hilbert_free_bound`:
   `2 H_n δ⁻¹`, equivalently `2(1 + log n) δ⁻¹`). In the intended application `δ ≍ 1/log T` and
   `n ≍ T log T`, so the free bound loses a factor `log T` — exactly the loss that destroys the
   argument. The residual gap is therefore a single, sharply identified statement:
   `RiemannHypothesis.Hilbert.GeneralizedHilbertInequality`.
2. **The taper package.** The zero side needs the Poisson-summation identity
   `Σ_{k ∈ ℤ} φ̂(γ − τ_k)² = a L²` for the sampling family, and the `ρ ↦ 1 − ρ̄` block decomposition.
   The linear algebra (Sylvester inertia, von Neumann trace inequality) is the part that Mathlib
   plus this repository can most readily supply; the analytic taper estimates are not present here.
3. **The explicit formula at the required uniformity.** `RiemannHypothesis/ExplicitFormula.lean`
   states the pairing but not the two trace asymptotics `[thm:tr1]`, `[thm:tr2]` with the
   `O(𝓔_T)` uniformity that the endgame consumes.

None of these is a Levinson-method ingredient: the route that would reproduce `2/3` is the
Gram-matrix route above, not the mollifier route, and the mollifier route in this repository is
independently blocked on the same Hilbert inequality.
