# The Riemann Hypothesis in Lean

A Lean 4 / Mathlib library around the Riemann hypothesis. It contains the precise statement,
machine-checked equivalences between its standard formulations, and a large body of
unconditional theory: the prime number theorem, zero-free regions, zero counting, Hardy's
theorem, moments of `ζ`, and the proportion of zeroes on the critical line.

## Status: the hypothesis has a machine-checked proof (alpo.ge, 2026-11-20)

On 20 November 2026 a Lean proof of the Riemann hypothesis, and of GRH for Dirichlet
`L`-functions, was published at alpo.ge by L. Alpöge, with Claude. See the
[announcement](vendor/alpo/remark.pdf) and the
[55-page exposition](vendor/alpo/riemann_hypothesis.pdf). Its main theorem is
`theorem riemannHypothesis : RiemannHypothesis`. That is Mathlib's statement, which this
repository calls `ZetaForm`.

**Independent verification.** A. Sutherland (MIT) checked the proof independently; his page is
`math.mit.edu/~drew/grh`, and the results below are as of 2026-11-22 04:35 UTC.

* All 175,187 modules compile. The five headline theorems use only `propext`,
  `Classical.choice` and `Quot.sound`.
* The Lean kernel (`leanchecker`) and `lean4lean` replay every module.
* The independent kernels nanoda and con-leche accept the full export.
* Two independent statement comparisons confirm all five theorems against a challenge file
  that imports only Mathlib.
* A sandboxed rebuild reproduces the export byte for byte.
* Still running at that time: the Lean default and paranoid kernels on the export, and
  `lake comparator`.

**What this repository has checked** ([`vendor/alpo`](vendor/alpo)):

* The tree is vendored byte-identical to the archive Sutherland verified (joined SHA-256
  `9631b4f0…`). CI checks the provenance and runs a static scan.
* The analytic half of the proof is compiled in CI and connected to our statements.
  [`AnalyticBridge.lean`](vendor/alpo/AnalyticBridge.lean) proves that a one-sided window bound
  on the smoothed prime sum implies `ZetaForm`, `ZetaStripForm` and `EtaForm`. For `ζ`,
  therefore, the arithmetic half has to be trusted for that one statement only.
* The same file proves, unconditionally, that no such bound holds with an exponent below `1/2`.
* The full 175,187-module build has **not** been repeated here (240–360 core-hours). It runs in
  the manual workflow [`alpo-verify`](.github/workflows/alpo-verify.yml) on a large self-hosted
  runner, with [`Verify.lean`](vendor/alpo/Verify.lean) and
  [`Bridge.lean`](vendor/alpo/Bridge.lean).

The proof is external. This repository's own library contains no term of type `ZetaForm`, and
[`scripts/audit.sh`](scripts/audit.sh) checks that none appears. Theorems below that assume a
hypothesis are still recorded as conditional. Details: [`vendor/alpo/README.md`](vendor/alpo/README.md).

## The statement and its equivalent forms

```lean
/-- The Riemann hypothesis (zeta form, as in Mathlib). -/
abbrev ZetaForm : Prop := RiemannHypothesis

/-- The Riemann hypothesis restricted to the critical strip. -/
def ZetaStripForm : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- The Riemann hypothesis in terms of the Dirichlet eta function. -/
def EtaForm : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → dirichletEta s = 0 → s.re = 1 / 2

theorem zeta_iff_zeta_strip : ZetaForm ↔ ZetaStripForm
theorem zeta_iff_eta : ZetaForm ↔ EtaForm
```

The eta form is elementary: `η(s) = 1 − 2⁻ˢ + 3⁻ˢ − ⋯` needs no analytic continuation, and the
bridge is `η(s) = (1 − 2^(1−s)) ζ(s)`. Further equivalent forms include:

* `EtaLimitForm`, in which only the partial sums of the alternating series appear;
* `XiForm`;
* the upper-strip, right-strip, nonvanishing, self-reflective and every-height-verified forms;
* the reciprocal, log-branch, counting, supremum and logarithmic-derivative forms;
* the de Bruijn–Newman form `∀ z, H₀ z = 0 → z.im = 0`.

They are in [`Main.lean`](RiemannHypothesis/Main.lean),
[`Symmetry.lean`](RiemannHypothesis/Symmetry.lean),
[`Alternating.lean`](RiemannHypothesis/Alternating.lean), [`Xi.lean`](RiemannHypothesis/Xi.lean),
[`Criteria.lean`](RiemannHypothesis/Criteria.lean) and
[`FourierXi.lean`](RiemannHypothesis/FourierXi.lean).

## Highlights

Every result is `sorry`-free and uses only `propext`, `Classical.choice` and `Quot.sound`.

| Result | Where |
| --- | --- |
| **Five sufficient conditions.** Square-root cancellation in `M(N)`, `det(A_n)` (Redheffer), `ψ(N) − N`, `∑ μ(n)/n` or `L(N)` each implies `ZetaForm` | [`MoebiusCriterion`](RiemannHypothesis/MoebiusCriterion.lean), [`Redheffer`](RiemannHypothesis/Redheffer.lean), [`ChebyshevCriterion`](RiemannHypothesis/ChebyshevCriterion.lean), [`MoebiusOverNCriterion`](RiemannHypothesis/MoebiusOverNCriterion.lean), [`LiouvilleCriterion`](RiemannHypothesis/LiouvilleCriterion.lean) |
| **The prime number theorem** `π(x) ∼ x/log x`, Chebyshev's bounds, and Mertens' three theorems | [`PrimeNumberTheorem`](RiemannHypothesis/PrimeNumberTheorem.lean), [`PrimeCounting`](RiemannHypothesis/PrimeCounting.lean), [`Mertens`](RiemannHypothesis/Mertens.lean) |
| **The de la Vallée Poussin zero-free region** `re s > 1 − c/log\|im s\|` | [`ZeroFreeClassical`](RiemannHypothesis/ZeroFreeClassical.lean) |
| **Zero counting.** `N(T) = (T/2π) log T + O(T)`, `∑_ρ 1/(1+γ²) < ∞`, multiplicities `O(log \|γ\|)` | [`RvMCumulative`](RiemannHypothesis/RvMCumulative.lean), [`ZeroCount`](RiemannHypothesis/ZeroCount.lean), [`ZeroSum`](RiemannHypothesis/ZeroSum.lean) |
| **Hardy's theorem.** Infinitely many zeroes on the critical line | [`CriticalLine`](RiemannHypothesis/CriticalLine.lean), [`CriticalLineOrdinates`](RiemannHypothesis/CriticalLineOrdinates.lean) |
| **Proportions.** More than `2/3` of the zeroes are simple and on the line; `67 %` on the line `ε`-free; `80 %` of the distinct zeroes are simple; at most `1/3` lie off the line | [`Zeta23Bridge`](RiemannHypothesis/Zeta23Bridge.lean), [`SixtySevenPercent`](RiemannHypothesis/SixtySevenPercent.lean), [`EightyPercentSimple`](RiemannHypothesis/EightyPercentSimple.lean), [`OffLine`](RiemannHypothesis/OffLine.lean) |
| **The Bohr–Landau density theorem.** Almost all zeroes lie within `δ` of the critical line | [`BohrLandau`](RiemannHypothesis/BohrLandau.lean) |
| **Growth and moments.** The convexity bound; `‖ζ(1/2+it)‖ ≤ 254 t^(1/4)` through the approximate functional equation; `∫₀ᵀ \|ζ(1/2+it)\|² dt = T log T + O(T)` | [`ConvexityLogFree`](RiemannHypothesis/ConvexityLogFree.lean), [`AFECriticalLineProof`](RiemannHypothesis/AFECriticalLineProof.lean), [`HardyLittlewoodMeanSquare`](RiemannHypothesis/HardyLittlewoodMeanSquare.lean) |
| **The de Bruijn–Newman bridge.** `H₀(z) = Ξ(z/2)/8`, unconditionally | [`FourierXi`](RiemannHypothesis/FourierXi.lean), [`ThetaW`](RiemannHypothesis/ThetaW.lean) |
| **Weil's explicit formula**, and `ZetaForm → 0 ≤ Re W(k)` for positive test functions | [`ExplicitFormula`](RiemannHypothesis/ExplicitFormula.lean), [`WeilPositivity`](RiemannHypothesis/WeilPositivity.lean) |
| **The argument principle on rectangles**, and Littlewood's lemma | [`RectangleArgumentPrinciple`](RiemannHypothesis/RectangleArgumentPrinciple.lean), [`Littlewood`](RiemannHypothesis/Littlewood.lean) |

Each result is explained in [`docs/results.md`](docs/results.md), which also has the full
highlights table. Every module is listed in [`docs/layout.md`](docs/layout.md). Several
proportion results are restated from the vendored [`Zeta23`](vendor/zeta23) library, with
attribution module by module. The proportion results are `liminf`/`limsup` statements with no
effective `T₀`.

## Building and checking

```bash
elan toolchain install leanprover/lean4:v4.33.1
lake exe cache get   # Mathlib's prebuilt oleans
lake build
./scripts/audit.sh
```

`scripts/audit.sh` checks the following:

* it rebuilds the project;
* no `sorry` occurs outside [`Challenge.lean`](Challenge.lean), the statement of record;
* it prints the axioms of every headline theorem;
* the pinned statements still elaborate;
* every *conditional* theorem is listed in
  [`docs/goal/conditional-theorems.txt`](docs/goal/conditional-theorems.txt) (one whose
  hypotheses mention a `Prop` stated here but not proved).

Because of the last check, the line between conditional and unconditional results is enforced
by the machine, not by docstrings.

For the alpo.ge tree, see [`vendor/alpo/README.md`](vendor/alpo/README.md):

```bash
bash vendor/alpo/tools/provenance.sh   # hashes, byte-identical tree (minutes)
bash vendor/alpo/tools/analytic.sh     # analytic half + AnalyticBridge (minutes; needs
                                       # `lake exe cache get` in vendor/alpo/lean first)
```

**Never run `lake build` inside `vendor/alpo/lean`.** Lake cannot cap its parallelism, and on
this tree an unthrottled build crashed the machine. Use `vendor/alpo/tools/build.py` instead.

## Layout

| Path | Contents |
| --- | --- |
| [`RiemannHypothesis/`](RiemannHypothesis) | the library (236 modules); see [`docs/layout.md`](docs/layout.md) |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) | the statement of record and its solution (the three equivalences) |
| [`vendor/zeta23`](vendor/zeta23) | the Zeta23 library: more than two thirds of the zeroes are simple and on the critical line (Apache 2.0) |
| [`vendor/alpo`](vendor/alpo) | the alpo.ge proof and this repository's checks of it |
| [`scripts/`](scripts) | audit, conditional-theorem manifest, task-board tools |
| [`docs/goal/`](docs/goal) | the goal prompt and the task board |

## Task board

[`docs/goal/task-board.yaml`](docs/goal/task-board.yaml) is the machine-readable work queue
(190 rows, milestones M0–M4). [`docs/current-goal-state.md`](docs/current-goal-state.md) is a
summary generated from it.

```bash
python3 scripts/goal_state.py validate   # board sanity
python3 scripts/goal_state.py next       # next dependency-ready task
python3 scripts/goal_state.py render     # regenerate docs/current-goal-state.md
```

## Provenance and credits

[`formalization.yaml`](formalization.yaml) and [`NOTICE`](NOTICE) record where every imported
result comes from, under [`LICENSES/`](LICENSES). The alpo.ge archive has no licence file. It is
kept in this private repository for verification only and must not be redistributed.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
